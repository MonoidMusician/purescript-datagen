module Externs.Codec.AKind where

import Prelude

import Data.Argonaut (Json)
import Data.Argonaut as A
import Data.Codec (basicCodec, decode, encode, (>~>))
import Data.Codec.Argonaut (JsonCodec, JsonDecodeError(..), jobject)
import Data.Codec.Argonaut as CA
import Data.Codec.Argonaut.Common (tuple)
import Data.Const (Const(..))
import Data.Either (Either(..))
import Data.Functor.Mu (Mu, roll, unroll)
import Data.Functor.Variant as VF
import Data.Identity (Identity(..))
import Data.Lazy (Lazy, defer, force)
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (un)
import Data.Pair (Pair(..))
import Data.Profunctor (dimap)
import Foreign.Object (Object)
import Foreign.Object as Foreign.Object
import Data.Tuple (Tuple(..), uncurry)
import Externs.Codec.Names (codecProper, codecQualified)
import Types (AKindV, AKindVF, _fun, _name, _row)

prop :: String -> Json -> Maybe Json
prop i = A.caseJsonObject Nothing (Foreign.Object.lookup i)

recursiveCodec :: forall f. (forall a. Lazy (JsonCodec a) -> JsonCodec (f a)) -> JsonCodec (Mu f)
recursiveCodec codec = dimap unroll roll (codec (defer \_ -> recursiveCodec codec))

contentField :: JsonCodec Json
contentField = basicCodec (pure <<< dec) enc
  where
  dec :: Json -> Json
  dec j = A.caseJsonObject j (A.fromObject <<< rename "value" "content") j
  enc :: Json -> Json
  enc j = A.caseJsonObject j (A.fromObject <<< rename "content" "value") j
  rename ∷ String -> String -> Object Json -> Object Json
  rename oldName newName obj = maybe obj (uncurry (Foreign.Object.insert newName)) (Foreign.Object.pop oldName obj)

pair :: forall a. JsonCodec a -> JsonCodec (Pair a)
pair codec = tuple codec codec # dimap
  (\(Pair a b) -> Tuple a b)
  (\(Tuple a b) -> Pair a b)

codecAKindV :: JsonCodec AKindV
codecAKindV = recursiveCodec inner
  where
    codecQualifiedProper = codecQualified codecProper
    inner :: forall a. Lazy (JsonCodec a) -> JsonCodec (AKindVF a)
    inner recur = jobject >~> basicCodec dec enc
      where
        dec o = do
          let
            getContent :: forall b. JsonCodec b -> Either JsonDecodeError b
            getContent c = decode (CA.prop "contents" c) o
          tag <- decode (CA.prop "tag" CA.string) o
          case tag of
            "FunKind" -> VF.inj _fun <$>
              getContent (pair $ force recur)
            "Row" -> VF.inj _row <<< Identity <$>
              getContent (force recur)
            "NamedKind" -> VF.inj _name <<< Const <$>
              getContent codecQualifiedProper
            _ -> Left (AtKey "tag" (UnexpectedValue (A.fromString tag)))
        mkContent :: forall b. String -> JsonCodec b -> b -> Object Json
        mkContent t c v = Foreign.Object.fromFoldable
          [ Tuple "tag" $ A.fromString t
          , Tuple "contents" $ encode c v
          ]
        enc = VF.match
          { fun: \v -> mkContent "FunKind" (pair $ force recur) v
          , row: un Identity >>> \v -> mkContent "Row" (force recur) v
          , name: un Const >>> mkContent "NamedKind" codecQualifiedProper
          }
