module Externs.Parse.Names where

import Prelude

import Control.MonadZero (empty)
import Data.Argonaut as A
import Data.Array (all, cons, drop, uncons, (!!))
import Data.Bifunctor (lmap)
import Data.Bitraversable (ltraverse)
import Data.Char (fromCharCode)
import Data.Char.Unicode (isAlphaNum, isUpper)
import Data.Codec (basicCodec, decode, encode, (>~>))
import Data.Codec.Argonaut (JsonCodec, JsonDecodeError(..), string)
import Data.Codec.Argonaut.Common (tuple)
import Data.Codec.Argonaut.Compat (maybe, strMap)
import Data.Either (note)
import Data.Lens (Prism', preview, review)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.NonEmpty ((:|))
import Data.Profunctor (dimap)
import Data.StrMap as SM
import Data.String.CodePoints (Pattern(..), codePointAt, codePointToInt, split, toCodePointArray)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Types (Module(..), Proper(..), Qualified(..))

codecQualified :: forall a. (JsonCodec a) -> JsonCodec (Qualified a)
codecQualified codec = tuple (maybe codecModule) codec # dimap
  (case _ of
    Unqualified n -> Tuple Nothing  n
    Qualified q n -> Tuple (Just q) n
  ) (case _ of
    Tuple Nothing  n -> Unqualified n
    Tuple (Just q) n -> Qualified q n
  )

codecModule :: JsonCodec Module
codecModule = basicCodec dec enc
  where
    dec j = do
      a <- note (TypeMismatch "Array") $ A.toArray j
      head <- decode codecProper =<< note (AtIndex 0 $ MissingValue) (a !! 0)
      rest <- traverse (decode codecProper) $ drop 1 a
      pure $ Module (head :| rest)
    enc (Module (head :| rest)) =
      A.fromArray $ encode codecProper <$> cons head rest

parseModule :: String -> Maybe Module
parseModule = split (Pattern ".") >>> traverse ensureProper >=>
  (uncons >>> map \{ head, tail } -> Module (head :| tail))

ensureProper :: String -> Maybe Proper
ensureProper s = do
  c <- codePointAt 0 s
  let
    testChar p = p <<< fromCharCode <<< codePointToInt
    otherChar = isAlphaNum || eq '\'' || eq '_'
  if testChar isUpper c && all (testChar otherChar) (toCodePointArray s)
    then pure (Proper s)
    else empty

codecProper :: JsonCodec Proper
codecProper = string >~> basicCodec dec show
  where
    dec s = note (UnexpectedValue (A.fromString s)) $
      ensureProper s

codecStrMapish :: forall k v. Ord k => Prism' String k -> JsonCodec v -> JsonCodec (Map k v)
codecStrMapish codecKey codecValue = strMap codecValue >~> basicCodec dec enc
  where
    asArray = id :: Array ~> Array
    dec s =
      let
        conv = traverse $ ltraverse \k ->
          note (UnexpectedValue (A.fromString k)) $ preview codecKey k
      in Map.fromFoldable <$> conv (asArray (SM.toUnfoldable s))
    enc = SM.fromFoldable <<< map (lmap (review codecKey)) <<< asArray <<< Map.toUnfoldable
