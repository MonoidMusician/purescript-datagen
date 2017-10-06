module Externs.Parse.Names where

import Prelude

import Control.MonadZero (empty)

import Data.Argonaut as A
import Data.Array (cons, drop, uncons, (!!))
import Data.Char (fromCharCode)
import Data.Char.Unicode (isUpper)
import Data.Codec (basicCodec, decode, encode)
import Data.Codec.Argonaut (JsonCodec, JsonDecodeError(..))
import Data.Codec.Argonaut.Common (tuple)
import Data.Codec.Argonaut.Compat (maybe)
import Data.Either (note)
import Data.Maybe (Maybe(..))
import Data.NonEmpty ((:|))
import Data.Profunctor (dimap)
import Data.String.CodePoints (Pattern(..), codePointAt, codePointToInt, split)
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
  if isUpper (fromCharCode (codePointToInt c))
    then pure (Proper s)
    else empty

codecProper :: JsonCodec Proper
codecProper = basicCodec dec enc
  where
    dec s = note (UnexpectedValue s) $
      A.toString s >>= ensureProper
    enc = show >>> A.fromString
