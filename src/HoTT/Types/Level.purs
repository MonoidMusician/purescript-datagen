module HoTT.Types.Level where

import Prelude

import Data.Maybe (Maybe(..))
import HoTT.Types.Name (Name)

data Level
  = Zero
  | Succ Level
  | Max Level Level
  | IMax Level Level
  | Param Name
  | MVar Name

compute :: Level -> Maybe Int
compute = case _ of
  Zero -> Just 0
  Succ l
    | Just n <- compute l
      -> Just (n+1)
  Max l r
    | Just n <- compute l
    , Just m <- compute r
      -> Just (max n m)
  IMax l r
    | Just 0 <- compute r
      -> Just 0
  IMax l r
    | Just n <- compute l
    , Just m <- compute r
      -> Just (max n m)
  _ -> Nothing

instance showLevel :: Show Level where
  show l | Just n <- compute l = show n
  show l = go 0 l where
    go succs = case _ of
      Succ l' -> go (succs+1) l'
      l' | succs == 0 -> finish l'
      l' -> finish l' <> "+" <> show succs
    finish Zero = "0"
    finish (Succ l') = show l' <> "+1"
    finish (Max l' r') = "(max " <> show l' <> " " <> show r' <> ")"
    finish (IMax l' r') = "(imax " <> show l' <> " " <> show r' <> ")"
    finish (Param n) = show n
    finish (MVar n) = "?" <> show n
