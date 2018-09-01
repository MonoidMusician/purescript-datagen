module HoTT.Types where

import Prelude

import Data.Array (foldl)
import Data.Function (on)
import Data.NonEmpty (NonEmpty, foldl1)
import Data.Tuple (Tuple(..))
import HoTT.Types.Level (Level)
import HoTT.Types.Level as Level
import HoTT.Types.Name (Name)

data BinderInfo
  = Default -- (name : ty)
  | Implicit -- {{name : ty}}
  | StrictImplicit -- {name : ty}
  | InstImplicit -- [name : ty]
  | AuxDecl

derive instance eqBinderInfo :: Eq BinderInfo
derive instance ordBinderInfo :: Ord BinderInfo

data Expr
  = Var Int
  | Sort Level
  | Const Name (Array Level)
  | MVar Name Name Expr
  | LocalConst Name Name BinderInfo Expr
  | App Expr Expr
  | Lam Name BinderInfo Expr Expr
  | Pi Name BinderInfo Expr Expr
  | Elet Name Expr Expr Expr
  -- | Macro MacroDef (List Expr)

apps :: NonEmpty Array Expr -> Expr
apps = foldl1 App

type Printer s =
  { operator :: String -> s
  , keyword :: String -> s
  , literal :: String -> s
  , name :: String -> s
  , append :: s -> s -> s
  , empty :: s
  , space :: s
  }
newtype Pretty = Pretty (forall s. Printer s -> s)

runPretty :: forall s. Pretty -> Printer s -> s
runPretty (Pretty printer) = printer

plainPrinter :: Printer String
plainPrinter =
  { operator: identity
  , keyword: identity
  , literal: identity
  , name: identity
  , append: (<>)
  , empty: ""
  , space: " "
  }

ppExpr :: Expr -> Int -> Pretty
ppExpr e prec = Pretty \s ->
  let
    run (Pretty printer) = printer s
    rec = flip $ ppExpr >>> compose run
    spaced a = s.space `s.append` a `s.append` s.space
    spacer a b = a `s.append` s.space `s.append` b
    parens a = s.operator "(" `s.append` a `s.append` s.operator ")"
    parensPrec p a =
      if prec == 0 || prec < p then a else parens a
  in case e of
    Var i -> s.operator "#" `s.append` s.literal (show i)
    Sort Level.Zero -> s.keyword "Prop"
    Sort (Level.Succ Level.Zero) -> s.keyword "Type"
    Sort l -> s.keyword "Sort" `s.append` s.space `s.append` s.literal (show l)
    Const n [] -> s.name (show n)
    Const n [l] -> s.name (show n)
      `s.append` s.operator "."
      `s.append` s.operator "{"
      `s.append` s.literal (show l)
      `s.append` s.operator "}"
    Const n ls -> s.name (show n)
      `s.append` s.operator "."
      `s.append` s.operator "{"
      `s.append` foldl s.append s.empty (parens <<< s.literal <<< show <$> ls)
      `s.append` s.operator "}"
    MVar n pp_n _ | pp_n /= n -> s.name (show pp_n)
    MVar n _ _ -> s.operator "?" `s.append` s.name (show n)
    LocalConst _ pp_n _ _ -> s.name (show pp_n)
    App f a -> parensPrec 1 $
      rec 0 f `s.append` s.operator " " `s.append` rec 1 a
    Lam n bi t body -> s.operator "fun"
      `s.append` ppBinder n bi (rec 0 t) s
      `s.append` s.operator ","
      `spacer` rec 0 body
    Pi n bi t body -> s.operator "Pi"
      `s.append` ppBinder n bi (rec 0 t) s
      `s.append` s.operator ","
      `spacer` rec 0 body
    Elet n t v body -> s.keyword "let"
      `spacer` s.name (show n)
      `s.append` spaced (s.operator ":")
      `s.append` rec 0 t
      `s.append` spaced (s.operator ":=")
      `s.append` rec 0 v
      `s.append` spaced (s.keyword "in")
      `s.append` rec 0 body

derive instance eqExpr :: Eq Expr
derive instance ordExpr :: Ord Expr

ppBinder :: forall s. Name -> BinderInfo -> s -> Printer s -> s
ppBinder n bi e s =
  let t = s.name (show n) `s.append` s.operator ":" `s.append` e
      parens l r = s.operator l `s.append` t `s.append` s.operator r
  in case bi of
    Default -> parens "(" ")"
    Implicit -> parens "{{" "}}"
    StrictImplicit -> parens "{" "}"
    InstImplicit -> parens "[" "]"
    AuxDecl -> parens "((" "))" -- FIXME

type Syntax =
  { unicode :: String
  , ascii :: String
  , explanation :: String
  }

binderParens :: BinderInfo -> Tuple Syntax Syntax
binderParens =
  let
    simpl :: String -> Syntax
    simpl = join { unicode: _, ascii: _, explanation: "" }
    simple :: String -> String -> Tuple Syntax Syntax
    simple = Tuple `on` simpl
    fancy :: String -> String -> String -> String -> Tuple Syntax Syntax
    fancy l l' r' r = Tuple
      { ascii: l, unicode: l', explanation: "" }
      { unicode: r', ascii: r, explanation: "" }
    explain :: String -> Tuple Syntax Syntax -> Tuple Syntax Syntax
    explain e (Tuple l r) = Tuple
      (l { explanation = e })
      (r { explanation = e })
  in case _ of
    Default -> simple "(" ")" # explain
      "An argument, always explicit"
    Implicit -> fancy "{{" "⦃" "⦄" "}}" # explain
      "An implicit argument, weakly inserted"
    StrictImplicit -> simple "{" "}" # explain
      "An implicit argument, always left implicit"
    InstImplicit -> simple "[" "]" # explain
      "An implicit argument inserted by typeclass resolution"
    AuxDecl -> simple "((" "))" # explain "idk"

showBinder :: Name -> BinderInfo -> String -> String
showBinder n bi e = let t = show n <> " : " <> e in case bi of
  Default -> "(" <> t <> ")"
  Implicit -> "{{" <> t <> "}}"
  StrictImplicit -> "{" <> t <> "}"
  InstImplicit -> "[" <> t <> "]"
  AuxDecl -> "((" <> t <> "))" -- FIXME
