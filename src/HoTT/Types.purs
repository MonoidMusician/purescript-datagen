module HoTT.Types where

import Data.List (List)
import HoTT.Types.Level (Level)
import HoTT.Types.Name (Name)

data BinderInfo
  = Default
  | Implicit
  | StrictImplicit
  | InstImplicit
  | AuxDecl

data Expr
  = Var Int
  | Sort Level
  | Const Name (List Level)
  | MVar Name Name Expr
  | LocalConst Name Name BinderInfo Expr
  | App Expr Expr
  | Lam Name BinderInfo Expr Expr
  | Pi Name BinderInfo Expr Expr
  | Elet Name Expr Expr Expr
  -- | Macro MacroDef (List Expr)
