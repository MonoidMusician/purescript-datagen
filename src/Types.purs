module Types where

import Prelude

import Data.Array (concatMap, last)
import Data.Array (fromFoldable) as Array
import Data.Const (Const)
import Data.Either (Either)
import Data.Functor.Mu (Mu)
import Data.Functor.Variant (FProxy, SProxy(..), VariantF)
import Data.Map (Map)
import Data.Map (toAscUnfoldable) as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Monoid (class Monoid, mempty)
import Data.NonEmpty (NonEmpty, (:|))
import Data.Pair (Pair)
import Data.Set (Set)
import Data.Set (toUnfoldable) as Set
import Data.String (joinWith)
import Data.Tuple (Tuple(..))
import Matryoshka (Algebra, cata)

newtype Module = Module (NonEmpty Array Proper)
derive newtype instance eqModule :: Eq Module
derive newtype instance ordModule :: Ord Module
instance showModule :: Show Module where
  show (Module (top :| [])) = show top
  show (Module (top :| rest)) =
    show top <> "." <> joinWith "." (show <$> rest)
lastOf :: Module -> Proper
lastOf (Module (n :| ns)) = fromMaybe n $ last ns
data Qualified a
  = Qualified Module a
  | Unqualified a
instance showQualified :: Show a => Show (Qualified a) where
  show (Unqualified a) = show a
  show (Qualified m a) = show m <> "." <> show a
newtype Proper = Proper String
derive newtype instance eqProper :: Eq Proper
derive newtype instance ordProper :: Ord Proper
instance showProper :: Show Proper where
  show (Proper p) = p
newtype Ident = Ident String
derive newtype instance eqIdent :: Eq Ident
derive newtype instance ordIdent :: Ord Ident
instance showIdent :: Show Ident where
  show (Ident p) = p
newtype Op = Op String
derive newtype instance eqOp :: Eq Op
derive newtype instance ordOp :: Ord Op
instance showOp :: Show Op where
  show (Op p) = p
type ProperOp = Either Op Proper
type IdentOp = Either Op Ident

type ImportModules = Map Module ImportModule
data ImportModule =
  ImportModule
    (Maybe Imports)
    (Map Module Imports)
instance semigroupImportModule :: Semigroup ImportModule where
  append (ImportModule is as) (ImportModule iz az) =
    ImportModule (is <> iz) (as <> az)
instance monoidImportModule :: Monoid ImportModule where
  mempty = ImportModule mempty mempty
showImportModules :: ImportModules -> String
showImportModules = joinWith "\n" <<< Map.toAscUnfoldable >>> concatMap
  \(Tuple modul (ImportModule mims aliases)) ->
    let
      showUnq []  = "import " <> show modul
      showUnq ims = "import " <> show modul <> " " <>
        "(" <> joinWith ", " (show <$> ims) <> ")"
      showQ (Tuple mod alias) = showUnq alias <> " as " <> show mod
    in Array.fromFoldable (showUnq <$> mims) <>
      (showQ <$> Map.toAscUnfoldable aliases)

type Imports = Array Import
data Import
  = Value Ident
  | Type Proper (Maybe Constructors)
  | Class Proper
  | Kind Proper
  | Operator Op
  | TypeOperator Op
instance showImport :: Show Import where
  show (Value i) = show i
  show (Type p Nothing) = show p
  show (Type p (Just cs)) = show p <> "(" <> show cs <> ")"
  show (Class p) = "class " <> show p
  show (Kind p) = "kind " <> show p
  show (Operator o) = "(" <> show o <> ")"
  show (TypeOperator o) = "type (" <> show o <> ")"
data Constructors = AllCs | SpecificCs (Set Proper)
instance showConstructors :: Show Constructors where
  show (SpecificCs ps) = joinWith ", " (show <$> Set.toUnfoldable ps)
  show AllCs = ".."
instance semigroupConstructors :: Semigroup Constructors where
  append (SpecificCs a) (SpecificCs b) = SpecificCs (a <> b)
  append _ _ = AllCs
instance monoidConstructors :: Monoid Constructors where
  mempty = SpecificCs mempty

data DataType
  = TypeAlias ATypeV
  | SumType (Map Proper (Array ATypeV))
data DeclKeyword = TType | TNewtype | TData
derive instance eqDeclKeyword :: Eq DeclKeyword
derive instance ordDeclKeyword :: Ord DeclKeyword
instance showDeclKeyword :: Show DeclKeyword where
  show TType = "type"
  show TNewtype = "newtype"
  show TData = "data"
declKeyword :: DataType -> DeclKeyword
declKeyword (TypeAlias _) = TType
declKeyword (SumType m)
  | [Tuple _ [_]] <- Map.toAscUnfoldable m
    = TNewtype
  | otherwise
    = TData
type ATypeVR =
  ( name     :: FProxy (Const (Qualified Proper))
  , var      :: FProxy (Const Ident)
  , function :: FProxy Pair
  , app      :: FProxy Pair
  -- , row      :: FProxy (Product StrMap Maybe)
  )
type ATypeVF = VariantF ATypeVR
type ATypeV = Mu ATypeVF

_name = SProxy :: SProxy "name"
_var = SProxy :: SProxy "var"
_function = SProxy :: SProxy "function"
_app = SProxy :: SProxy "app"

data AKindF a
  = KindName (Qualified Proper)
  | KindFunction a a
  | KindApp a a
  | KindRow a
newtype AKind = AKind (Mu AKindF)
derive instance functorAKindF :: Functor AKindF
instance showAKind :: Show AKind where
  show (AKind inner) = cata showInner inner
    where
      showInner :: Algebra AKindF String
      showInner (KindName q) = show q
      showInner (KindFunction a b) = wrap a <> " -> " <> wrap b
      showInner (KindApp f a) = wrap f <> " " <> wrap a
      showInner (KindRow a) = "# " <> a
      wrap a = "(" <> a <> ")"

type TypeAbses = Array TypeAbs
data TypeAbs = TypeAbs Ident (Maybe AKind)
instance showTypeAbs :: Show TypeAbs where
  show (TypeAbs i Nothing) = show i
  show (TypeAbs i (Just k)) = "(" <> show i <> " :: " <> show k <> ")"
data DataTypeDef = DataTypeDef TypeAbses DataType
type DataTypeDecls = Map Proper DataTypeDef

type Modules = Map Module ModuleData
type ModuleData =
  { imports :: ImportModules
  , datatypes :: DataTypeDecls
  }
