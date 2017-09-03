module Types where

import Prelude

import Control.Apply (lift2)
import Data.Array (concatMap, last, uncons, unsnoc)
import Data.Array (fromFoldable) as Array
import Data.Either (Either)
import Data.Functor.Mu (Mu, roll, unroll)
import Data.Map (Map)
import Data.Map (fromFoldable, toAscUnfoldable, singleton, insert) as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Monoid (class Monoid, mempty)
import Data.NonEmpty (NonEmpty, (:|))
import Data.Set (Set)
import Data.Set (toUnfoldable) as Set
import Data.StrMap (StrMap)
import Data.StrMap (toUnfoldable) as StrMap
import Data.String (joinWith)
import Data.Tuple (Tuple(..))
import Matryoshka (Algebra, GAlgebra, cata, para)

onlyType :: Proper -> Import
onlyType = Type <@> mempty
dataModule :: Array Proper -> Module
dataModule rest = Module (Proper "Data" :| rest)
dataImport :: Proper -> Tuple Module ImportModule
dataImport name =
  pure (Type name mempty) `importFrom`
    dataModule (pure name)
importAll :: ImportModule
importAll = ImportModule (pure mempty) mempty
importAllFrom :: Module -> Tuple Module ImportModule
importAllFrom = Tuple <@> importAll
importFrom :: Imports -> Module -> Tuple Module ImportModule
importFrom is = Tuple <@> ImportModule (pure is) mempty

aType :: ATypeF AType -> AType
aType = roll

aTypeApp :: AType -> AType -> AType
aTypeApp = map aType <<< TypeApp

aTypeFunction :: AType -> AType -> AType
aTypeFunction = map aType <<< TypeFunction

aTypeName :: Qualified Proper -> AType
aTypeName = aType <<< TypeName

aTypeVar :: Ident -> AType
aTypeVar = aType <<< TypeVar

typeAbsType :: Ident -> TypeAbs
typeAbsType = TypeAbs <@> Nothing

newType :: Proper -> AType -> DataTypeDef
newType name typ = DataTypeDef mempty $ SumType $ Map.singleton name $ pure typ

namedNewType :: Proper -> AType -> Tuple Proper DataTypeDef
namedNewType = lift2 compose Tuple newType

alias :: Proper -> NonEmpty Array (Qualified Proper) -> Tuple Proper DataTypeDef
alias name as = Tuple name $ DataTypeDef mempty $ TypeAlias (chainl aTypeApp as)

chainl :: (AType -> AType -> AType) -> NonEmpty Array (Qualified Proper) -> AType
chainl app (fn :| args) = go (aTypeName fn) args
  where
    go :: AType -> Array (Qualified Proper) -> AType
    go f as = case uncons as of
      Nothing -> f
      Just { head, tail } ->
        go (app f (aTypeName head)) tail

chainr :: (AType -> AType -> AType) -> NonEmpty Array (Qualified Proper) -> AType
chainr app (fn :| args) = go (aTypeName fn) args
  where
    go :: AType -> Array (Qualified Proper) -> AType
    go f as = case unsnoc as of
      Nothing -> f
      Just { init, last } ->
        go (app (aTypeName last) f) init

qualifyP :: Proper -> Qualified Proper
qualifyP p@(Proper name) = case name of
  "NonEmpty" -> qualifyData p
  "Either" -> qualifyData p
  "Map" -> qualifyData p
  "String" -> prim p
  _ -> Unqualified p

qualifyData :: Proper -> Qualified Proper
qualifyData p = Qualified (dataModule $ pure p) p

prim :: Proper -> Qualified Proper
prim = Qualified (Module (Proper "Prim" :| mempty))

qualify :: Tuple Module ImportModule -> Imports -> Tuple Module ImportModule
qualify (Tuple name (ImportModule mims mp)) is =
  Tuple name (ImportModule mims mp')
  where
    mp' = Map.insert (Module (lastOf name :| [])) is mp

thisModule :: ModuleData
thisModule =
  { imports: Map.fromFoldable
    [ importAllFrom $ Module $ Proper <$> "Prelude" :| mempty
    , dataImport $ Proper "Either"
    , [onlyType $ Proper "Mu"] `importFrom`
      (dataModule $ Proper <$> ["Functor", "Mu"])
    , dataImport (Proper "Map") `qualify`
        (Value <<< Ident <$> ["fromFoldable", "toAscUnfoldable", "singleton", "insert"])
    , dataImport $ Proper "Maybe"
    , [Class $ Proper "Monoid", Value $ Ident "mempty"] `importFrom`
      (dataModule $ pure $ Proper "Monoid")
    , dataImport (Proper "NonEmpty") <#> flip append
        (ImportModule (pure (pure (Operator (Op ":|")))) mempty)
    , dataImport $ Proper "Set"
    , dataImport $ Proper "StrMap"
    , [Type (Proper "Tuple") (pure AllCs)] `importFrom`
      (dataModule $ pure $ Proper "Tuple")
    ]
  , datatypes: Map.fromFoldable
    [ Proper "Module" `namedNewType`
        chainl aTypeApp (Unqualified <<< Proper <$> "NonEmpty" :| ["Array", "Proper"])
    , Tuple (Proper "Qualified") $ DataTypeDef [typeAbsType $ Ident "a"] $
        SumType $ Map.fromFoldable
        [ Tuple (Proper "Qualified")
          [ atnunqp "Module"
          , aTypeVar $ Ident "a"
          ]
        , Tuple (Proper "Unqualified") $ pure $ aTypeVar $ Ident "a"
        ]
    , Proper "Proper" `namedNewType` aTypeName (Unqualified $ Proper "String")
    , Proper "Ident" `namedNewType` aTypeName (Unqualified $ Proper "String")
    , Proper "Op" `namedNewType` aTypeName (Unqualified $ Proper "String")
    , Proper "ProperOp" `alias`
      ( Unqualified <<< Proper <$> "Either" :| ["Proper", "Op"] )
    , Proper "IdentOp" `alias`
      ( Unqualified <<< Proper <$> "Either" :| ["Ident", "Op"] )
    , Proper "ImportModules" `alias`
      ( Unqualified <<< Proper <$> "Map" :| ["Module", "ImportModule"] )
    , Tuple (Proper "ImportModule") $ DataTypeDef mempty $
        SumType $ Map.singleton (Proper "ImportModule") $
        [ aTypeApp (atnunqp "Maybe") $ atnunqp "Imports"
        , chainl aTypeApp (Unqualified <<< Proper <$> "Map" :| ["Module", "Imports"])
        ]
    , Tuple (Proper "FUNCTION") $ DataTypeDef mempty $
        TypeAlias $
          chainr aTypeFunction (Unqualified <<< Proper <$> "Module" :| ["Imports", "ImportModule"])
            `aTypeFunction` ((atnunqp "Map" `aTypeApp` atnunqp "Module")
              `aTypeApp` (atnunqp "Meh" `aTypeFunction` atnunqp "Eh"))
    ]
  }
  where atnunqp = aTypeName <<< Unqualified <<< Proper

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

wrap :: String -> String
wrap a = "(" <> a <> ")"
wrapIf :: Boolean -> String -> String
wrapIf true = wrap
wrapIf false = id
wrapIf' :: String -> Boolean -> String
wrapIf' = flip wrapIf
wrapIfl :: forall a. (a -> Boolean) -> (a -> String) -> (a -> String)
wrapIfl = lift2 wrapIf

data DataType
  = TypeAlias AType
  | SumType (Map Proper (Array AType))
instance showDataType :: Show DataType where
  show (TypeAlias t) = showAType t
  show (SumType m) = joinWith " | " $ Map.toAscUnfoldable m <#> \(Tuple c ts) ->
    show c <> case ts of
      [] -> ""
      _ ->
        " " <> joinWith " "
          (wrapIfl (isTypeFunction || isTypeApp) showAType <$> ts)
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
data ATypeF a
  = TypeName (Qualified Proper)
  | TypeVar Ident
  | TypeFunction a a
  | TypeApp a a
  | TypeRow (StrMap a) (Maybe a)
type AType = Mu ATypeF
derive instance functorATypeF :: Functor ATypeF
showAType :: AType -> String
showAType one = para showInner one
  where
    showInner :: GAlgebra (Tuple AType) ATypeF String
    showInner (TypeName q) = show q
    showInner (TypeVar v) = show v
    showInner (TypeFunction (Tuple a l) (Tuple b r)) =
      left <> " -> " <> right
      where
        left = wrapIf' l $ isTypeFunction a
        right = r
    showInner (TypeApp (Tuple f l) (Tuple a r)) =
      left <> " " <> right
      where
        left = wrapIf' l (isTypeFunction f)
        right = wrapIf' r (isTypeApp a || isTypeFunction a)
    showInner (TypeRow m Nothing) =
      "( " <> showFields m <> " )"
    showInner (TypeRow m (Just (Tuple _ a))) =
      "( " <> showFields m <> " | " <> a <> " )"

    showFields m = joinWith ", " $ StrMap.toUnfoldable m <#> \(Tuple k (Tuple _ v)) ->
      k <> " :: " <> v
isTypeFunction :: AType -> Boolean
isTypeFunction = unroll >>> case _ of
  TypeFunction _ _ -> true
  _ -> false
isTypeApp :: AType -> Boolean
isTypeApp = unroll >>> case _ of
  TypeApp _ _ -> true
  _ -> false

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

type TypeAbses = Array TypeAbs
data TypeAbs = TypeAbs Ident (Maybe AKind)
instance showTypeAbs :: Show TypeAbs where
  show (TypeAbs i Nothing) = show i
  show (TypeAbs i (Just k)) = "(" <> show i <> " :: " <> show k <> ")"
data DataTypeDef = DataTypeDef TypeAbses DataType
type DataTypeDecls = Map Proper DataTypeDef
showDataTypeDecls :: DataTypeDecls -> String
showDataTypeDecls = joinWith "\n" <<< Map.toAscUnfoldable >>> map
  \(Tuple name (DataTypeDef vs dt)) ->
    let
      vars = case vs of
        [] -> ""
        _ -> " " <> joinWith " " (show <$> vs)
    in show (declKeyword dt) <> " " <> show name <> vars <> " = " <> show dt

type Modules = Map Module ModuleData
type ModuleData =
  { imports :: ImportModules
  , datatypes :: DataTypeDecls
  }
showModuleData :: ModuleData -> String
showModuleData = do
  imports <- showImportModules <<< _.imports
  datatypes <- showDataTypeDecls <<< _.datatypes
  pure (imports <> "\n\n" <> datatypes)
