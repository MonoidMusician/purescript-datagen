module Types where

import Prelude

import Control.Apply (lift2)
import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Monad.State (State, gets, modify, runState)
import Data.Array (concatMap, last, uncons, unsnoc)
import Data.Array (fromFoldable) as Array
import Data.Bifunctor (lmap)
import Data.Const (Const(..))
import Data.Either (Either)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Mu (Mu, roll, unroll)
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (FProxy, SProxy(..), VariantF)
import Data.Functor.Variant as VF
import Data.HeytingAlgebra (ff, tt)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map (fromFoldable, toAscUnfoldable, singleton, insert) as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Monoid (class Monoid, mempty)
import Data.Monoid.Additive (Additive(..))
import Data.Newtype (unwrap)
import Data.NonEmpty (NonEmpty, (:|))
import Data.Pair (Pair(..))
import Data.Set (Set)
import Data.Set (toUnfoldable) as Set
import Data.StrMap (StrMap)
import Data.StrMap (toUnfoldable, insert) as StrMap
import Data.String (drop, joinWith, length, take)
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..), fst, uncurry)
import Data.Variant as Variant
import Matryoshka (Algebra, GAlgebra, cata, para)
import Unsafe.Coerce (unsafeCoerce)

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

aType :: ATypeVF ATypeV -> ATypeV
aType = roll

aTypeConst ::
  forall sym a bleh.
    IsSymbol sym =>
    RowCons sym (FProxy (Const a)) bleh ATypeVR =>
  SProxy sym -> a -> ATypeV
aTypeConst k a = aType $ VF.inj k $ Const a

aTypePair ::
  forall sym bleh.
    IsSymbol sym =>
    RowCons sym (FProxy Pair) bleh ATypeVR =>
  SProxy sym -> ATypeV -> ATypeV -> ATypeV
aTypePair k a b  = aType $ VF.inj k $ Pair a b

aTypeProduct ::
  forall sym f g bleh.
    IsSymbol sym =>
    Functor f =>
    Functor g =>
    RowCons sym (FProxy (Product f g)) bleh ATypeVR =>
  SProxy sym -> f ATypeV -> g ATypeV -> ATypeV
aTypeProduct k a b = aType $ VF.inj k $ Product $ Tuple a b

aTypeApp :: ATypeV -> ATypeV -> ATypeV
aTypeApp = aTypePair (SProxy :: SProxy "app")

aTypeFunction :: ATypeV -> ATypeV -> ATypeV
aTypeFunction = aTypePair (SProxy :: SProxy "function")

aTypeName :: Qualified Proper -> ATypeV
aTypeName = aTypeConst (SProxy :: SProxy "name")

aTypeVar :: Ident -> ATypeV
aTypeVar = aTypeConst (SProxy :: SProxy "var")

typeAbsType :: Ident -> TypeAbs
typeAbsType = TypeAbs <@> Nothing

newType :: Proper -> ATypeV -> DataTypeDef
newType name typ = DataTypeDef mempty $ SumType $ Map.singleton name $ pure typ

namedNewType :: Proper -> ATypeV -> Tuple Proper DataTypeDef
namedNewType = lift2 compose Tuple newType

alias :: Proper -> NonEmpty Array (Qualified Proper) -> Tuple Proper DataTypeDef
alias name as = Tuple name $ DataTypeDef mempty $ TypeAlias (chainl aTypeApp as)

chainl :: (ATypeV -> ATypeV -> ATypeV) -> NonEmpty Array (Qualified Proper) -> ATypeV
chainl app (fn :| args) = go (aTypeName fn) args
  where
    go :: ATypeV -> Array (Qualified Proper) -> ATypeV
    go f as = case uncons as of
      Nothing -> f
      Just { head, tail } ->
        go (app f (aTypeName head)) tail

chainr :: (ATypeV -> ATypeV -> ATypeV) -> NonEmpty Array (Qualified Proper) -> ATypeV
chainr app (fn :| args) = go (aTypeName fn) args
  where
    go :: ATypeV -> Array (Qualified Proper) -> ATypeV
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
  } where atnunqp = aTypeName <<< Unqualified <<< Proper

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
  = TypeAlias ATypeV
  | SumType (Map Proper (Array ATypeV))
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
type ATypeVR =
  ( name     :: FProxy (Const (Qualified Proper))
  , var      :: FProxy (Const Ident)
  , function :: FProxy Pair
  , app      :: FProxy Pair
  -- , row      :: FProxy (Product StrMap Maybe)
  )
type ATypeVF = VariantF ATypeVR
type ATypeV = Mu ATypeVF

data DPair' a da = DPairL' da a | DPairR' a da
data DStrMap' a da = DStrMap' String da (StrMap a)
type DATypeVR' a da =
  ( name     :: Unit
  , var      :: Unit
  , function :: DPair' a da
  , app      :: DPair' a da
  -- , row      :: Tuple (DStrMap' a da) da
  )
data DMu' f df = DIn' (df (Mu f) (DMu' f df)) (DMu' f df)

foreign import data D :: Type -> Type
toD :: forall f df. Diff f df => df -> D f
toD = unsafeCoerce
fromD :: forall f df. Diff f df => D f -> df
fromD = unsafeCoerce
foreign import data DF :: (Type -> Type) -> (Type -> Type)
toDF :: forall f df x. Diff1 f df => df x -> DF f x
toDF = unsafeCoerce
fromDF :: forall f df x. Diff1 f df => DF f x -> df x
fromDF = unsafeCoerce
data Z x = Z (D x) x
data ZF f x = ZF (DF f x) x
class Diff a da | a -> da where
  up :: Z a -> a
class
  ( Functor f
  -- , Functor df
  ) <= Diff1 (f :: Type -> Type) (df :: Type -> Type) | f -> df where
    upF     :: forall x dx. Diff x dx => ZF f x  ->           f x
    --aroundF :: forall x. ZF f x  ->  ZF f (ZF f x)
    --downF   :: forall x.    f x  ->     f (ZF f x)
{-
instance diff1StrMap :: Diff1 a da => Diff1 StrMap DStrMap where
  upF (ZF eh x) = case fromDF eh of
    DStrMap key dx rest ->
      StrMap.insert key (upF (ZF (toDF dx) x)) rest
-}
instance diff1Const :: Diff1 (Const a) (Const Void) where
  upF (ZF eh _) = absurd (unwrap (fromDF eh))
instance diff1Identity :: Diff1 Identity (Const Unit) where
  upF (ZF _ x) = Identity x
instance diff1Pair :: Diff1 Pair DPair where
  upF (ZF eh a) =
    case fromDF eh of
      DPairR l da   -> Pair l (up (Z ( da) a))
      DPairL   da r -> Pair   (up (Z ( da) a)) r
{-
instance diff1Compose ::
  ( Diff1 f df
  , Diff1 g fg
  ) => Diff1 (Compose f g) (Product (Compose df g) dg) where
    upF (ZF eh x) =
      case fromDF eh of
        (Product (Tuple (Compose dfg) dg)) ->
          let
            g = upF (ZF dg x)
          in Compose $ ?finalize dg x
-}

data DPair a = DPairL (D a) a | DPairR a (D a)
instance functorDPair :: Functor D => Functor DPair where
  map f (DPairL da a) = DPairL (map f da) (f a)
  map f (DPairR a da) = DPairR (f a) (map f da)
data DStrMap a = DStrMap String (D a) (StrMap a)
data DMu f = DIn ((DF f) (Mu f)) (DMu f)
type DATypeVR =
  ( name     :: FProxy (Const Unit)
  , var      :: FProxy (Const Unit)
  , function :: FProxy (DPair)
  , app      :: FProxy (DPair)
  -- , row      :: FProxy (Product D DStrMap)
  )

joinPair :: String -> Pair String -> String
joinPair m (Pair l r) = l <> m <> r

simpleShow :: Algebra ATypeVF String
simpleShow = VF.match
  { name: unwrap >>> show
  , var: unwrap >>> show
  , function: joinPair " -> "
  , app: joinPair " "
  --, row: const "()"
  }

type Tag = Tuple (Additive Int) String
type Tagged f = Cofree f Tag
type Tagging a = State Tag a

len :: Tag -> Additive Int
len = Additive <<< length <<< content

start :: Tag -> Additive Int
start (Tuple i _) = i

end :: Tag -> Additive Int
end = start <> len

content :: Tag -> String
content (Tuple _ s) = s

tag :: Tagging (ATypeVF (Tagged ATypeVF)) -> Tagged ATypeVF
tag = flip runState mempty >>> uncurry (flip (:<))

literal :: String -> Tagging Unit
literal s = modify (_ <> Tuple (Additive (length s)) s)

subresult :: Tagged ATypeVF -> Tagging (Tagged ATypeVF)
subresult subr = do
  let Tuple index content = head subr
  offset <- gets fst
  literal content
  pure $ lmap (_ <> offset) <$> subr

simple :: ATypeVF Void -> String -> Tagged ATypeVF
simple v s = Tuple mempty s :< map absurd v

simpleShowConst ::
  forall a b sym bleh.
    IsSymbol sym =>
    RowCons sym (FProxy (Const a)) bleh ATypeVR =>
    Show a =>
  SProxy sym -> Const a b -> Tagged ATypeVF
simpleShowConst k v = simple (VF.inj k $ rewrap v) $ show $ unwrap v

rewrap :: forall a b c. Const a b -> Const a c
rewrap (Const a) = Const a

showTagged1 :: Algebra ATypeVF (Tagged ATypeVF)
showTagged1 = VF.match
  { name: simpleShowConst (SProxy :: SProxy "name")
  , var: simpleShowConst (SProxy :: SProxy "var")
  , function: \(Pair l r) -> tag do
      a <- subresult l
      literal " -> "
      b <- subresult r
      pure (VF.inj (SProxy :: SProxy "function") (Pair a b))
  , app: \(Pair l r) -> tag do
      a <- subresult l
      literal " "
      b <- subresult r
      pure (VF.inj (SProxy :: SProxy "app") (Pair a b))
  --, row: \meh -> tag do
      --literal "meh"
      --pure (VF.inj (SProxy :: SProxy "row") meh)
  }

type ZipperVR a =
  ( function :: FProxy (DPair' a)
  , app :: FProxy (DPair' a)
  )
type ZipperVF a = VariantF (ZipperVR a)
type ZipperVF' a = Compose Maybe (ZipperVF a)
type ZipperV = Mu (ZipperVF' ATypeV)
patch :: Tagged (ZipperVF' (Tagged ATypeVF)) -> ATypeV -> Tagged ATypeVF
patch positioned replacement =
  let
    caput = head positioned
    st = start caput
    sz = len caput
    old = content caput
  in case tail positioned of
    Compose Nothing ->
      lmap (_ <> st) <$> cata showTagged1 replacement
    Compose (Just inside) ->
      let
        next ::
          forall sym bleh.
            IsSymbol sym =>
            RowCons sym (FProxy Pair) bleh ATypeVR =>
          SProxy sym -> DPair' (Tagged ATypeVF) (Tagged (ZipperVF' (Tagged ATypeVF))) -> Tagged ATypeVF
        next k (DPairL' da a) =
          let
            startAt = start (head updated)
            endAt = end (head updated)
            before = take (unwrap startAt) old
            after = drop (unwrap endAt) old
            updated = patch da replacement
            spliced = before <> content (head updated) <> after
            diff = Additive $ length spliced - (unwrap sz)
          in Tuple st spliced :< (VF.inj k $ Pair updated $ lmap (_ <> diff) <$> a)
        next k (DPairR' a da) =
          let
            startAt = start (head updated)
            endAt = end (head updated)
            before = take (unwrap startAt) old
            after = drop (unwrap endAt) old
            updated = patch da replacement
            spliced = before <> content (head updated) <> after
          in Tuple st spliced :< (VF.inj k $ Pair a $ patch da replacement)
      in inside # VF.match
        { function: next (SProxy :: SProxy "function")
        , app: next (SProxy :: SProxy "app")
        }

showAType :: ATypeV -> String
showAType one = para showInner one
  where
    showInner :: GAlgebra (Tuple ATypeV) ATypeVF String
    showInner =
      VF.match
        { name: unwrap >>> show
        , var: unwrap >>> show
        , function:
            \(Pair (Tuple a l) (Tuple b r)) ->
              let left = wrapIf' l $ isTypeFunction a
              in left <> " -> " <> r
        , app:
            \(Pair (Tuple f l) (Tuple a r)) ->
              let
                left = wrapIf' l (isTypeFunction f)
                right = wrapIf' r (isTypeApp a || isTypeFunction a)
              in left <> " " <> right
        --, row:
            --case _ of
              --Product (Tuple m Nothing) ->
                --"( " <> showFields m <> " )"
              --Product (Tuple m (Just (Tuple _ a))) ->
                --"( " <> showFields m <> " | " <> a <> " )"
        }

showFields :: forall a. StrMap (Tuple a String) -> String
showFields m = joinWith ", " $ StrMap.toUnfoldable m <#> \(Tuple k (Tuple _ v)) ->
  k <> " :: " <> v

is ::
  forall sym f bleh rows a.
    IsSymbol sym =>
    RowCons sym (FProxy f) bleh rows =>
  SProxy sym -> VariantF rows a -> Boolean
is k = VF.on k tt $ VF.default ff

isTypeFunction :: ATypeV -> Boolean
isTypeFunction = unroll >>> is (SProxy :: SProxy "function")
isTypeApp :: ATypeV -> Boolean
isTypeApp = unroll >>> is (SProxy :: SProxy "app")

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
