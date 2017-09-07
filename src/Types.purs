module Types where

import Prelude

import Control.Apply (lift2)
import Control.Comonad.Cofree (Cofree, head, mkCofree, tail, (:<))
import Control.Monad.State (State, gets, modify, runState)
import Data.Array (concatMap, last, uncons, unsnoc)
import Data.Array (fromFoldable) as Array
import Data.Bifunctor (lmap)
import Data.Const (Const(..))
import Data.Either (Either)
import Data.Function (on)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Mu (Mu, roll, unroll)
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (FProxy, SProxy(..), VariantF)
import Data.Functor.Variant as VF
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map (fromFoldable, toAscUnfoldable, singleton, insert) as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Monoid (class Monoid, mempty)
import Data.Monoid.Additive (Additive(..))
import Data.Newtype (unwrap)
import Data.NonEmpty (NonEmpty, (:|))
import Data.Pair (Pair(..))
import Data.Set (Set)
import Data.Set (toUnfoldable) as Set
import Data.StrMap (StrMap)
import Data.StrMap (toUnfoldable, insert) as StrMap
import Data.String (Pattern(..), Replacement(..), drop, joinWith, length, replaceAll, take)
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..), fst, snd, swap, uncurry)
import Matryoshka (class Recursive, Algebra, cata, project)
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
aTypeApp = aTypePair _app

aTypeFunction :: ATypeV -> ATypeV -> ATypeV
aTypeFunction = aTypePair _function

aTypeName :: Qualified Proper -> ATypeV
aTypeName = aTypeConst _name

aTypeVar :: Ident -> ATypeV
aTypeVar = aTypeConst _var

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
          testType
    ]
  }

atnunqp :: String -> ATypeV
atnunqp = aTypeName <<< Unqualified <<< Proper

testType :: ATypeV
testType = chainl aTypeFunction (Unqualified <<< Proper <$> "Module" :| ["Imports", "ImportModule"])
  `aTypeFunction` ((atnunqp "Map" `aTypeApp` (atnunqp "Maybe" `aTypeApp` atnunqp "Module"))
    `aTypeApp` (atnunqp "Meh" `aTypeFunction` atnunqp "Eh"))

otherTest :: ATypeV
otherTest = chainr aTypeFunction (Unqualified <<< Proper <$> "Heus" :| ["Yo", "Hey"])

testTypeL :: Tuple (Maybe (ZipperVF ATypeV Unit)) ATypeV
testTypeL = extract1 left testType

testTypeLS :: String
testTypeLS = case testTypeL of
  Tuple (Just z) h ->
    "(" <> simpleShowZ1 showAType z <> ", " <> showAType h <> ")"
  Tuple Nothing h -> showAType h

testTypeC :: Tuple String ATypeVC
testTypeC = case showTagged testType of
  Tuple s v -> Tuple s $ Tuple mempty (Additive (length s)) :< v

testTypeCS :: String
testTypeCS = cofrecurse (snd testTypeC)

testTypeLC :: Tuple (Maybe (ZipperVF ATypeVC Tag)) ATypeVC
testTypeLC = extract1C rightC (snd testTypeC)

testTypeLC' :: Tuple ZipperVC ATypeVC
testTypeLC' = extract1C' rightC (snd testTypeC)

testTypeLSC :: String
testTypeLSC = case testTypeLC of
  Tuple (Just z) h ->
    "(" <> simpleShowZ1 (forget >>> showAType) z <> ", " <> showAType (forget h) <> ")"
  Tuple Nothing h -> showAType (forget h)

testPatchSameR :: Tuple String ATypeVC
testPatchSameR = uncurry patch (map forget testTypeLC') (fst testTypeC) mempty Nothing

testPatchSameL :: Tuple String ATypeVC
testPatchSameL = uncurry patch (map forget $ extract1C' leftC (snd testTypeC)) (fst testTypeC) mempty Nothing

testPatchExplodeR :: Tuple String ATypeVC
testPatchExplodeR = patch (fst testTypeLC') otherTest (fst testTypeC) mempty Nothing

testPatchExplodeL :: Tuple String ATypeVC
testPatchExplodeL = patch (fst $ extract1C' leftC (snd testTypeC)) otherTest (fst testTypeC) mempty Nothing

forget :: forall f a. Functor f => Cofree f a -> Mu f
forget v = tail v # map forget # roll

badindent :: String -> String
badindent = replaceAll (Pattern "\n") (Replacement "\n  ")

cofrecurse :: ATypeVC -> String
cofrecurse v = let t = " >: " <> show (head v) in
  ( VF.case_
  # VF.on _var (unwrap >>> show >>> (_ <> t))
  # VF.on _name (unwrap >>> show >>> (_ <> t))
  # VF.on _function (\(Pair l r) -> "function" <> t <>
      badindent ("\n" <> cofrecurse l <> "\n" <> cofrecurse r))
  # VF.on _app (\(Pair l r) -> "app" <> t <>
      badindent ("\n" <> cofrecurse l <> "\n" <> cofrecurse r))
  ) (tail v)

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

joinWithIfNE :: forall a. String -> (a -> String) -> Array a -> String
joinWithIfNE _ _ [] = ""
joinWithIfNE sep f as = sep <> joinWith sep (f <$> as)

data DataType
  = TypeAlias ATypeV
  | SumType (Map Proper (Array ATypeV))
instance showDataType :: Show DataType where
  show (TypeAlias t) = showAType t
  show (SumType m) = joinWith " | " $ Map.toAscUnfoldable m <#> \(Tuple c ts) ->
    show c <> joinWithIfNE " " (showAType' (Just FnAppParen)) ts
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
type ATypeVC = Tagged ATypeVF

data DPair' a da = DPairL' da a | DPairR' a da
derive instance functorDPair' :: Functor (DPair' a)
instance showDPair' :: (Show a, Show da) => Show (DPair' a da) where
  show (DPairL' da a) = "(DPairL' " <> show da <> " " <> show a <> ")"
  show (DPairR' a da) = "(DPairR' " <> show a <> " " <> show da <> ")"
data DStrMap' a da = DStrMap' String da (StrMap a)
type DATypeVR' a da =
  ( name     :: Unit
  , var      :: Unit
  , function :: DPair' a da
  , app      :: DPair' a da
  -- , row      :: Tuple (DStrMap' a da) da
  )
data DMu' f df = DIn' (df (Mu f) (DMu' f df)) (DMu' f df)

type ZipperVR a =
  ( function :: FProxy (DPair' a)
  , app :: FProxy (DPair' a)
  )
type ZipperVF a = VariantF (ZipperVR a)
type ZipperVF' a = Compose Maybe (ZipperVF a)
type ZipperVF'' a = Compose Maybe (Compose (Tuple Tag) (ZipperVF a))
type ZipperV = Mu (ZipperVF' ATypeV)
type ZipperVC = Tagged (ZipperVF' ATypeVC)

simpleShowZ :: forall a. (a -> String) -> Algebra (ZipperVF a) String
simpleShowZ inner = VF.match
  { function: showDPair' " -> "
  , app: showDPair' " "
  --, row: const "()"
  }
  where
    showDPair' :: String -> DPair' a String -> String
    showDPair' s (DPairL' da a) = "{" <> da <> "}" <> s <> inner a
    showDPair' s (DPairR' a da) = inner a <> s <> "{" <> da <> "}"

simpleShowZ1 :: forall a s. Show s => (a -> String) -> ZipperVF a s -> String
simpleShowZ1 inner v = simpleShowZ inner (v <#> show)

_name = SProxy :: SProxy "name"
_var = SProxy :: SProxy "var"
_function = SProxy :: SProxy "function"
_app = SProxy :: SProxy "app"

downZipperVF :: forall a da. (a -> da) -> ATypeVF a -> ATypeVF (ZipperVF a da)
downZipperVF down = VF.case_
  # VF.on _name (VF.inj _name <<< rewrap)
  # VF.on _var (VF.inj _var <<< rewrap)
  # VF.on _function (downDPair' down >>> rePair' _function)
  # VF.on _app (downDPair' down >>> rePair' _app)

rePair' ::
  forall a da sym bleh meh.
    IsSymbol sym =>
    RowCons sym (FProxy Pair) bleh ATypeVR =>
    RowCons sym (FProxy (DPair' a)) meh (ZipperVR a) =>
  SProxy sym -> Pair (DPair' a da) -> ATypeVF (ZipperVF a da)
rePair' sym = VF.inj sym <<< map (VF.inj sym)

{-
downZipperVF' :: forall a da. (a -> da) -> ATypeVF a -> ZipperVF' a da
downZipperVF' down = VF.default (Compose Nothing)
    # VF.on _function (downDPair' down >>> map (VF.inj _function) >>> Just >>> Compose)
    # VF.on _app (downDPair' down >>> map (VF.inj _app) >>> Just >>> Compose)
-}

{-
     ATypeV
down (a -> b) =
              ATypeVF ()
              ->
  (a, _ -> b)    (b, a -> _)
  Tuple ATypeV ZipperV

_ -> b == inj "function" $ DPairL' Unit (b :: ATypeV)
(a, _ -> b) == inj "function" $ DPairL' (a :: ATypeV) (b :: ATypeV)
-}

downZipper1 :: ATypeV -> ATypeVF (ZipperVF ATypeV ATypeV)
downZipper1 v =
  ( VF.case_
  # VF.on _name (VF.inj _name <<< rewrap)
  # VF.on _var (VF.inj _var <<< rewrap)
  # VF.on _function (downDPair' id >>> rePair' _function)
  # VF.on _app (downDPair' id >>> rePair' _app)
  ) (unroll v)

extract1 ::
  (Pair ATypeV -> Tuple (DPair' ATypeV Unit) ATypeV) ->
  ATypeV -> Tuple (Maybe (ZipperVF ATypeV Unit)) ATypeV
extract1 choose this =
  ( VF.default (Tuple Nothing this)
  # VF.on _function (lmap (Just <<< VF.inj _function) <<< choose)
  # VF.on _app (lmap (Just <<< VF.inj _app) <<< choose)
  ) (unroll this)

extract1' ::
  (Pair ATypeV -> Tuple (DPair' ATypeV Unit) ATypeV) ->
  ATypeV -> Tuple ZipperV ATypeV
extract1' choose = extract1 choose >>> lmap unroll1

extract1C ::
  (Pair ATypeVC -> Tuple (DPair' ATypeVC Tag) ATypeVC) ->
  ATypeVC -> Tuple (Maybe (ZipperVF ATypeVC Tag)) ATypeVC
extract1C choose this =
  ( VF.default (Tuple Nothing this)
  # VF.on _function (lmap (Just <<< VF.inj _function) <<< choose)
  # VF.on _app (lmap (Just <<< VF.inj _app) <<< choose)
  ) (tail this)

extract1C' ::
  (Pair ATypeVC -> Tuple (DPair' ATypeVC Tag) ATypeVC) ->
  ATypeVC -> Tuple ZipperVC ATypeVC
extract1C' choose v =
  extract1C choose v # lmap (unroll1C (head v))

left :: forall a. Pair a -> Tuple (DPair' a Unit) a
left (Pair l r) = Tuple (DPairL' unit r) l

right :: forall a. Pair a -> Tuple (DPair' a Unit) a
right (Pair l r) = Tuple (DPairR' l unit) r

leftC :: Pair ATypeVC -> Tuple (DPair' ATypeVC Tag) ATypeVC
leftC (Pair l r) = Tuple (DPairL' (head l) r) l

rightC :: Pair ATypeVC -> Tuple (DPair' ATypeVC Tag) ATypeVC
rightC (Pair l r) = Tuple (DPairR' l (head r)) r

unroll1 :: Maybe (ZipperVF ATypeV Unit) -> ZipperV
unroll1 = roll <<< Compose <<< map (_ $> roll (Compose Nothing))

unroll1C :: Tag -> Maybe (ZipperVF ATypeVC Tag) -> ZipperVC
unroll1C h v = h :< Compose (map (mkCofree <@> Compose Nothing) <$> v)

downDPair' :: forall a da. (a -> da) -> Pair a -> Pair (DPair' a da)
downDPair' down (Pair l r) = Pair
  (DPairL' (down l) r)
  (DPairR' l (down r))

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
instance diff1StrMap :: Diff1 StrMap DStrMap where
  upF (ZF eh a) =
    case fromDF eh of
      DStrMap key da rest ->
        StrMap.insert key (up (Z da a)) rest
instance diff1Const :: Diff1 (Const a) (Const Void) where
  upF (ZF eh _) = absurd (unwrap (fromDF eh))
instance diff1Identity :: Diff1 Identity (Const Unit) where
  upF (ZF _ x) = Identity x
instance diff1Pair :: Diff1 Pair DPair where
  upF (ZF eh a) =
    case fromDF eh of
      DPairR l da   -> Pair l (up (Z da a))
      DPairL   da r -> Pair   (up (Z da a)) r
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

-- | A tag consists of the following:
-- |   1. the starting index *relative to the parent*
-- |   2. the length of the string that represents this chunk
type Tag = Tuple (Additive Int) (Additive Int)
-- | A tagged recursive structure of `Cofree` and `Tag`.
type Tagged f = Cofree f Tag
-- | Used before a Cofree is tagged.
type Untagged f = f (Tagged f)
-- | While building up a tag, accumulate a `String` of the current content,
-- | which also gives the index relative to the parent (see `Tag`).
type Tagging a = State String a

tag :: Tagging (Untagged ATypeVF) -> Tuple String (Untagged ATypeVF)
tag = swap <<< (runState <@> mempty)

recur :: Tuple String (Untagged ATypeVF) -> Tagging (Tagged ATypeVF)
recur (Tuple s r) = do
  offset <- gets (Additive <<< length)
  literal s
  pure $ Tuple offset (Additive (length s)) :< r

literal :: String -> Tagging Unit
literal s = modify (_ <> s)

simple :: ATypeVF Void -> String -> Tuple String (Untagged ATypeVF)
simple v s = Tuple s $ map absurd v

simpleShowConst ::
  forall a b sym bleh.
    IsSymbol sym =>
    RowCons sym (FProxy (Const a)) bleh ATypeVR =>
    Show a =>
  SProxy sym -> Const a b -> Tuple String (ATypeVF (Tagged ATypeVF))
simpleShowConst k v = simple (VF.inj k $ rewrap v) $ show $ unwrap v

rewrap :: forall a b c. Const a b -> Const a c
rewrap (Const a) = Const a

showTagged1P :: Maybe Annot -> Algebra ATypeVF (Tuple String (Untagged ATypeVF))
showTagged1P p = VF.match
  { name: simpleShowConst _name
  , var: simpleShowConst _var
  , function: \(Pair l r) -> wrapTagIf mayNeedFnParen do
      a <- recur l
      literal " -> "
      b <- recur r
      pure (VF.inj _function (Pair a b))
  , app: \(Pair l r) -> wrapTagIf mayNeedAppParen do
      a <- recur l
      literal " "
      b <- recur r
      pure (VF.inj _app (Pair a b))
  --, row: \meh -> tag do
      --literal "meh"
      --pure (VF.inj (SProxy :: SProxy "row") meh)
  }
  where
    wrapTagIf pred v
      | pred p    = tag $ literal "(" *> v <* literal ")"
      | otherwise = tag v

whileAnnotatingDown ::
  forall t f a ann.
    Recursive t f =>
  Maybe ann -> (f t -> f (Tuple ann t)) ->
  (Maybe ann -> Algebra f a) -> t -> a
whileAnnotatingDown ann0 mkAnn f = f ann0 <<< go
  where
    go t = mkAnn (project t) <#>
      \(Tuple ann t) -> f (Just ann) (go t)

data Annot = FnParen | AppParen | FnAppParen | None
derive instance eqAnnot :: Eq Annot
needsFnParen :: Annot -> Boolean
needsFnParen FnParen = true
needsFnParen FnAppParen = true
needsFnParen _ = false
needsAppParen :: Annot -> Boolean
needsAppParen AppParen = true
needsAppParen FnAppParen = true
needsAppParen _ = false
mayNeedFnParen :: Maybe Annot -> Boolean
mayNeedFnParen = maybe false needsFnParen
mayNeedAppParen :: Maybe Annot -> Boolean
mayNeedAppParen = maybe false needsAppParen
-- instance heytingAlgebraAnnot :: HeytingAlgebra Annot
annotPrec :: forall a. ATypeVF a -> ATypeVF (Tuple Annot a)
annotPrec = VF.match
  { name: VF.inj _name <<< rewrap
  , var: VF.inj _var <<< rewrap
  , function: VF.inj _function <<< bimapPair (Tuple FnParen) (Tuple None)
  , app: VF.inj _app <<< bimapPair (Tuple FnParen) (Tuple FnAppParen)
  } where bimapPair f g (Pair a b) = Pair (f a) (g b)

showTagged :: forall t. Recursive t ATypeVF =>
  t -> Tuple String (Untagged ATypeVF)
showTagged = whileAnnotatingDown Nothing annotPrec showTagged1P

showTagged' :: forall t. Recursive t ATypeVF =>
  Maybe Annot -> t -> Tuple String (Untagged ATypeVF)
showTagged' ann = whileAnnotatingDown ann annotPrec showTagged1P

showAType :: forall t. Recursive t ATypeVF => t -> String
showAType = showTagged >>> fst

showAType' :: forall t. Recursive t ATypeVF => Maybe Annot -> t -> String
showAType' ann = showTagged' ann >>> fst

evalFrom :: Additive Int -> Tuple String (Untagged ATypeVF) -> Tuple String ATypeVC
evalFrom st (Tuple s v) =
  Tuple s $ Tuple st (Additive (length s)) :< v

showTaggedFrom :: forall t. Recursive t ATypeVF =>
  Additive Int -> Maybe Annot -> t -> Tuple String ATypeVC
showTaggedFrom i ann = showTagged' ann >>> evalFrom i

modifyHead :: forall f a. (a -> a) -> Cofree f a -> Cofree f a
modifyHead f = lift2 (:<) (f <<< head) tail

patch ::
  ZipperVC -> ATypeV -> String ->
  (Additive Int -> Maybe Annot -> Tuple String ATypeVC)
patch positioned replacement old i =
  let
    Tuple offset size = head positioned
  in case tail positioned of
    Compose Nothing -> \ann ->
      let
        before = take (unwrap (i <> offset)) old
        after  = drop (unwrap (i <> offset <> size)) old
        Tuple slice node = showTaggedFrom offset ann replacement
        spliced = before <> slice <> after
      in Tuple spliced node
    Compose (Just inside) -> const
      let
        next da offset ann f =
          let
            Tuple new updated = patch da replacement old i $ Just ann
            diff = Additive $ ((-) `on` length) new old
          in Tuple new (Tuple offset (size <> diff) :< f diff updated)
        handle ::
          forall sym bleh.
            IsSymbol sym =>
            RowCons sym (FProxy Pair) bleh ATypeVR =>
          SProxy sym -> Annot -> Annot ->
          DPair' ATypeVC ZipperVC -> Tuple String ATypeVC
        handle k ann _ (DPairL' da a) =
          next da mempty ann
            \diff updated ->
              VF.inj k (Pair updated $ modifyHead (_ <> Tuple diff mempty) a)
        handle k _ ann (DPairR' a da) =
          next da offset ann
            \_ updated ->
              VF.inj k (Pair a updated)
      in inside # VF.match
        { function: handle _function FnParen None
        , app: handle _app FnParen FnAppParen
        }

showFields :: forall a. StrMap (Tuple a String) -> String
showFields m = joinWith ", " $ StrMap.toUnfoldable m <#> \(Tuple k (Tuple _ v)) ->
  k <> " :: " <> v

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
      vars = joinWithIfNE " " show vs
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
