module Test.Main where

import Combinators (aTypeApp, aTypeFunction, aTypeName, aTypeVar, alias, chainl, chainr, dataImport, dataModule, importAllFrom, importFrom, namedNewType, onlyType, qualify, typeAbsType)
import Control.Comonad.Cofree (head, (:<))
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log, logShow)
import Data.Bitraversable (bitraverse)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Monoid (mempty)
import Data.NonEmpty ((:|))
import Data.Spliceable (length)
import Data.Tuple (Tuple(..), fst, snd, uncurry)
import Prelude (Unit, append, discard, flip, map, pure, void, ($), (<#>), (<$>), (<<<), (<>), (>>>))
import Printing (cofrecurse)
import Recursion (forget)
import Reprinting (ATypeVC, Tag, patch, showAType, showModuleData, showTagged)
import Types (ATypeV, Constructors(..), DataType(..), DataTypeDef(..), Ident(..), Import(..), ImportModule(..), Module(..), ModuleData, Op(..), Proper(..), Qualified(..))
import Zippers (ZipperVC, ZipperVF, extract1, extract1C, extract1C', left, leftC, rightC, simpleShowZ1)

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
  Tuple s v -> Tuple s $ Tuple mempty (length s) :< v

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
testPatchSameR = uncurry patch (map forget testTypeLC') (fst testTypeC)

testPatchSameL :: Tuple String ATypeVC
testPatchSameL = uncurry patch (map forget $ extract1C' leftC (snd testTypeC)) (fst testTypeC)

testPatchExplodeR :: Tuple String ATypeVC
testPatchExplodeR = patch (fst testTypeLC') otherTest (fst testTypeC)

testPatchExplodeL :: Tuple String ATypeVC
testPatchExplodeL = patch (fst $ extract1C' leftC (snd testTypeC)) otherTest (fst testTypeC)

main :: Eff ( console :: CONSOLE ) Unit
main = do
  let showy = bitraverse logShow (cofrecurse >>> log) >>> void
  log testTypeLS
  logShow (head (snd testTypeC))
  log "----------"
  log testTypeCS
  log "---------- SameR"
  showy testPatchSameR
  log "---------- SameL"
  showy testPatchSameL
  log "---------- ExplodeR"
  showy testPatchExplodeR
  log "---------- ExplodeL"
  showy testPatchExplodeL
  log "---------- "
  log testTypeLSC
  log (showModuleData thisModule)
  -- log (simpleShowZRec (downF))
