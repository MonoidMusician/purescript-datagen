module Test.Main where

import Combinators (aTypeApp, aTypeFunction, aTypeName, aTypeVar, alias, chainl, chainr, dataImport, dataModule, importAllFrom, importFrom, namedNewType, onlyType, qualify, typeAbsType)
import Control.Comonad.Cofree ((:<))
import Control.Comonad.Env (EnvT(..))
import Effect (Effect)
import Effect.Console (log, logShow)
import Data.Bitraversable (bitraverse)
import Data.Functor.Variant (match)
import Data.Lens (_2)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Monoid (mempty)
import Data.Newtype (un)
import Data.NonEmpty ((:|))
import Data.Pair (Pair(..))
import Data.Spliceable (length)
import Data.Tuple (Tuple(Tuple), fst, snd)
import Prelude (type (~>), Unit, append, const, discard, flip, pure, void, ($), (<#>), (<$>), (<<<), (>>>))
import Printing (cofrecurse)
import Reprinting (ATypeVC, patch, showModuleData, showTagged)
import Test.QuickCheck.Laws.Control (checkComonad, checkExtend)
import Type.Proxy (Proxy2(..))
import Types (ATypeV, Constructors(..), DataType(..), DataTypeDef(..), Ident(..), Import(..), ImportModule(..), Module(..), ModuleData, Op(..), Proper(..), Qualified(..), ATypeVF)
import Zippers (ZF, ZRec, downIntoRec, simpleShowZRec, tipRec, topRec)

type EmptyRow = ()

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
        SumType
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
        SumType
          [ Tuple (Proper "ImportModule")
            [ aTypeApp (atnunqp "Maybe") $ atnunqp "Imports"
            , chainl aTypeApp (Unqualified <<< Proper <$> "Map" :| ["Module", "Imports"])
            ]
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
{-
testTypeL :: Tuple (Maybe (ZipperVF ATypeV Unit)) ATypeV
testTypeL = extract1 left testType

testTypeLS :: String
testTypeLS = case testTypeL of
  Tuple (Just z) h ->
    "(" <> simpleShowZ1 showAType z <> ", " <> showAType h <> ")"
  Tuple Nothing h -> showAType h
-}
testTypeC :: Tuple String ATypeVC
testTypeC = case showTagged testType of
  Tuple s v -> Tuple s $ Tuple mempty (length s) :< v

testTypeShown :: String
testTypeShown = fst testTypeC

testTypeCS :: String
testTypeCS = cofrecurse (snd testTypeC)

testPatchExplodeL :: Tuple String (ZRec ATypeVC)
testPatchExplodeL = patch (_2 (leftInc <<< tipRec) testTypeC) otherTest

leftIsh :: ATypeVF ~> Maybe
leftIsh = match
  { fun: \(Pair l _) -> Just l
  , app: \(Pair l _) -> Just l
  , name: const Nothing
  , var: const Nothing
  }
leftIng :: ZRec ATypeV -> ZRec ATypeV
leftIng = downIntoRec leftIsh
leftInc :: ZRec ATypeVC -> ZRec ATypeVC
leftInc = downIntoRec (un EnvT >>> snd >>> leftIsh)

main :: Effect Unit
main = do
  let showz = bitraverse logShow (topRec >>> cofrecurse >>> log) >>> void
  let testPath path = showz <<< patch (_2 (path <<< tipRec) testTypeC)
  testPath leftInc otherTest
  testPath (leftInc <<< leftInc) testType
  log (showModuleData thisModule)
  log $ simpleShowZRec $ leftIng $ leftIng $ tipRec testType
  log "\nTesting comonads"
  checkExtend (Proxy2 :: Proxy2 (ZF Pair))
  checkComonad (Proxy2 :: Proxy2 (ZF Pair))
