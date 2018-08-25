module Externs.Codec where

import Prelude

import Data.Argonaut (Json)
import Data.Argonaut as A
import Data.Array (catMaybes, elem, mapMaybe)
import Data.Codec (decode)
import Data.Codec.Argonaut (JsonDecodeError(..), jarray)
import Data.Codec.Argonaut.Record (record)
import Data.Either (Either(..), hush, note)
import Data.Map (Map, fromFoldable, filterKeys)
import Foreign.Object as Foreign.Object
import Data.Traversable (sequence, traverse)
import Data.Tuple (Tuple(..))
import Data.Variant (Variant)
import Externs.Codec.AKind (codecAKindV)
import Externs.Codec.Names (codecProper)
import Types (AKindV, Proper)

type ExternsDeclaration = Variant
  -- | A type declaration
  ( "EDType" ::
      { edTypeName                :: Proper
      , edTypeKind                :: AKindV
      --, edTypeDeclarationKind     :: TypeKind
      }
  {-
  -- | A type synonym
  , "EDTypeSynonym" ::
      { edTypeSynonymName         :: Proper
      , edTypeSynonymArguments    :: Array (Tuple Ident (Maybe Kind))
      , edTypeSynonymType         :: ATypeV
      }
  -- | A data construtor
  , "EDDataConstructor" ::
      { edDataCtorName            :: Proper
      -- , edDataCtorOrigin          :: DataDeclType
      -- , edDataCtorTypeCtor        :: ProperName 'TypeName
      -- , edDataCtorType            :: Type
      -- , edDataCtorFields          :: [Ident]
      }
  -- | A value declaration
  , "EDValue" ::
      { edValueName               :: Ident
      , edValueType               :: Type
      }
  -- | A type class declaration
  , "EDClass" ::
      { edClassName               :: ProperName 'ClassName
      , edClassTypeArguments      :: [(Text, Maybe Kind)]
      , edClassMembers            :: [(Ident, Type)]
      , edClassConstraints        :: [Constraint]
      , edFunctionalDependencies  :: [FunctionalDependency]
      }
  -- | An instance declaration
  , "EDInstance" ::
      { edInstanceClassName       :: Qualified (ProperName 'ClassName)
      , edInstanceName            :: Ident
      , edInstanceTypes           :: [Type]
      , edInstanceConstraints     :: Maybe [Constraint]
      , edInstanceChain           :: [Qualified Ident]
      , edInstanceChainIndex      :: Integer
      }
  -- | A kind declaration
  , "EDKind" ::
      { edKindName                :: ProperName 'KindName
      }
  -}
  )


prop :: String -> Json -> Either JsonDecodeError Json
prop i = A.caseJsonObject (Left (TypeMismatch "Object"))
  (Foreign.Object.lookup i >>> note (AtKey i MissingValue))

extractTypes :: Array Json -> Either JsonDecodeError (Map Proper AKindV)
extractTypes = compose (map (fromFoldable <<< map conv <<< catMaybes)) <<< traverse $
  (A.toObject >=> Foreign.Object.lookup "EDType" >=> A.toObject >>> map
    (decode (record {edTypeName: codecProper, edTypeKind: codecAKindV}))) >>> sequence
  where
    conv {edTypeName, edTypeKind} = Tuple edTypeName edTypeKind

externsTypes :: Json -> Either JsonDecodeError (Map Proper AKindV)
externsTypes = prop "efDeclarations" >=> decode jarray >=> extractTypes

externsJustTypes :: Json -> Either JsonDecodeError (Map Proper AKindV)
externsJustTypes = prop "efDeclarations" >=> decode jarray >=> \o -> do
  types <- extractTypes o
  let classes = mapMaybe (compose hush $ prop "EDClass" >=> prop "edClassName" >=> decode codecProper) o
  let isClass t = t `elem` classes
  pure (filterKeys (not isClass) types)
