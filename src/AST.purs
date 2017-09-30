module Component.AST where

import Prelude

import Annot (Annot(..), mayNeedAppParen, mayNeedFnParen)
import Combinators (aTypeApp, aTypeFunction, aTypeName, chainr)
import Control.Comonad (extract)
import Control.Comonad.Env (EnvT(..))
import Control.Monad.Aff (Aff)
import Control.Monad.Eff.Console (log)
import Control.Monad.Eff.Unsafe (unsafeCoerceEff)
import DOM (DOM)
import DOM.Event.KeyboardEvent (key)
import DOM.Event.Types (KeyboardEvent)
import Data.Const (Const(..))
import Data.Either (Either(..))
import Data.Foldable (fold)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Mu (Mu, roll, unroll)
import Data.Functor.Product (Product(..))
import Data.Functor.Variant as VF
import Data.Lazy (force)
import Data.Lens (Lens', modifying, (.~), (^.))
import Data.Lens.Record (prop)
import Data.List.Lazy (nil, uncons, (:))
import Data.Maybe (Maybe(..), fromMaybe, fromMaybe', isNothing, maybe, maybe')
import Data.Newtype (over, un, unwrap, wrap)
import Data.NonEmpty ((:|))
import Data.Pair (Pair(..))
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..), fst)
import Data.Variant (Variant)
import Data.Variant as V
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Lens as HL
import Halogen.HTML.Lens.Button as HL.Button
import Halogen.HTML.Lens.Checkbox as HL.Checkbox
import Halogen.HTML.Lens.Input as HL.Input
import Halogen.HTML.Properties as HP
import Matryoshka (class Recursive, cata, embed)
import Recursion (rewrap, whileAnnotatingDown)
import Reprinting (ATypeVC)
import Types (ATypeV, ATypeVF, Proper(Proper), Qualified(..), _app, _function, _name, _var)
import Unsafe.Coerce (unsafeCoerce)
import Zippers (DF, ParentCtx, ParentCtxs, ZRec, _focusRec, downF, downIntoRec, downRec, fromDF, fromParentCtx, liftDF, tipRec, toDF, toParentCtx, topRec, upF, upRec, (:<-:), (:<<~:))

data Query a
 = Lensy (HL.Query State a)
 | KeyPress KeyboardEvent a

type Element p = H.HTML p Query

type ATypeVMF = Compose Maybe ATypeVF
type ATypeVM = Mu ATypeVMF

atnunqp :: String -> ATypeV
atnunqp = aTypeName <<< Unqualified <<< Proper

testType :: ATypeV
testType = chainr aTypeFunction (Unqualified <<< Proper <$> "Module" :| ["Imports", "ImportModule"])
  `aTypeFunction` atnunqp "IO" `aTypeApp` ((atnunqp "Map" `aTypeApp` (atnunqp "Maybe" `aTypeApp` atnunqp "Module"))
    `aTypeApp` (atnunqp "Proper" `aTypeFunction` atnunqp "AKindV"))

type State =
  { typ :: ZRec ATypeVM
  , imput :: String
  , unicode :: Boolean
  }

_typ :: Lens' State (ZRec ATypeVM)
_typ = prop (SProxy :: SProxy "typ")

hole :: ATypeVM
hole = roll $ Compose Nothing

node :: ATypeVF ATypeVM -> ATypeVM
node = roll <<< Compose <<< Just

leftIsh :: ATypeVF ~> Maybe
leftIsh = VF.match
  { function: \(Pair l _) -> Just l
  , app: \(Pair l _) -> Just l
  , name: const Nothing
  , var: const Nothing
  }
leftIsm :: ATypeVMF ~> Maybe
leftIsm = un Compose >=> leftIsh
rightIsh :: ATypeVF ~> Maybe
rightIsh = VF.match
  { function: \(Pair _ r) -> Just r
  , app: \(Pair _ r) -> Just r
  , name: const Nothing
  , var: const Nothing
  }
rightIsm :: ATypeVMF ~> Maybe
rightIsm = un Compose >=> rightIsh
leftIng :: ZRec ATypeV -> ZRec ATypeV
leftIng = downIntoRec leftIsh
leftInc :: ZRec ATypeVC -> ZRec ATypeVC
leftInc = downIntoRec (un EnvT >>> extract >>> leftIsh)
leftImg :: ZRec ATypeVM -> ZRec ATypeVM
leftImg = downIntoRec leftIsm

navFirst :: ZRec ATypeVM -> ZRec ATypeVM
navFirst z = maybe z navFirst $ leftIsm (downRec z)

navLast :: ZRec ATypeVM -> ZRec ATypeVM
navLast z = maybe z navLast $ rightIsm (downRec z)

navUp :: ZRec ATypeVM -> ZRec ATypeVM
navUp z = case upRec z of
  Left _ -> z
  Right z' -> z'

navDown :: ZRec ATypeVM -> ZRec ATypeVM
navDown = downIntoRec (un Compose >=> m)
  where
    m :: ATypeVF ~> Maybe
    m = VF.match
      { function: \(Pair _ r) -> Just r
      , app: \(Pair l _) -> Just l
      , name: const Nothing
      , var: const Nothing
      }

navLeft :: ZRec ATypeVM -> ZRec ATypeVM
navLeft zipper = leftIsm (downRec zipper) #
    maybe' (\_ -> orGetParent zipper) navLast
  where
    orGetParent z@(cxs :<<~: focus) =
      case uncons cxs of
        Nothing -> zipper
        Just { head, tail } ->
          let
            isRight = VF.match
              { function: \(Tuple r _) -> r
              , app: \(Tuple r _) -> r
              , name: absurd <<< unwrap
              , var: absurd <<< unwrap
              }
          in if isRight $ extract $ un Product $ fromDF $ fromParentCtx head
            then navUp z
            else orGetParent (navUp z)

navRight :: ZRec ATypeVM -> ZRec ATypeVM
navRight zipper = rightIsm (downRec zipper) #
    maybe' (\_ -> orGetParent zipper) navFirst
  where
    orGetParent z@(cxs :<<~: focus) =
      case uncons cxs of
        Nothing -> zipper
        Just { head, tail } ->
          let
            isLeft = VF.match
              { function: \(Tuple r _) -> not r
              , app: \(Tuple r _) -> not r
              , name: absurd <<< unwrap
              , var: absurd <<< unwrap
              }
          in if isLeft $ extract $ un Product $ fromDF $ fromParentCtx head
            then navUp z
            else orGetParent (navUp z)

component :: forall eff. H.Component HH.HTML Query Unit Void (Aff (dom :: DOM | eff))
component =
  H.component
    { initialState: const initialState
    , render
    , eval
    , receiver: const Nothing
    }
  where

  initialState :: State
  initialState =
    { typ: leftImg $ tipRec $ cata (embed <<< Compose <<< Just) testType
    , imput: "Type here"
    , unicode: true
    }

  render :: State -> H.ComponentHTML Query
  render state@{ typ } =
    HH.div
      [ HE.onKeyUp (HE.input KeyPress)
      , HP.tabIndex 0
      ]
      [ HH.h1_ [ HH.text "AST Edit PureScript Type" ]
      , Lensy <$> HL.Checkbox.renderAsField "Use unicode" (prop (SProxy :: SProxy "unicode")) state
      , HH.h2_ [ HH.text "Inline zipper:" ]
      , renderZipper typ
      , HH.h2_ [ addEvent (leftImg typ) "Focus:" ]
      , renderFocus typ
      , HH.h2_ [ HH.text "Complete:" ]
      , renderFocus (nil :<<~: topRec typ)
      , HH.div_ -- editing
        [ Lensy <$> HL.Button.renderAsField "Hole" (_typ <<< _focusRec .~ hole) false
        , HH.br_
        , Lensy <$> HL.Input.renderAsField "Name" (prop (SProxy :: SProxy "imput")) state
        , Lensy <$> HL.Button.renderAsField "Name" (\s@{imput, typ:(cxs :<<~: _)} -> (_typ .~ (cxs :<<~: node (unsafeName Unqualified imput))) s) false
        , HH.div_ functions
        , HH.div_ apps
        ]
      , HH.div_
        [ Lensy <$> HL.Button.renderAsField "Left" (_typ navLeft) false
        , Lensy <$> HL.Button.renderAsField "Right" (_typ navRight) false
        , Lensy <$> HL.Button.renderAsField "Up" (_typ navUp) false
        , Lensy <$> HL.Button.renderAsField "Down" (_typ navDown) false
        ]
      ]
      where
        unsafeName q name = VF.inj _name $ Const $ q $ Proper name
        branching :: (DF Pair ~> DF ATypeVF) -> Boolean -> ATypeVM -> ParentCtx ATypeVM
        branching inj side other =
          toParentCtx $ toDF $
            Product $ Tuple (Compose (Const unit)) $
              fromDF $ inj $ toDF $
                Tuple side other
        function side = _typ \(cxs :<<~: f) ->
          branching (liftDF $ VF.inj _function) side f : cxs :<<~: hole
        app side = _typ \(cxs :<<~: f) ->
          branching (liftDF $ VF.inj _app) side f : cxs :<<~: hole
        functions = map Lensy <$> if isNothing (unwrap (unroll (typ ^. _focusRec)))
          then
            [ HL.Button.renderAsField "Function" (function false) false
            ]
          else
            [ HL.Button.renderAsField "As argument to function" (function true) false
            , HL.Button.renderAsField "As result of function" (function false) false
            ]
        apps = map Lensy <$> if isNothing (unwrap (unroll (typ ^. _focusRec)))
          then
            [ HL.Button.renderAsField "Apply" (app false) false
            ]
          else
            [ HL.Button.renderAsField "As function to apply" (app true) false
            , HL.Button.renderAsField "As argument to apply" (app false) false
            ]


  eval :: Query ~> H.ComponentDSL State Query Void (Aff (dom :: DOM | eff))
  eval (Lensy q) = HL.eval q
  eval (KeyPress e a) = a <$ do
    H.liftEff $ unsafeCoerceEff $ log $ unsafeCoerce e
    modifying _typ case key e of
      "ArrowUp" -> navUp
      "ArrowDown" -> navDown
      "ArrowLeft" -> navLeft
      "ArrowRight" -> navRight
      _ -> id

renderZipper :: forall p. ZRec ATypeVM -> Element p
renderZipper zipper =
  go zipper $
    HH.span [HP.class_ $ wrap "focus"]
      [renderFocus zipper]
  where
    go z@(cx :<<~: f) child = case uncons cx of
      Nothing -> child
      Just { head, tail } ->
        let
          here = pure (fromParentCtx head) :<-: f
          upped = upF here
          next = tail :<<~: roll upped
          circum = downF upped
          pos :: forall a. DF ATypeVMF a -> Variant (function :: Boolean, app :: Boolean)
          pos = VF.match
            { function: V.inj _function <<< fst
            , app: V.inj _app <<< fst
            , name: absurd <<< unwrap
            , var: absurd <<< unwrap
            } <<< extract <<< unwrap <<< fromDF
          posHere = pos $ fromParentCtx head
          isHere cx1 = pos cx1 == posHere
          renderChild (cx1 :<-: f1) =
            let hic = force cx1
            in if isHere hic
              then child
              else renderFocus (toParentCtx hic : tail :<<~: f1)
        in go next $
          render1 HH.span_ (addEvent next) (getAnnFromParents tail) $
            circum <#> renderChild

addEvent :: forall p. ZRec ATypeVM -> String -> Element p
addEvent z = HH.span
  [ HE.onClick (HE.input_ $ Lensy <<< HL.UpdateState (pure $ _typ .~ z))
  , HP.class_ $ wrap "clickable"
  , HP.title $ renderStr $ z ^. _focusRec
  ] <<< pure <<< HH.text

renderFocus :: forall p. ZRec ATypeVM -> Element p
renderFocus z@(cxs :<<~: focus) =
  let ann = getAnnForZipper z
  in render1 HH.span_ (addEvent z) ann $
    downF (unroll focus) <#>
      \(cx :<-: f) ->
        let pcx = toParentCtx (force cx)
        in renderFocus (pcx : cxs :<<~: f)

getAnnForZipper :: forall a. ZRec ATypeVM -> Maybe Annot
getAnnForZipper (cxs :<<~: _) = getAnnFromParents cxs

getAnnFromParents :: ParentCtxs ATypeVM -> Maybe Annot
getAnnFromParents cxs = uncons cxs <#>
  _.head >>> fromParentCtx >>> getAnnFromParent

getAnnFromParent :: forall a. DF ATypeVMF a -> Annot
getAnnFromParent = VF.match
  { function:
      fst >>> if _ then None else FnParen
  , app:
      fst >>> if _ then FnAppParen else FnParen
  , name: absurd <<< unwrap
  , var: absurd <<< unwrap
  } <<< extract <<< unwrap <<< fromDF

annotPrec :: forall a. ATypeVMF a -> ATypeVMF (Tuple Annot a)
annotPrec = over Compose $ map $ VF.match
  { name: VF.inj _name <<< rewrap
  , var: VF.inj _var <<< rewrap
  , function: VF.inj _function <<< bimapPair (Tuple FnParen) (Tuple None)
  , app: VF.inj _app <<< bimapPair (Tuple FnParen) (Tuple FnAppParen)
  } where bimapPair f g (Pair a b) = Pair (f a) (g b)

render1 :: forall e. (Array e -> e) -> (String -> e) -> Maybe Annot -> ATypeVMF e -> e
render1 arr w ann = unwrap >>> case _ of
  Nothing -> w "_"
  Just one -> one # VF.match
    { name: unwrap >>> show >>> w
    , var: unwrap >>> show >>> w
    , function: \(Pair l r) -> arr $
        wrapIf ann w mayNeedFnParen
          [ l, w " → ", r ]
    , app: \(Pair l r) -> arr $
        wrapIf ann w mayNeedAppParen
          [ l, w " · ", r ]
    }

render1Str :: Maybe Annot -> ATypeVMF String -> String
render1Str = render1 fold id
renderStr :: forall t. Recursive t ATypeVMF => t -> String
renderStr = whileAnnotatingDown Nothing annotPrec render1Str

wrapIf :: forall ann e. ann -> (String -> e) -> (ann -> Boolean) -> Array e -> Array e
wrapIf ann w f cs = if f ann then ([w "("] <> cs <> [w ")"]) else cs
