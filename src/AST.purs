module Component.AST where

import Prelude

import Annot (Annot(..), mayNeedAppParen, mayNeedFnParen)
import Combinators (aTypeApp, aTypeFunction, aTypeName, chainl)
import Control.Comonad (extract)
import Control.Comonad.Env (EnvT(..))
import Control.Monad.Aff (Aff)
import DOM (DOM)
import Data.Const (Const(..))
import Data.Foldable (fold)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Mu (Mu, roll, unroll)
import Data.Functor.Variant as VF
import Data.Lazy (force)
import Data.Lens (Lens', (.~), (^.))
import Data.Lens.Record (prop)
import Data.List.Lazy (nil, uncons, (:))
import Data.Maybe (Maybe(..), isNothing)
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
import Zippers (DF, ParentCtxs, ZRec, _focusRec, downF, downIntoRec, fromDF, fromParentCtx, tipRec, toParentCtx, topRec, upF, (:<-:), (:<<~:))

type Query = HL.Query State

type Element p = H.HTML p Query

type ATypeVMF = Compose Maybe ATypeVF
type ATypeVM = Mu ATypeVMF

atnunqp :: String -> ATypeV
atnunqp = aTypeName <<< Unqualified <<< Proper

testType :: ATypeV
testType = chainl aTypeFunction (Unqualified <<< Proper <$> "Module" :| ["Imports", "ImportModule"])
  `aTypeFunction` ((atnunqp "Map" `aTypeApp` (atnunqp "Maybe" `aTypeApp` atnunqp "Module"))
    `aTypeApp` (atnunqp "Meh" `aTypeFunction` atnunqp "Eh"))

type State =
  { typ :: ZRec ATypeVM
  , imput :: String
  , unicode :: Boolean
  }

_typ :: Lens' State (ZRec ATypeVM)
_typ = prop (SProxy :: SProxy "typ")

leftIsh :: ATypeVF ~> Maybe
leftIsh = VF.match
  { function: \(Pair l _) -> Just l
  , app: \(Pair l _) -> Just l
  , name: const Nothing
  , var: const Nothing
  }
leftIng :: ZRec ATypeV -> ZRec ATypeV
leftIng = downIntoRec leftIsh
leftInc :: ZRec ATypeVC -> ZRec ATypeVC
leftInc = downIntoRec (un EnvT >>> extract >>> leftIsh)
leftImg :: ZRec ATypeVM -> ZRec ATypeVM
leftImg = downIntoRec (un Compose >=> leftIsh)

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
    HH.div_
      [ HH.h1_ [ HH.text "AST Edit PureScript Type" ]
      , HL.Checkbox.renderAsField "Use unicode" (prop (SProxy :: SProxy "unicode")) state
      , HH.h2_ [ HH.text "Inline zipper:" ]
      , renderZipper typ
      , HH.h2_ [ addEvent (leftImg typ) "Focus:" ]
      , renderFocus typ
      , HH.h2_ [ HH.text "Complete:" ]
      , renderFocus (nil :<<~: topRec typ)
      , HH.div_ -- editing
        [ HL.Button.renderAsField "Hole" (_typ \(cxs :<<~: _) -> cxs :<<~: roll (Compose Nothing)) false
        , HH.br_
        , HL.Input.renderAsField "Name" (prop (SProxy :: SProxy "imput")) state
        , HL.Button.renderAsField "Name" (\s@{imput, typ:(cxs :<<~: _)} -> (_typ .~ (cxs :<<~: roll (Compose (Just (VF.inj _name (Const (Unqualified (Proper imput)))))))) s) false
        , HH.div_ functions
        ]
      ]
      where
        function = _typ \(cxs :<<~: f) -> cxs :<<~: roll (Compose (Just (VF.inj _function (Pair (roll (Compose Nothing)) f))))
        functionsSided =
          [ HL.Button.renderAsField "Function left" function false
          , flip (HL.Button.renderAsField "Function right") false $
            _typ \(cxs :<<~: f) -> cxs :<<~: roll (Compose (Just (VF.inj _function (Pair f (roll (Compose Nothing))))))
          ]
        functions = if isNothing (unwrap (unroll (typ ^. _focusRec)))
          then [HL.Button.renderAsField "Function" function false]
          else functionsSided


  eval :: Query ~> H.ComponentDSL State Query Void (Aff (dom :: DOM | eff))
  eval = HL.eval

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
  [ HE.onClick (HE.input_ $ HL.UpdateState (pure $ _typ .~ z))
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
