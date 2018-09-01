module HoTT where

import Prelude

import Control.Apply (lift2)
import Control.Bind (bindFlipped)
import Data.Bifunctor (bimap, lmap)
import Data.Const (Const(..))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (un, unwrap, wrap)
import Data.NonEmpty ((:|))
import Data.Profunctor (dimap)
import Data.Symbol (SProxy(..))
import Data.Traversable (sequence)
import Data.Tuple (Tuple(..), fst)
import Data.Variant (Variant)
import Data.Variant as Variant
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Exception.Unsafe (unsafeThrow)
import Halogen as H
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.Component.Profunctor (ProComponent(..))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.Pager (renderPage)
import Halogen.Query.Input as Input
import Halogen.VDom.DOM.Prop as Prop
import Halogen.VDom.Driver (runUI)
import HoTT.Render.Syntax as RS
import HoTT.Types (BinderInfo(..), Expr)
import HoTT.Types as Expr
import HoTT.Types.Level as Level
import HoTT.Types.Name as Name

mapMaybeProp :: forall a b. (a -> Maybe b) -> Prop.Prop a -> Prop.Prop b
mapMaybeProp f (Prop.Handler ty g) = Prop.Handler ty (bindFlipped f <$> g)
mapMaybeProp f (Prop.Ref g) = Prop.Ref (bindFlipped f <$> g)
mapMaybeProp _ (Prop.Attribute ns attr val) = Prop.Attribute ns attr val
mapMaybeProp _ (Prop.Property prop val) = Prop.Property prop val

mapMaybeHTML :: forall p a b. (a -> Maybe b) -> HH.HTML p a -> HH.HTML p b
mapMaybeHTML f = unwrap >>> lmap (map (mapMaybeProp g)) >>> wrap where
  g (Input.RefUpdate lbl el) = Just (Input.RefUpdate lbl el)
  g (Input.Action a) = Input.Action <$> f a

noSlots :: forall m act. H.ComponentSlot HH.HTML () m act -> Void
noSlots _ = unsafeThrow "There should be no components in a place with no slots"

silenceHTML :: forall b p a. HH.HTML p a -> HH.HTML p b
silenceHTML = mapMaybeHTML (const Nothing)

sampleExpr :: Expr
sampleExpr =
  let
    _anon = Name.fromString "_"
    _n = Name.fromString "n"
    _ty = Name.fromString "ty"
    _el = Name.fromString "el"
    vocate nominal = Expr.Const nominal []
    nominate = vocate <<< Name.fromString
    _nat = nominate "nat"
    _vec ty = Expr.apps $ nominate "vec" :| [vocate _n, ty]
    _body ty el = Expr.apps $ nominate "rec_on" :| [vocate _n, nominate "nil", Expr.App (nominate "cons") el]
  in
  Expr.Elet (Name.fromString "zeros")
    (Expr.Pi _n Expr.Default _nat (_vec _nat))
    (Expr.Lam _n Expr.Default _nat (_body _nat (nominate "zero"))) $
  Expr.Elet (Name.fromString "fill")
    (Expr.Pi _ty Expr.Implicit (Expr.Sort (Level.Succ Level.Zero)) $
      Expr.Pi _n Expr.Default _nat $
        Expr.Pi _anon Expr.Default (vocate _ty) $
          _vec $ vocate _ty
    )
    (Expr.Lam _ty Expr.StrictImplicit (Expr.Sort (Level.Succ Level.Zero)) $
      Expr.Lam _n Expr.Default _nat $
        Expr.Lam _el Expr.Default (vocate _ty) $
          _body (vocate _ty) (vocate _el)
    ) $
  nominate "tt"

sampleString :: String
sampleString = Expr.runPretty (Expr.ppExpr sampleExpr 0) Expr.plainPrinter

sampleHTML :: RS.M (RS.HTML RS.Message)
sampleHTML = do
  _vector_ty <- RS.arrow (pure $ HH.text "Type") $ RS.arrow (pure $ HH.text "ℕ") (pure $ HH.text "Type")
  let
    _vector = RS.Global
      { name: Name.fromString "vector"
      , pp_name: Name.fromString "vector"
      , provenance: RS.URL
        "https://github.com/leanprover/lean/blob/v3.4.1/library/data/vector.lean#L14"
      , ty: pure _vector_ty
      }
    _nat = RS.Global
      { name: Name.fromString "nat"
      , pp_name: Name.fromString "ℕ"
      , provenance: RS.URL
        "https://github.com/leanprover/lean/blob/v3.4.1/library/init/core.lean#L293"
      , ty: pure $ HH.text "Type"
      }
  RS.pi { binder: StrictImplicit, name: "α", ty: pure $ pure $ HH.text "Type" } $
  RS.arrow (RS.bindingAt 0) $
  RS.pi { binder: Default, name: "n", ty: pure $ RS.binding _nat } $
  RS.app (RS.app (RS.binding _vector) (RS.bindingAt 1)) (RS.bindingAt 0)


type StaticSlot = H.Slot Silent (Variant Pages) Unit
type FancySlot = H.Slot Silent Fancy Unit
type Slots =
  ( intro :: StaticSlot
  , functions :: FancySlot
  )
type StaticPage = Tuple Unit Unit
type Pages =
  ( intro :: StaticPage
  , functions :: StaticPage
  )
type State =
  { page :: Variant Pages
  , highlighting_local :: Maybe Int
  }
data Query a
  = ToPage a (Variant Pages)
  | HighlightLocal a (Maybe Int)

data StaticQuery i o a
  = In a i
  | Out a o

type Silent = Const Void
fromFn :: forall p i m. (i -> HH.HTML Void p) ->
  H.Component HH.HTML Silent i p m
fromFn visor = H.mkComponent
  { initialState: identity
  , render: bimap absurd identity <<< visor
  , eval: case _ of
    (H.Initialize a) -> pure a
    (H.Finalize a) -> pure a
    (H.Receive i a) -> a <$ H.put i
    (H.Handle o a) -> a <$ H.raise o
    (H.Request l) -> un Const l # absurd
  }

staticPage :: (State -> HH.HTML Void (Variant Pages)) ->
  Tuple
    (H.Component HH.HTML
      Silent
      (Tuple State Unit)
      (Variant Pages)
      Aff
    )
    (Variant Pages -> Maybe (Query Unit))
staticPage visor = Tuple (fromFn (fst >>> visor)) (pure <<< ToPage unit)

type Fancy = Either (Variant Pages) RS.Message
fancyPage :: (State -> HH.HTML Void Fancy) ->
  Tuple
    (H.Component HH.HTML
      Silent
      (Tuple State Unit)
      Fancy
      Aff
    )
    (Fancy -> Maybe (Query Unit))
fancyPage visor = Tuple (fromFn (fst >>> visor)) (pure <<< adapt) where
  adapt (Left page) = ToPage unit page
  adapt (Right thingy) = Variant.case_ #
    Variant.on (SProxy :: SProxy "highlight_local") (HighlightLocal unit) $ thingy

uncurryComponent :: forall h q i i' o m. Functor q =>
  H.Component h q (Tuple i' i) o m -> i' -> H.Component h q i o m
uncurryComponent c i' = unwrap $ dimap (Tuple i') identity $ ProComponent c

component :: H.Component HH.HTML Query Unit Void Aff
component = H.component
  { eval
  , render
  , initialState: const { page: intro, highlighting_local: Nothing }
  , receiver: const Nothing
  , initializer: Nothing
  , finalizer: Nothing
  } where
    noLink = HP.href "javascript:void(0)"
    pageLink pg = HH.a [ noLink, HE.onClick (pure $ pure pg) ]
    intro = Variant.inj (SProxy :: SProxy "intro") mempty
    functions = Variant.inj (SProxy :: SProxy "functions") mempty
    pager :: Variant Pages -> State -> H.ComponentHTML Query Slots Aff
    pager = renderPage
      { intro: staticPage \st ->
          pageLink functions
            [ HH.text "About functions." ]
      , functions: fancyPage \st ->
          let
            para :: String -> RS.M (HH.HTML Void Fancy)
            para t = pure $ HH.p_ $ pure $ HH.text t
            adapt = map (bimap noSlots Right)
            r = RS.render
              { unicode: true
              , precedence: 0
              , highlighting_local: st.highlighting_local
              , elaborated: true
              }
          in HH.div_ $ r $ sequence
            [ para
              "Functions are the most fundamental ingredient in dependent type theory, and they are particularly complex in HoTT. There is a colloquial (and sensible) distinction between “dependently-typed functions” (also known as “Pi types”) and regular functions (whose type is denoted with an arrow)."
            , para
              "Pi types introduce an argument of a certain type and have a return type, which may depend on the value of that argument."
            , para "Basic syntax:"
            -- Π(var : ?input_type), ?return_type[var]
            , adapt do
                let input_type = pure $ pure $ HH.span [ HP.title "A metavariable, to be filled in with a real term" ] [ HH.text "?input_type" ]
                RS.pi { binder: Default, name: "var", ty: input_type } do
                  varH <- RS.bindingAt 0
                  pure $ HH.span
                    [ HP.title "A metavariable, to be filled in with a real term, it may depend on the value of var" ]
                    [ HH.text "?return_type", HH.text "[", varH, HH.text "]" ]
            , para "Many variables can be specified in the same binder as long as they have the same type. Many binders may be specified before the comma, separated by spaced. Brackets denote different kinds of binders. Variables specified may appear in the following binders, and more generally, the bodies of the pi types."
            , para "Example(s):"
            , adapt $ sampleHTML >>= \sample -> do
                _vector_ty <- RS.arrow (pure $ HH.text "Type") $ RS.arrow (pure $ HH.text "ℕ") (pure $ HH.text "Type")
                let
                  _vector = RS.Global
                    { name: Name.fromString "vector"
                    , pp_name: Name.fromString "vector"
                    , provenance: RS.URL
                      "https://github.com/leanprover/lean/blob/v3.4.1/library/data/vector.lean#L14"
                    , ty: pure _vector_ty
                    }
                  _nat = RS.Global
                    { name: Name.fromString "nat"
                    , pp_name: Name.fromString "ℕ"
                    , provenance: RS.URL
                      "https://github.com/leanprover/lean/blob/v3.4.1/library/init/core.lean#L293"
                    , ty: pure $ HH.text "Type"
                    }
                let space = HH.text " "
                zeroH <- lift2 (*>) RS.addBinding RS.binding $ RS.Global
                  { name: Name.fromString "fill"
                  , pp_name: Name.fromString "fill"
                  , provenance: RS.None
                  , ty: Just sample
                  }
                defH <- RS.syntax
                  { unicode: "def"
                  , ascii: "def"
                  , explanation: "Introduces a top-level definition in the current scope."
                  , role: RS.Keyword
                  }
                typeH <- RS.syntax
                  { unicode: ":"
                  , ascii: ":"
                  , explanation: "This asserts that the left side has the type described by the right side."
                  , role: RS.Separator
                  }
                assignH <- RS.syntax
                  { unicode: "≔"
                  , ascii: ":="
                  , explanation: "Definitional equality: this defines the left side as equal to the right side."
                  , role: RS.Separator
                  }
                lamH <- RS.lam'
                  [ { binder: StrictImplicit
                    , names: ["α"]
                    , ty: pure $ pure $ HH.text "Type"
                    , existing: Just 2
                    }
                  , { binder: Default
                    , names: ["a"]
                    , ty: pure $ RS.bindingAt 0
                    , existing: Nothing
                    }
                  , { binder: Default
                    , names: ["n"]
                    , ty: pure $ RS.binding _nat
                    , existing: Just 2
                    }
                  ] do
                    _n <- RS.bindingAt 0
                    _a <- RS.bindingAt 1
                    _α <- RS.bindingAt 2
                    atH <- RS.syntax
                      { unicode: "@"
                      , ascii: "@"
                      , explanation: "Makes implicit arguments explicit."
                      , role: RS.Operator
                      }
                    -- pure $ HH.text "@nat.rec_on (vector α) n (@vector.nil α) (λ n, @vector.cons α n a)"
                    -- pure $ HH.text "nat.rec_on n vector.nil (λ (m : ℕ), vector.cons a)"
                    RS.app (RS.app (RS.app (pure $ HH.text "nat.rec_on") (pure _n)) (pure $ HH.text "vector.nil")) $
                    RS.lam { binder: Default, name: "m", ty: pure $ RS.binding _nat } $
                    RS.app (pure $ HH.text "vector.cons") (pure _a)
                pure $ HH.ol_ $ HH.li_ <$>
                  [ [ zeroH, HH.text " ", typeH, HH.text " ", sample
                    , HH.p_ $ pure $ HH.text "This is a function that takes a type, a value of that type, and a natural number, and produces a vector of that type with the specified length. There is one unique function with that type; it can be implemented as follows:"
                    , defH, space, zeroH, space, typeH, space, sample, space, assignH, space, lamH
                    ]
                  ]
            , pure HH.br_
            , para "Introduction and elimination:"
            , para "Typing judgments:"
            , pure HH.br_
            , pure $ Left <$> pageLink intro [ HH.text "Back to beginning." ]
            ]
      }

    render :: State -> H.ComponentHTML Query Slots Aff
    render = pager <$> _.page <*> identity

    eval :: Query ~> H.HalogenM State Query Slots Void Aff
    eval (ToPage a p) = a <$ H.modify_ _ { page = p, highlighting_local = Nothing }
    eval (HighlightLocal a l) = a <$ H.modify_ _ { highlighting_local = l }

main :: Effect Unit
main = runHalogenAff do
  body <- awaitBody
  runUI component unit body
