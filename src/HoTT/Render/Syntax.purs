module HoTT.Render.Syntax where

import Prelude

import CSS (CSS, color)
import Color (Color)
import Color as Color
import Color.Scheme.MaterialDesign as Material
import Control.Extend (duplicate)
import Control.Monad.RWS (RWS, RWSResult(..), ask, runRWS)
import Control.Monad.Reader (ReaderT, class MonadReader, local)
import Control.Monad.State (class MonadState)
import Control.Plus (empty)
import Data.Foldable (length, foldMap)
import Data.Lens (Lens', Setter', use, view, (%=), (+=), (-=), (.=))
import Data.Lens.Record (prop)
import Data.List (List(..), intercalate, index)
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (for, sequence, traverse)
import Data.Tuple (Tuple(..))
import Data.Variant (SProxy(..), Variant)
import Data.Variant as Variant
import Effect.Aff (Aff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.CSS (style)
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import HoTT.Types (BinderInfo, binderParens)
import HoTT.Types.Name (Name)

data Binding
  = Local
    { id :: Int
    , name :: String
    , ty :: Maybe (HTML Message)
    }
  | Global
    { name :: Name
    , pp_name :: Name -- taking into account open namespaces &c.
    , provenance :: Provenance
    , ty :: Maybe (HTML Message)
    }

data Provenance
  = None
  | URL String

type Message = Variant
  ( highlight_local :: Maybe Int
  )
type MonadState =
  {
  }
type Slots =
  (
  )

type HTML o = H.ComponentHTML' o Slots (ReaderT MonadState Aff)

type R =
  { unicode :: Boolean
  , precedence :: Int
  , highlighting_local :: Maybe Int
  , elaborated :: Boolean
  }
type W =
  {
  }
type S =
  { fresh_ix :: Int
  , bindings :: List Binding
  }
type M = RWS R W S
type Renderer = M (HTML Message)

_fresh_id = prop (SProxy :: SProxy "fresh_ix") :: forall s. Lens' { fresh_ix :: Int | s } Int
_bindings = prop (SProxy :: SProxy "bindings") :: forall s. Lens' { bindings :: List Binding | s } (List Binding)
_precedence = prop (SProxy :: SProxy "precedence") :: forall r. Lens' { precedence :: Int | r } Int
_highlighting_local = prop (SProxy :: SProxy "highlighting_local") :: forall r. Lens' { highlighting_local :: Maybe Int | r } (Maybe Int)

with :: forall r t m a. MonadReader r m =>
  Setter' r t -> (t -> t) -> m a -> m a
with = compose local

withOf :: forall r t m a. MonadReader r m =>
  Setter' r t -> t -> m a -> m a
withOf l v = with l (const v)

scopedWith :: forall s t m a. MonadState s m =>
  Lens' s t -> m a -> m a
scopedWith l m = do
  t0 <- use l
  a <- m
  l .= t0
  pure a

scopedWithAs :: forall s t m a. MonadState s m =>
  Lens' s t -> t -> m a -> m a
scopedWithAs l t m = do
  t0 <- use l
  l .= t
  a <- m
  l .= t0
  pure a

fresh :: forall r w s. Monoid w => RWS r w { fresh_ix :: Int | s } Int
fresh = use _fresh_id <* (_fresh_id += 1)

rewind :: forall r w s. Monoid w => Int -> RWS r w { fresh_ix :: Int | s } Unit
rewind n = _fresh_id -= n

unicode :: forall r w s. Monoid w => RWS { unicode :: Boolean | r } w s Boolean
unicode = ask <#> _.unicode

addBinding :: forall r w s. Monoid w => Binding -> RWS r w { bindings :: List Binding | s } Unit
addBinding b = _bindings %= (Cons b)

addLocal :: forall r w s. Monoid w =>
  { name :: String
  , ty :: Maybe (HTML Message)
  , existing :: Maybe Int
  } ->
  RWS r w { fresh_ix :: Int, bindings :: List Binding | s } Binding
addLocal { name, ty, existing } = do
  id <- case existing of
    Nothing -> fresh
    Just i -> use _fresh_id <#> (_ - i)
  let b = Local { name, ty, id }
  b <$ addBinding b

render' :: forall a. R -> M a -> RWSResult S a W
render' r = runRWS <@> r <@> { fresh_ix: 0, bindings: mempty }

render :: forall a. R -> M a -> a
render = render' >>> map \(RWSResult _ html _) -> html

data Role
  = Keyword
  | Separator
  | Operator
  | Variable
  | Constant

roleColor :: Role -> Color
roleColor = case _ of
  Keyword -> Material.lime
  Separator -> Color.graytone 0.5
  Operator -> Material.green
  Variable -> Material.purple
  Constant -> Material.blue

roleAttr :: forall r i. Role -> HH.IProp ( style :: String | r ) i
roleAttr = style <<< roleStyle

roleStyle :: Role -> CSS
roleStyle role = do
  color (roleColor role)

syntax ::
  { unicode :: String
  , ascii :: String
  , explanation :: String
  , role :: Role
  } ->
  Renderer
syntax r@{ explanation: "" } = do
  u <- unicode
  pure $ HH.span [ roleAttr r.role ] $ pure $ HH.text $
    if u then r.unicode else r.ascii
syntax r = do
  u <- unicode
  pure $ HH.span [ roleAttr r.role, HP.title r.explanation ] $ pure $ HH.text $
    if u then r.unicode else r.ascii

parenPrec :: Int -> Renderer -> Renderer
parenPrec prec r = do
  p <- ask <#> view _precedence
  if p <= prec then r else
    r <#> \rH -> HH.span_ [ HH.text "(", rH, HH.text ")" ]

highlightLocal :: forall e. Int -> e -> Maybe Message
highlightLocal id = pure $ pure $
  Variant.inj (SProxy :: SProxy "highlight_local") $ pure id

dehighlight :: forall e. e -> Maybe Message
dehighlight = pure $ pure $
  Variant.inj (SProxy :: SProxy "highlight_local") empty

binding :: Binding -> Renderer
binding (Local { id, name, ty }) = do
  hl <- ask <#> view _highlighting_local
  let styl = if hl /= Just id then roleStyle Variable else color Material.red
  pure $ HH.span
    [ style styl
    , HE.onMouseOver $ highlightLocal id
    , HE.onMouseOut dehighlight
    ]
    [ HH.text name ]
binding (Global { name, pp_name }) =
  pure $ HH.span [ HP.title (show name), roleAttr Constant ] $ pure $ HH.text $ show pp_name

bindingAt :: Int -> Renderer
bindingAt i = do
  bs <- use _bindings
  let
    missing = pure $ HH.text $
      "Missing bound variable at index " <> show i <> ", there were " <>
      show (length bs :: Int) <> " variables in scope."

  maybe missing binding (index bs i)

app :: Renderer -> Renderer -> Renderer
app l r = parenPrec 1024 do
  lH <- withOf _precedence 1024 l
  sH <- syntax
    { unicode: "·"
    , ascii: " "
    , explanation: "Function application"
    , role: Operator
    }
  rH <- withOf _precedence 1023 r
  pure $ HH.span_ [ lH, sH, rH ]

fn :: Renderer -> Renderer -> Renderer
fn l r = do
  lH <- l
  aH <- syntax
    { unicode: "→"
    , ascii: "->"
    , explanation: "A function arrow, from the left type to the right type"
    , role: Operator
    }
  rH <- r
  pure $ HH.span_ [ lH, HH.text " ", aH, HH.text " ", rH ]

type Binder =
  { binder :: BinderInfo
  , ty :: Maybe Renderer
  , names :: Array String
  , existing :: Maybe Int
  }

binder' ::
  Boolean ->
  Binder ->
  Renderer
binder' with_space var = do
  let Tuple lS rS = binderParens var.binder
  let change { unicode: u, ascii, explanation } = { unicode: u, ascii, explanation, role: Separator }
  lH <- syntax $ change lS
  -- render the type first -- it does not have access to the new variables
  tHm <- sequence var.ty
  -- now add the bindings, with the rendered type
  bHs <- for var.names $
    { ty: tHm, name: _, existing: var.existing }
      >>> addLocal >=> binding
  let bHs' = intercalate [ HH.text " " ] $ duplicate bHs
  rH <- syntax $ change rS
  pure $ HH.span_ $
    (if with_space then [ HH.text " " ] else [])
    <> [ lH ] <> bHs'
    <> foldMap (\tH -> [ HH.text " : ", tH ]) tHm
    <> [ rH ]

binder :: Binder -> Renderer
binder = binder' false

binders :: Array Binder -> M (Array (HTML Message))
binders = traverse $ binder' true

pi' ::
  Array Binder ->
  Renderer ->
  Renderer
pi' [] body = body
pi' vars body = scopedWith _bindings do
  piH <- syntax
    { unicode: "Π"
    , ascii: "Pi"
    , explanation: "Pi: Introduces a dependent function type with binders and a body where the just bound variables are in scope."
    , role: Keyword
    }
  vHs <- binders vars
  bH <- body
  pure $ HH.span_ $
    [ piH ] <> vHs <> [ HH.text ", ", bH ]

pi ::
  { binder :: BinderInfo
  , name :: String
  , ty :: Maybe Renderer
  } ->
  Renderer -> Renderer
pi = pi' <<< pure <<< \{ name, binder: b, ty } ->
  { names: [name], binder: b, ty, existing: Nothing }

lam' ::
  Array Binder ->
  Renderer ->
  Renderer
lam' [] body = body
lam' vars body = scopedWith _bindings $ parenPrec 0 do
  lamH <- syntax
    { unicode: "λ"
    , ascii: "fun"
    , explanation: "Lambda: introduces an anonymous function with binders and a body where the just bound variables are in scope."
    , role: Keyword
    }
  vHs <- binders vars
  bH <- body
  pure $ HH.span_ $
    [ lamH ] <> vHs <> [ HH.text ", ", bH ]

lam ::
  { binder :: BinderInfo
  , name :: String
  , ty :: Maybe Renderer
  } ->
  Renderer -> Renderer
lam = lam' <<< pure <<< \{ name, binder: b, ty } ->
  { names: [name], binder: b, ty, existing: Nothing }
