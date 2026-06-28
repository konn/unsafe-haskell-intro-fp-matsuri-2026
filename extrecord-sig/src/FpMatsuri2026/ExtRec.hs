{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module FpMatsuri2026.ExtRec (
  Record,
  empty,
  fieldL,
  type (∈) (..),
  hGetField,
  type (∉),
  insert,
  mapRecord,
) where

import Control.Lens (Lens', lens)
import Data.DList (DList)
import Data.DList qualified as DL
import Data.Foldable (fold)
import Data.Functor.Product (Product (..))
import Data.Kind
import Data.List (intersperse)
import Data.Monoid (Endo (..))
import Data.Proxy (Proxy (..))
import FpMatsuri2026.HList
import FpMatsuri2026.TypeOps
import GHC.Base (Proxy#, proxy#)
import GHC.Generics (Generic)
import GHC.Records
import GHC.TypeLits

type Field :: (Symbol -> k -> Type) -> (Symbol, k) -> Type
newtype Field f kv = MkField (f (Fst kv) (Snd kv))
  deriving (Generic)

deriving newtype instance (Show (f k a)) => Show (Field f '(k, a))

deriving newtype instance (Eq (f k a)) => Eq (Field f '(k, a))

deriving newtype instance (Ord (f k a)) => Ord (Field f '(k, a))

type Record :: (Symbol -> k -> Type) -> [(Symbol, k)] -> Type
newtype Record f fs = MkRecord (HList (Field f) fs)

type (∈) :: Symbol -> [(Symbol, v)] -> Constraint
class (Member '(l, Lookup' l fs) fs) => l ∈ fs where
  hGetField' :: Proxy# l -> Record f fs -> f l (Lookup' l fs)
  hGetField' _ (MkRecord xs) = case hLookup @'(l, Lookup' l fs) xs of
    MkField v -> v

instance (Member '(l, Lookup' l fs) fs) => l ∈ fs

infix 4 ∈

hGetField :: forall l -> (l ∈ fs) => Record f fs -> f l (Lookup' l fs)
hGetField l = hGetField' (proxy# @l)

instance
  (l ∈ fs, v ~ f l (Lookup' l fs)) =>
  HasField l (Record f fs) v
  where
  getField = hGetField l
  {-# INLINE getField #-}

fieldL ::
  forall f fs.
  forall (l :: Symbol) ->
  (l ∈ fs) =>
  Lens' (Record f fs) (f l (Lookup' l fs))
fieldL l =
  lens
    (hGetField l)
    (\(MkRecord xs) v -> MkRecord (hReplace @'(l, Lookup' l fs) (MkField v) xs))

type (∉) :: Symbol -> [(Symbol, v)] -> Constraint
type k ∉ kvs = Lookup k kvs ~ 'Nothing

insert ::
  forall f v fs.
  forall l ->
  (l ∉ fs) =>
  f l v ->
  Record f fs ->
  Record f ('(l, v) ': fs)
insert _ fv (MkRecord fs) = MkRecord $ MkField fv <| fs

type ShowableField :: (Symbol -> k -> Type) -> (Symbol, k) -> Constraint
class (KnownSymbol (Fst kv), Show (f (Fst kv) (Snd kv))) => ShowableField f kv

instance (KnownSymbol k, Show (f k v)) => ShowableField f '(k, v)

instance (All (ShowableField f) kvs) => Show (Record f kvs) where
  showsPrec _ (MkRecord fs) =
    showString "MkRecord {"
      . appEndo
        ( fold $
            intersperse (Endo $ showString ", ") $
              DL.toList $
                hfoldMap showsField $
                  hzipWith Pair (allDict @_ @(ShowableField f) @kvs) fs
        )
      . showChar '}'
    where
      showsField ::
        forall kv.
        Product (Dict1 (ShowableField f)) (Field f) kv ->
        DList (Endo String)
      showsField (Pair Dict1 (MkField v)) =
        let k = symbolVal (Proxy @(Fst kv))
         in DL.singleton $ Endo $ showString k . showString " = " . shows v

empty :: Record f '[]
empty = MkRecord hnil

mapRecord :: forall f g fs. (forall v. forall (l :: Symbol) -> f l v -> g l v) -> Record f fs -> Record g fs
mapRecord f (MkRecord fs) = MkRecord $ hmap f' fs
  where
    f' :: forall kv. Field f kv -> Field g kv
    f' (MkField v) = MkField (f (Fst kv) v)

class (c (Fst kv) (Snd kv)) => OverKV c kv

instance (c k v) => OverKV c '(k, v)

elimAll ::
  forall c fs r.
  forall l ->
  (All (OverKV c) fs, l ∈ fs) =>
  Proxy fs ->
  ((c l (Lookup' l fs)) => r) ->
  r
elimAll l _ k =
  withDict1
    (hLookup @'(l, Lookup' l fs) (allDict @_ @(OverKV c) @fs))
    k
