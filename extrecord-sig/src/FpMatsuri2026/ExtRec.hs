{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
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
  hmap,
  hmapC,
  hzipWith,
  hzipWith3,
  hfoldMap,
  htraverse_,
  htraverse,
) where

import Control.Lens (Lens', lens)
import Data.Coerce (coerce)
import Data.DList (DList)
import Data.DList qualified as DL
import Data.Foldable (fold)
import Data.Functor.Product (Product (..))
import Data.Kind
import Data.List (intersperse)
import Data.Monoid (Endo (..))
import Data.Proxy (Proxy (..))
import FpMatsuri2026.HList (
  All (..),
  HList,
  Member (..),
  hLookup,
  hReplace,
  hnil,
  (<|),
 )
import FpMatsuri2026.HList qualified as HL
import FpMatsuri2026.TypeOps
import GHC.Base (Proxy#, proxy#)
import GHC.Generics (Generic)
import GHC.Records
import GHC.TypeLits
import Prelude hiding (foldMap, map)

type Field :: (Symbol -> k -> Type) -> (Symbol, k) -> Type
newtype Field f kv = MkField {unField :: f (Fst kv) (Snd kv)}
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
                HL.hfoldMap showsField $
                  HL.hzipWith Pair (allDict @(ShowableField f) @kvs) fs
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

type OverKV :: (a -> b -> Constraint) -> (a, b) -> Constraint
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
    (hLookup @'(l, Lookup' l fs) (allDict @(OverKV c) @fs))
    k

hmap ::
  forall f g fs.
  (forall l v. f l v -> g l v) ->
  Record f fs ->
  Record g fs
hmap f (MkRecord fs) =
  MkRecord $ HL.hmap (\(MkField v :: Field f kv) -> MkField (f v)) fs

htraverse_ ::
  forall f m fs.
  (Applicative m) =>
  (forall l v. f l v -> m ()) ->
  Record f fs ->
  m ()
htraverse_ f (MkRecord fs) =
  HL.htraverse_ (\(MkField v :: Field f kv) -> f v) fs

htraverse ::
  forall f g m fs.
  (Applicative m) =>
  (forall l v. f l v -> m (g l v)) ->
  Record f fs ->
  m (Record g fs)
htraverse f (MkRecord fs) =
  MkRecord
    <$> HL.htraverse
      (\(MkField v :: Field f kv) -> MkField <$> f v)
      fs

hfoldMap ::
  forall f m fs.
  (Monoid m) =>
  (forall l v. f l v -> m) ->
  Record f fs ->
  m
hfoldMap f (MkRecord fs) =
  HL.hfoldMap (\(MkField v :: Field f kv) -> f v) fs

hzipWith ::
  forall f g h fs.
  (forall l v. f l v -> g l v -> h l v) ->
  Record f fs ->
  Record g fs ->
  Record h fs
hzipWith f (MkRecord fs) (MkRecord gs) =
  MkRecord $
    HL.hzipWith
      (\(MkField v :: Field f kv) (MkField w :: Field g kv) -> MkField (f v w))
      fs
      gs

hzipWith3 ::
  forall f g h i fs.
  (forall l v. f l v -> g l v -> h l v -> i l v) ->
  Record f fs ->
  Record g fs ->
  Record h fs ->
  Record i fs
hzipWith3 f (MkRecord fs) (MkRecord gs) (MkRecord hs) =
  MkRecord $
    HL.hzipWith3
      (\(MkField v :: Field f kv) (MkField w :: Field g kv) (MkField x :: Field h kv) -> MkField (f v w x))
      fs
      gs
      hs

hmapC ::
  forall f g fs.
  forall c ->
  (All (OverKV c) fs) =>
  (forall l v. (c l v) => f l v -> g l v) ->
  Record f fs ->
  Record g fs
hmapC c f =
  MkRecord
    . HL.hzipWith
      (\Dict1 (MkField fv) -> MkField $ f fv)
      (allDict @(OverKV c) @fs)
    . coerce
