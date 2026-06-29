module FpMatsuri2026.HList.Unsafe.Core (
  HList (..),
  Member (..),
  (<|),
  hnil,
  hmap,
  hzipWith,
  hzipWith3,
  hzipWithM,
  hzipWith3M,
  hfoldMap,
  hfoldMap1,
  hfoldl,
  hfoldl',
  hfoldr,
  hfoldr',
  htraverse,
  htraverse_,
) where

import Control.Lens (ix, (&), (.~))
import Data.Foldable (traverse_)
import Data.Kind
import Data.Maybe (fromJust)
import Data.Proxy (Proxy (..))
import Data.Vector qualified as V
import FpMatsuri2026.TypeOps
import GHC.Exts (Any)
import GHC.TypeError
import GHC.TypeNats (KnownNat, SomeNat (..), natVal, someNatVal, type (+))
import Unsafe.Coerce (unsafeCoerce)

type HList :: (k -> Type) -> [k] -> Type
newtype HList f xs = UnsafeHList (V.Vector Any)

type family IndexOf x xs where
  IndexOf x '[] = TypeError ('Text "A type `" :<>: 'ShowType x :<>: 'Text "' not found!")
  IndexOf x (x ': xs) = 0
  IndexOf x (y ': xs) = 1 + IndexOf x xs

type Member :: k -> [k] -> Constraint
class Member x xs where
  hGetSet :: HList f xs -> (f x, f x -> HList f xs)

instance
  {-# OVERLAPPING #-}
  (Unsatisfiable ('ShowType x ':<>: 'Text " is not a member")) =>
  Member x '[]
  where
  hGetSet = unsatisfiable

instance {-# OVERLAPPABLE #-} (KnownNat (IndexOf x xs)) => Member x xs where
  hGetSet (UnsafeHList xs) =
    let !i =
          fromIntegral $
            natVal $
              Proxy @(IndexOf x xs)
        !x = unsafeCoerce $ V.unsafeIndex xs i
     in (x, \ !v' -> UnsafeHList $ xs & ix i .~ unsafeCoerce v')
  {-# INLINE hGetSet #-}

hzipWith ::
  forall f g k xs.
  (forall v. f v -> g v -> k v) ->
  HList f xs ->
  HList g xs ->
  HList k xs
hzipWith f (UnsafeHList fs) (UnsafeHList gs) =
  UnsafeHList $
    V.izipWith
      ( \i fx gx ->
          case someNatVal (fromIntegral i) of
            SomeNat (_ :: Proxy n) ->
              unsafeCoerce (f (unsafeCoerce fx :: f (ElemAt n xs)) (unsafeCoerce gx :: g (ElemAt n xs)))
      )
      fs
      gs

hzipWith3 ::
  forall f g k h xs.
  (forall v. f v -> g v -> k v -> h v) ->
  HList f xs ->
  HList g xs ->
  HList k xs ->
  HList h xs
hzipWith3 f (UnsafeHList fs) (UnsafeHList gs) (UnsafeHList hs) =
  UnsafeHList $
    V.izipWith3
      ( \i fx gx hx ->
          case someNatVal (fromIntegral i) of
            SomeNat (_ :: Proxy n) ->
              let fx' = unsafeCoerce fx :: f (ElemAt n xs)
                  gx' = unsafeCoerce gx :: g (ElemAt n xs)
                  hx' = unsafeCoerce hx :: k (ElemAt n xs)
               in unsafeCoerce $ f fx' gx' hx'
      )
      fs
      gs
      hs

hzipWithM ::
  (Applicative m) =>
  (forall v. f v -> g v -> m (k v)) ->
  HList f xs ->
  HList g xs ->
  m (HList k xs)
hzipWithM f (UnsafeHList fs :: HList f xs) (UnsafeHList gs) =
  UnsafeHList
    <$> traverse
      ( \(i, (fx, gx)) ->
          case someNatVal (fromIntegral i) of
            SomeNat (_ :: Proxy n) ->
              let fx' = unsafeCoerce fx :: f (ElemAt n xs)
                  gx' = unsafeCoerce gx :: g (ElemAt n xs)
               in unsafeCoerce <$> f fx' gx'
      )
      (V.indexed $ V.zip fs gs)

hzipWith3M ::
  (Applicative m) =>
  (forall v. f v -> g v -> k v -> m (h v)) ->
  HList f xs ->
  HList g xs ->
  HList k xs ->
  m (HList h xs)
hzipWith3M f (UnsafeHList fs :: HList f xs) (UnsafeHList gs) (UnsafeHList hs) =
  UnsafeHList
    <$> traverse
      ( \(i, (fx, gx, hx)) ->
          case someNatVal (fromIntegral i) of
            SomeNat (_ :: Proxy n) ->
              let fx' = unsafeCoerce fx :: f (ElemAt n xs)
                  gx' = unsafeCoerce gx :: g (ElemAt n xs)
                  hx' = unsafeCoerce hx :: k (ElemAt n xs)
               in unsafeCoerce <$> f fx' gx' hx'
      )
      (V.indexed $ V.zip3 fs gs hs)

hfoldMap ::
  forall w f xs.
  (Monoid w) =>
  (forall v. f v -> w) ->
  HList f xs ->
  w
hfoldMap f (UnsafeHList xs) =
  V.foldMap
    ( \(i, x) -> case someNatVal (fromIntegral i) of
        SomeNat (_ :: Proxy n) ->
          f (unsafeCoerce x :: f (ElemAt n xs))
    )
    $ V.indexed xs

hfoldMap1 ::
  forall w f x xs.
  (Semigroup w) =>
  (forall v. f v -> w) ->
  HList f (x ': xs) ->
  w
hfoldMap1 f (UnsafeHList xs) =
  let (hd, tl) = fromJust $ V.uncons xs
   in V.ifoldl'
        ( \w' i x ->
            case someNatVal (fromIntegral i) of
              SomeNat (_ :: Proxy n) ->
                w' <> f (unsafeCoerce x :: f (ElemAt n xs))
        )
        (f (unsafeCoerce hd :: f x))
        tl

hfoldl :: forall r f xs. (forall v. r -> f v -> r) -> r -> HList f xs -> r
hfoldl f z (UnsafeHList xs) =
  V.ifoldl
    ( \z' i x ->
        case someNatVal (fromIntegral i) of
          SomeNat (_ :: Proxy n) ->
            f z' (unsafeCoerce x :: f (ElemAt n xs))
    )
    z
    xs

hfoldl' :: forall r f xs. (forall v. r -> f v -> r) -> r -> HList f xs -> r
hfoldl' f z (UnsafeHList xs) =
  V.ifoldl'
    ( \ !z' !i !x ->
        case someNatVal (fromIntegral i) of
          SomeNat (_ :: Proxy n) ->
            f z' (unsafeCoerce x :: f (ElemAt n xs))
    )
    z
    xs

hfoldr :: forall r f xs. (forall v. f v -> r -> r) -> r -> HList f xs -> r
hfoldr f z (UnsafeHList xs) =
  V.ifoldr
    ( \i x z' ->
        case someNatVal (fromIntegral i) of
          SomeNat (_ :: Proxy n) ->
            f (unsafeCoerce x :: f (ElemAt n xs)) z'
    )
    z
    xs

hfoldr' :: forall r f xs. (forall v. f v -> r -> r) -> r -> HList f xs -> r
hfoldr' f z (UnsafeHList xs) =
  V.ifoldr'
    ( \ !i !x !z' ->
        case someNatVal (fromIntegral i) of
          SomeNat (_ :: Proxy n) ->
            f (unsafeCoerce x :: f (ElemAt n xs)) z'
    )
    z
    xs

hmap :: forall f g xs. (forall v. f v -> g v) -> HList f xs -> HList g xs
hmap f (UnsafeHList xs) =
  UnsafeHList $
    V.imap
      ( \i x ->
          case someNatVal (fromIntegral i) of
            SomeNat (_ :: Proxy n) ->
              unsafeCoerce (f (unsafeCoerce x :: f (ElemAt n xs)))
      )
      xs

(<|) :: f x -> HList f xs -> HList f (x ': xs)
fx <| UnsafeHList xs = UnsafeHList (V.cons (unsafeCoerce fx) xs)

infixr 5 <|

hnil :: HList f '[]
hnil = UnsafeHList V.empty

htraverse :: (Applicative m) => (forall v. f v -> m (g v)) -> HList f xs -> m (HList g xs)
htraverse f (UnsafeHList xs :: HList f xs) =
  UnsafeHList
    <$> traverse
      ( \(i, x) -> case someNatVal (fromIntegral i) of
          SomeNat (_ :: Proxy n) ->
            unsafeCoerce <$> f (unsafeCoerce x :: f (ElemAt n xs))
      )
      (V.indexed xs)

htraverse_ :: (Applicative m) => (forall v. f v -> m ()) -> HList f xs -> m ()
htraverse_ f (UnsafeHList xs :: HList f xs) =
  traverse_
    ( \(i, x) -> case someNatVal (fromIntegral i) of
        SomeNat (_ :: Proxy n) ->
          f (unsafeCoerce x :: f (ElemAt n xs))
    )
    (V.indexed xs)
