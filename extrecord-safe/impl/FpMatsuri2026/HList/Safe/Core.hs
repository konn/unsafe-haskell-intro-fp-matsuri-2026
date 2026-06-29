module FpMatsuri2026.HList.Safe.Core (
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

import Data.Kind
import GHC.TypeError

type HList :: (k -> Type) -> [k] -> Type
data HList f xs where
  HNil :: HList f '[]
  (:-) :: f x -> HList f xs -> HList f (x ': xs)

infixr 5 :-

type Member :: k -> [k] -> Constraint
class Member x xs where
  hGetSet :: (HList f xs -> f x, f x -> HList f xs -> HList f xs)

instance
  (Unsatisfiable ('ShowType x ':<>: 'Text " is not a member")) =>
  Member x '[]
  where
  hGetSet = unsatisfiable

instance {-# OVERLAPPING #-} Member x (x ': xs) where
  hGetSet = (\(v :- _) -> v, \v' (_ :- xs) -> v' :- xs)
  {-# INLINE hGetSet #-}

instance
  {-# OVERLAPPABLE #-}
  (Member x xs) =>
  Member x (y ': xs)
  where
  hGetSet =
    ( \(_ :- xs) -> fst (hGetSet @_ @x @xs) xs
    , \v' (y :- xs) -> y :- snd (hGetSet @_ @x @xs) v' xs
    )
  {-# INLINE hGetSet #-}

hzipWith :: (forall v. f v -> g v -> k v) -> HList f xs -> HList g xs -> HList k xs
hzipWith _ HNil HNil = HNil
hzipWith f (fv :- fs) (gv :- gs) = f fv gv :- hzipWith f fs gs

hzipWith3 :: (forall v. f v -> g v -> k v -> h v) -> HList f xs -> HList g xs -> HList k xs -> HList h xs
hzipWith3 _ HNil HNil HNil = HNil
hzipWith3 f (fv :- fs) (gv :- gs) (hv :- hs) = f fv gv hv :- hzipWith3 f fs gs hs

hzipWithM ::
  (Applicative m) =>
  (forall v. f v -> g v -> m (k v)) ->
  HList f xs ->
  HList g xs ->
  m (HList k xs)
hzipWithM _ HNil HNil = pure HNil
hzipWithM f (fv :- fs) (gv :- gs) = (:-) <$> f fv gv <*> hzipWithM f fs gs

hzipWith3M ::
  (Applicative m) =>
  (forall v. f v -> g v -> k v -> m (h v)) ->
  HList f xs ->
  HList g xs ->
  HList k xs ->
  m (HList h xs)
hzipWith3M _ HNil HNil HNil = pure HNil
hzipWith3M f (fv :- fs) (gv :- gs) (hv :- hs) =
  (:-) <$> f fv gv hv <*> hzipWith3M f fs gs hs

hfoldMap1 :: forall w f x xs. (Semigroup w) => (forall v. f v -> w) -> HList f (x ': xs) -> w
hfoldMap1 f (x :- xs) = go (f x) xs
  where
    go :: w -> HList f ys -> w
    go !z HNil = z
    go z (y :- ys) = go (z <> f y) ys

hfoldMap :: forall w f xs. (Monoid w) => (forall v. f v -> w) -> HList f xs -> w
hfoldMap f = go mempty
  where
    go :: w -> HList f ys -> w
    go !z HNil = z
    go z (x :- xs) = go (z <> f x) xs

hfoldl :: forall r f xs. (forall v. r -> f v -> r) -> r -> HList f xs -> r
hfoldl f = go
  where
    go :: r -> HList f ys -> r
    go z HNil = z
    go z (x :- xs) = go (f z x) xs

hfoldl' :: forall r f xs. (forall v. r -> f v -> r) -> r -> HList f xs -> r
hfoldl' f = go
  where
    go :: r -> HList f ys -> r
    go !z HNil = z
    go z (x :- xs) = go (f z x) xs

hfoldr :: forall r f xs. (forall v. f v -> r -> r) -> r -> HList f xs -> r
hfoldr f = go
  where
    go :: r -> HList f ys -> r
    go z HNil = z
    go z (x :- xs) = f x (go z xs)

hfoldr' :: forall r f xs. (forall v. f v -> r -> r) -> r -> HList f xs -> r
hfoldr' f = go
  where
    go :: r -> HList f ys -> r
    go !z HNil = z
    go z (x :- xs) = f x (go z xs)

hmap :: (forall v. f v -> g v) -> HList f xs -> HList g xs
hmap _ HNil = HNil
hmap f (x :- xs) = f x :- hmap f xs

(<|) :: f x -> HList f xs -> HList f (x ': xs)
(<|) = (:-)

infixr 5 <|

hnil :: HList f '[]
hnil = HNil

htraverse :: (Applicative m) => (forall v. f v -> m (g v)) -> HList f xs -> m (HList g xs)
htraverse (f :: forall v. f v -> m (g v)) = go
  where
    go :: HList f ys -> m (HList g ys)
    go HNil = pure HNil
    go (x :- xs) = (:-) <$> f x <*> go xs

htraverse_ :: (Applicative m) => (forall v. f v -> m ()) -> HList f xs -> m ()
htraverse_ (f :: forall v. f v -> m ()) = go
  where
    go :: HList f ys -> m ()
    go HNil = pure ()
    go (x :- xs) = f x *> go xs
