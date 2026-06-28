module FpMatsuri2026.HList.Safe.Core (
  HList (..),
  Member (..),
  (<|),
  hnil,
  hLookup,
  hReplace,
  hmap,
  hzipWith,
  hzipWith3,
  hfoldMap,
  hfoldMap1,
  hintercalateMap1,
  hfoldl,
  hfoldl',
  hfoldr,
  hfoldr',
  All(..),
) where

import Data.Kind
import GHC.TypeError
import FpMatsuri2026.TypeOps

type HList :: (k -> Type) -> [k] -> Type
data HList f xs where
  HNil :: HList f '[]
  (:-) :: f x -> HList f xs -> HList f (x ': xs)

infixr 5 :-

type Member :: k -> [k] -> Constraint
class Member x xs where
  hGetSet :: HList f xs -> (f x, f x -> HList f xs)

class All c xs where
  allDict :: HList (Dict1 c) xs

instance All c '[] where
  allDict = HNil

instance (c x, All c xs) => All c (x ': xs) where
  allDict = Dict1 :- allDict


hLookup :: forall x xs f. (Member x xs) => HList f xs -> f x
hLookup xs = fst (hGetSet @_ @x xs)

hReplace :: forall x xs f. (Member x xs) => f x -> HList f xs -> HList f xs
hReplace v xs = snd (hGetSet @_ @x xs) v

instance
  (Unsatisfiable ('ShowType x ':<>: 'Text " is not a member")) =>
  Member x '[]
  where
  hGetSet = unsatisfiable

instance {-# OVERLAPPING #-} Member x (x ': xs) where
  hGetSet (v :- xs) = (v, \v' -> v' :- xs)
  {-# INLINE hGetSet #-}

instance
  {-# OVERLAPPABLE #-}
  (Member x xs) =>
  Member x (y ': xs)
  where
  hGetSet (y :- xs) =
    let (v, f) = hGetSet @_ @x xs
     in (v, \v' -> y :- f v')
  {-# INLINE hGetSet #-}

hzipWith :: (forall v. f v -> g v -> k v) -> HList f xs -> HList g xs -> HList k xs
hzipWith _ HNil HNil = HNil
hzipWith f (fv :- fs) (gv :- gs) = f fv gv :- hzipWith f fs gs

hzipWith3 :: (forall v. f v -> g v -> k v -> h v) -> HList f xs -> HList g xs -> HList k xs -> HList h xs
hzipWith3 _ HNil HNil HNil = HNil
hzipWith3 f (fv :- fs) (gv :- gs) (hv :- hs) = f fv gv hv :- hzipWith3 f fs gs hs

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

newtype JoinWith a = JoinWith {joinee :: (a -> a)}

instance (Semigroup a) => Semigroup (JoinWith a) where
  JoinWith a <> JoinWith b = JoinWith $ \j -> a j <> j <> b j

hintercalateMap1 ::
  (Semigroup w) =>
  w ->
  (forall v. f v -> w) ->
  HList f (x ': xs) ->
  w
hintercalateMap1 sep f =
  flip joinee sep . hfoldMap1 (JoinWith . const . f)

(<|) :: f x -> HList f xs -> HList f (x ': xs)
(<|) = (:-)

infixr 5 <|

hnil :: HList f '[]
hnil = HNil
