module FpMatsuri2026.HList (
  HList,
  (<|),
  hnil,
  Member (..),
  hLookup,
  hReplace,
  hmap,
  hzipWith,
  hzipWith3,
  hzipWithM,
  hzipWith3M,
  hfoldMap,
  hfoldMap1,
  hintercalateMap1,
  hfoldl,
  hfoldl',
  hfoldr,
  hfoldr',
  htraverse,
  htraverse_,
  hfor,
  hfor_,
  All (..),
) where

import FpMatsuri2026.HList.Core
import FpMatsuri2026.TypeOps

hLookup :: forall x xs f. (Member x xs) => HList f xs -> f x
hLookup = fst $ hGetSet @_ @x

hReplace :: forall x xs f. (Member x xs) => f x -> HList f xs -> HList f xs
hReplace = snd $ hGetSet @_ @x

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

class All c xs where
  allDict :: HList (Dict1 c) xs

instance All c '[] where
  allDict = hnil

instance (c x, All c xs) => All c (x ': xs) where
  allDict = Dict1 <| allDict

hfor ::
  (Applicative m) =>
  HList f xs ->
  (forall v. f v -> m (g v)) ->
  m (HList g xs)
hfor xs f = htraverse f xs

hfor_ ::
  (Applicative m) =>
  HList f xs ->
  (forall v. f v -> m ()) ->
  m ()
hfor_ xs f = htraverse_ f xs
