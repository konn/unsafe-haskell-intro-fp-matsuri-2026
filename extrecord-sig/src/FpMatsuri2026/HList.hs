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
  hfoldMap,
  hfoldMap1,
  hintercalateMap1,
  hfoldl,
  hfoldl',
  hfoldr,
  hfoldr',
  All (..),
) where

import FpMatsuri2026.HList.Core

hLookup :: forall x xs f. (Member x xs) => HList f xs -> f x
hLookup xs = fst (hGetSet @_ @x xs)

hReplace :: forall x xs f. (Member x xs) => f x -> HList f xs -> HList f xs
hReplace v xs = snd (hGetSet @_ @x xs) v
