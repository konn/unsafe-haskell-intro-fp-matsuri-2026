{-# LANGUAGE TypeData #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module FpMatsuri2026.TypeOps (
  Dict1 (..),
  Dict (..),
  withDict1,
  All_,
  All (..),
  Map,
  Lookup,
  Lookup',
  Fst,
  Snd,
  FromJust,
  MapApply,
  Fst1,
  Apply,
) where

import Data.Kind
import FpMatsuri2026.HList
import GHC.TypeError

data Dict1 c x where
  Dict1 :: (c x) => Dict1 c x

data Dict c where
  Dict :: (c) => Dict c

withDict1 :: Dict1 c x -> ((c x) => r) -> r
withDict1 Dict1 r = r

type All_ :: (k -> Constraint) -> [k] -> Constraint
type family All_ c xs where
  All_ c '[] = ()
  All_ c (x ': xs) = (c x, All c xs)

class (All_ c xs) => All c xs where
  allDict :: HList (Dict1 c) xs

instance All c '[] where
  allDict = HNil

instance (c x, All c xs) => All c (x ': xs) where
  allDict = Dict1 :- allDict

type Map :: (a -> b) -> [a] -> [b]
type family Map f xs where
  Map f '[] = '[]
  Map f (x ': xs) = f x ': Map f xs

type Fst :: (a, b) -> a
type family Fst ab where
  Fst '(a, b) = a

type Snd :: (a, b) -> b
type family Snd ab where
  Snd '(_, b) = b

type Lookup :: k -> [(k, v)] -> Maybe v
type family Lookup k kvs where
  Lookup t '[] = 'Nothing
  Lookup t ('(t, v) ': kvs) = 'Just v
  Lookup t ('(t', v) ': kvs) = Lookup t kvs

type Lookup' :: k -> [(k, v)] -> v
type Lookup' k kvs = FromJust ('ShowType k ':<>: 'Text " is not a member of the " ':<>: 'ShowType kvs) (Lookup k kvs)

type FromJust :: ErrorMessage -> Maybe a -> a
type family FromJust msg m where
  FromJust _ ('Just a) = a
  FromJust msg 'Nothing = TypeError msg

type a ~> b = a -> b -> Type

infixr 4 ~>

type data Fst1 :: (a, b) ~> a

type Apply :: (a ~> b) -> a -> b
type family Apply f a

type instance Apply Fst1 '(a, b) = a

type MapApply :: (a ~> b) -> [a] -> [b]
type family MapApply f xs where
  MapApply f '[] = '[]
  MapApply f (x ': xs) = Apply f x ': MapApply f xs

type Delete :: k -> [k] -> [k]
type family Delete k xs where
  Delete k '[] = '[]
  Delete x (x ': xs) = xs
  Delete k (x' ': xs) = x' ': Delete k xs
