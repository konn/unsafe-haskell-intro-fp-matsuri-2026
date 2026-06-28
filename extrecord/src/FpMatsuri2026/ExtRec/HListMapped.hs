module FpMatsuri2026.ExtRec.HListMapped where

import FpMatsuri2026.HList
import FpMatsuri2026.TypeOps
import GHC.Generics

newtype Field f kvs k = Field {runField :: f (Lookup' k kvs)}
  deriving (Generic)

deriving newtype instance (Eq (f (Lookup' k kvs))) => Eq (Field f kvs k)

deriving newtype instance (Ord (f (Lookup' k kvs))) => Ord (Field f kvs k)

deriving newtype instance (Show (f (Lookup' k kvs))) => Show (Field f kvs k)

newtype Record f kvs = Record {runRecord :: HList (Field f kvs) (MapApply Fst1 kvs)}
