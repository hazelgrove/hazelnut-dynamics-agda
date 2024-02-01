open import Nat
open import Prelude
open import debruijn.debruijn-core-type

module debruijn.debruijn-lemmas-consistency where
  
  ~sym : {t1 t2 : htyp} → t1 ~ t2 → t2 ~ t1
  ~sym ConsistBase = ConsistBase
  ~sym ConsistVar = ConsistVar
  ~sym ConsistHole1 = ConsistHole2
  ~sym ConsistHole2 = ConsistHole1
  ~sym ConsistArr = ConsistArr
  ~sym (ConsistForall consist) = ConsistForall (~sym consist)
