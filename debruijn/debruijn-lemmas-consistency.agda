open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-index

module debruijn.debruijn-lemmas-consistency where

  ~refl : {τ : htyp} → τ ~ τ
  ~refl {τ = b} = ConsistBase
  ~refl {τ = T x} = ConsistVar
  ~refl {τ = ⦇-⦈} = ConsistHole1
  ~refl {τ = τ ==> τ₁} = ConsistArr ~refl ~refl
  ~refl {τ = ·∀ τ} = ConsistForall ~refl
  
  ~sym : {τ1 τ2 : htyp} → τ1 ~ τ2 → τ2 ~ τ1
  ~sym ConsistBase = ConsistBase
  ~sym ConsistVar = ConsistVar 
  ~sym ConsistHole1 = ConsistHole2
  ~sym ConsistHole2 = ConsistHole1
  ~sym (ConsistArr con1 con2) = ConsistArr (~sym con1) (~sym con2)
  ~sym (ConsistForall consist) = ConsistForall (~sym consist)