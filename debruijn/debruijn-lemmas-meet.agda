open import Nat
open import Prelude
open import contexts
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-prec

module debruijn.debruijn-lemmas-meet where

  ⊓-lb : ∀{τ1 τ2 τ3} → τ1 ⊓ τ2 == τ3 → (τ3 ⊑t τ1 × τ3 ⊑t τ2)
  ⊓-lb JoinHoleL = PTHole , ⊑t-refl _ 
  ⊓-lb JoinHoleR = ⊑t-refl _ , PTHole
  ⊓-lb JoinBase = PTBase , PTBase
  ⊓-lb JoinVar = PTTVar , PTTVar
  ⊓-lb (JoinArr meet meet₁) = (PTArr (π1 (⊓-lb meet)) (π1 (⊓-lb meet₁))) , (PTArr (π2 (⊓-lb meet)) (π2 (⊓-lb meet₁)))
  ⊓-lb (JoinForall meet) = (PTForall (π1 (⊓-lb meet))) , (PTForall (π2 (⊓-lb meet))) 