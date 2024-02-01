open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-lemmas-prec

module debruijn.debruijn-lemmas-meet where

  ⊓-lb : ∀{τ1 τ2 τ3} → τ1 ⊓ τ2 == τ3 → (τ3 ⊑t τ1 × τ3 ⊑t τ2)
  ⊓-lb JoinHoleL = PTHole , ⊑t-refl _ 
  ⊓-lb JoinHoleR = ⊑t-refl _ , PTHole
  ⊓-lb JoinBase = PTBase , PTBase
  ⊓-lb JoinVar = PTTVar , PTTVar
  ⊓-lb (JoinArr meet meet₁) = (PTArr (π1 (⊓-lb meet)) (π1 (⊓-lb meet₁))) , (PTArr (π2 (⊓-lb meet)) (π2 (⊓-lb meet₁)))
  ⊓-lb (JoinForall meet) = (PTForall (π1 (⊓-lb meet))) , (PTForall (π2 (⊓-lb meet))) 

  ⊑t-⊓ : ∀{τ1 τ2 τ3 τ1' τ2'} → τ1 ⊑t τ1' → τ2 ⊑t τ2' → τ1 ⊓ τ2 == τ3 → Σ[ τ3' ∈ htyp ] ((τ1' ⊓ τ2' == τ3') × (τ3 ⊑t τ3'))
  ⊑t-⊓ PTHole prec2 JoinHoleL = _ , JoinHoleL , prec2 
  ⊑t-⊓ prec1 PTHole JoinHoleR = _ , JoinHoleR , prec1
  ⊑t-⊓ PTHole PTHole thing = ⦇-⦈ , JoinHoleL , PTHole
  ⊑t-⊓ PTBase PTBase JoinBase = _ , JoinBase , PTBase
  ⊑t-⊓ PTBase PTHole JoinBase = _ , JoinHoleR , PTBase
  ⊑t-⊓ PTHole PTBase JoinBase = _ , JoinHoleL , PTBase
  ⊑t-⊓ PTHole PTTVar JoinVar = _ , JoinHoleL , PTTVar
  ⊑t-⊓ PTTVar PTHole JoinVar = _ , JoinHoleR , PTTVar 
  ⊑t-⊓ PTTVar PTTVar JoinVar = _ , JoinVar , PTTVar
  ⊑t-⊓ PTHole (PTArr prec2 prec3) (JoinArr meet1 meet2) = _ , JoinHoleL , PTArr (⊑t-trans (π2 (⊓-lb  meet1)) prec2) ((⊑t-trans (π2 (⊓-lb  meet2)) prec3))
  ⊑t-⊓ (PTArr prec1 prec2) PTHole (JoinArr meet1 meet2) = _ , JoinHoleR , PTArr (⊑t-trans (π1 (⊓-lb  meet1)) prec1) (⊑t-trans (π1 (⊓-lb  meet2)) prec2)
  ⊑t-⊓ (PTArr prec1 prec2) (PTArr prec3 prec4) (JoinArr meet1 meet2) with ⊑t-⊓ prec1 prec3 meet1 | ⊑t-⊓ prec2 prec4 meet2 
  ... | _ , meet1' , prec1' | _ , meet2' , prec2' = _ , JoinArr meet1' meet2' , PTArr prec1' prec2'
  ⊑t-⊓ PTHole (PTForall prec2) (JoinForall meet) = _ , JoinHoleL , PTForall (⊑t-trans (π2 (⊓-lb  meet)) prec2) 
  ⊑t-⊓ (PTForall prec1) PTHole (JoinForall meet) = _ , JoinHoleR , PTForall (⊑t-trans (π1 (⊓-lb  meet)) prec1)
  ⊑t-⊓ (PTForall prec1) (PTForall prec2) (JoinForall meet) with ⊑t-⊓ prec1 prec2 meet 
  ... | _ , meet' , prec' = _ , JoinForall meet' , PTForall prec' 