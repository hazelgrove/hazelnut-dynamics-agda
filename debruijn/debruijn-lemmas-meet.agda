open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-lemmas-prec

module debruijn.debruijn-lemmas-meet where

  ⊓-lb : ∀{τ1 τ2 τ3} → τ1 ⊓ τ2 == τ3 → (τ3 ⊑t τ1 × τ3 ⊑t τ2)
  ⊓-lb MeetHoleL = PTHole , ⊑t-refl _ 
  ⊓-lb MeetHoleR = ⊑t-refl _ , PTHole
  ⊓-lb MeetBase = PTBase , PTBase
  ⊓-lb MeetVar = PTTVar , PTTVar
  ⊓-lb (MeetArr meet meet₁) = (PTArr (π1 (⊓-lb meet)) (π1 (⊓-lb meet₁))) , (PTArr (π2 (⊓-lb meet)) (π2 (⊓-lb meet₁)))
  ⊓-lb (MeetForall meet) = (PTForall (π1 (⊓-lb meet))) , (PTForall (π2 (⊓-lb meet))) 

  ⊑t-⊓ : ∀{τ1 τ2 τ3 τ1' τ2'} → τ1 ⊑t τ1' → τ2 ⊑t τ2' → τ1 ⊓ τ2 == τ3 → Σ[ τ3' ∈ htyp ] ((τ1' ⊓ τ2' == τ3') × (τ3 ⊑t τ3'))
  ⊑t-⊓ PTHole prec2 MeetHoleL = _ , MeetHoleL , prec2 
  ⊑t-⊓ prec1 PTHole MeetHoleR = _ , MeetHoleR , prec1
  ⊑t-⊓ PTHole PTHole thing = ⦇-⦈ , MeetHoleL , PTHole
  ⊑t-⊓ PTBase PTBase MeetBase = _ , MeetBase , PTBase
  ⊑t-⊓ PTBase PTHole MeetBase = _ , MeetHoleR , PTBase
  ⊑t-⊓ PTHole PTBase MeetBase = _ , MeetHoleL , PTBase
  ⊑t-⊓ PTHole PTTVar MeetVar = _ , MeetHoleL , PTTVar
  ⊑t-⊓ PTTVar PTHole MeetVar = _ , MeetHoleR , PTTVar 
  ⊑t-⊓ PTTVar PTTVar MeetVar = _ , MeetVar , PTTVar
  ⊑t-⊓ PTHole (PTArr prec2 prec3) (MeetArr meet1 meet2) = _ , MeetHoleL , PTArr (⊑t-trans (π2 (⊓-lb  meet1)) prec2) ((⊑t-trans (π2 (⊓-lb  meet2)) prec3))
  ⊑t-⊓ (PTArr prec1 prec2) PTHole (MeetArr meet1 meet2) = _ , MeetHoleR , PTArr (⊑t-trans (π1 (⊓-lb  meet1)) prec1) (⊑t-trans (π1 (⊓-lb  meet2)) prec2)
  ⊑t-⊓ (PTArr prec1 prec2) (PTArr prec3 prec4) (MeetArr meet1 meet2) with ⊑t-⊓ prec1 prec3 meet1 | ⊑t-⊓ prec2 prec4 meet2 
  ... | _ , meet1' , prec1' | _ , meet2' , prec2' = _ , MeetArr meet1' meet2' , PTArr prec1' prec2'
  ⊑t-⊓ PTHole (PTForall prec2) (MeetForall meet) = _ , MeetHoleL , PTForall (⊑t-trans (π2 (⊓-lb  meet)) prec2) 
  ⊑t-⊓ (PTForall prec1) PTHole (MeetForall meet) = _ , MeetHoleR , PTForall (⊑t-trans (π1 (⊓-lb  meet)) prec1)
  ⊑t-⊓ (PTForall prec1) (PTForall prec2) (MeetForall meet) with ⊑t-⊓ prec1 prec2 meet 
  ... | _ , meet' , prec' = _ , MeetForall meet' , PTForall prec' 

  ⊓-wf : ∀{τ1 τ2 τ3 Θ} → τ1 ⊓ τ2 == τ3 → Θ ⊢ τ1 wf → Θ ⊢ τ2 wf → Θ ⊢ τ3 wf
  ⊓-wf MeetHoleL wf1 wf2 = wf2 
  ⊓-wf MeetHoleR wf1 wf2 = wf1
  ⊓-wf MeetBase wf1 wf2 = wf2
  ⊓-wf MeetVar wf1 wf2 = wf2
  ⊓-wf (MeetArr meet meet₁) (WFArr wf1 wf2) (WFArr wf3 wf4) = WFArr (⊓-wf meet wf1 wf3) (⊓-wf meet₁ wf2 wf4)
  ⊓-wf (MeetForall meet) (WFForall wf1) (WFForall wf2) = WFForall (⊓-wf meet wf1 wf2)