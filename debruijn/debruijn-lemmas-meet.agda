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
  ⊑t-⊓ PTHole PTHole _ = ⦇-⦈ , MeetHoleL , PTHole
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

  ⊑t-⊓-fun :  ∀{τ1 τ2 τ3 τ1' τ2' τ3'} → τ1 ⊑t τ1' → τ2 ⊑t τ2' → τ1 ⊓ τ2 == τ3 → τ1' ⊓ τ2' == τ3' → τ3 ⊑t τ3'
  ⊑t-⊓-fun PTHole prec2 MeetHoleL MeetHoleL = prec2
  ⊑t-⊓-fun PTHole prec2 MeetHoleL MeetHoleR = prec2
  ⊑t-⊓-fun prec1 PTHole MeetHoleR MeetHoleL = prec1
  ⊑t-⊓-fun prec1 PTHole MeetHoleR MeetHoleR = prec1
  ⊑t-⊓-fun prec1 prec2 MeetBase MeetHoleL = prec2
  ⊑t-⊓-fun prec1 prec2 MeetBase MeetHoleR = prec1
  ⊑t-⊓-fun prec1 prec2 MeetBase MeetBase = prec2
  ⊑t-⊓-fun prec1 prec2 MeetVar MeetHoleL = prec2
  ⊑t-⊓-fun prec1 prec2 MeetVar MeetHoleR = prec1
  ⊑t-⊓-fun prec1 prec2 MeetVar MeetVar = prec2
  ⊑t-⊓-fun PTHole prec2 (MeetArr meet1 meet2) MeetHoleL = ⊑t-trans (PTArr (π2 (⊓-lb meet1)) (π2 (⊓-lb meet2))) prec2
  ⊑t-⊓-fun prec1 prec2 (MeetArr meet1 meet2) MeetHoleR = ⊑t-trans (PTArr (π1 (⊓-lb meet1)) (π1 (⊓-lb meet2))) prec1
  ⊑t-⊓-fun (PTArr prec1 prec2) (PTArr prec3 prec4) (MeetArr meet1 meet2) (MeetArr meet3 meet4) = 
      PTArr (⊑t-⊓-fun prec1 prec3 meet1 meet3) (⊑t-⊓-fun prec2 prec4 meet2 meet4) 
  ⊑t-⊓-fun PTHole prec2 (MeetForall meet) MeetHoleL = ⊑t-trans (PTForall (π2 (⊓-lb meet))) prec2
  ⊑t-⊓-fun prec1 prec2 (MeetForall meet) MeetHoleR = ⊑t-trans (PTForall (π1 (⊓-lb meet))) prec1
  ⊑t-⊓-fun (PTForall prec1) (PTForall prec2) (MeetForall meet) (MeetForall meet2) = PTForall (⊑t-⊓-fun prec1 prec2 meet meet2)


  module meet-match where 

    --- direct matching for arrows
    data _▸arr_ : htyp → htyp → Set where
      MAHole : ⦇-⦈ ▸arr ⦇-⦈ ==> ⦇-⦈
      MAArr  : {τ1 τ2 : htyp} → τ1 ==> τ2 ▸arr τ1 ==> τ2

    --- direct matching for foralls
    data _▸forall_ : htyp → htyp → Set where
      MFHole : ⦇-⦈ ▸forall (·∀ ⦇-⦈)
      MFForall : ∀{τ} → (·∀ τ) ▸forall (·∀ τ)

    ⊓-▸arr : ∀{τ1 τ2 τ3} → τ1 ⊓ (⦇-⦈ ==> ⦇-⦈) == τ2 → τ1 ▸arr τ3 → τ2 == τ3
    ⊓-▸arr MeetHoleL MAHole = refl
    ⊓-▸arr (MeetArr MeetHoleL MeetHoleL) MAArr = refl
    ⊓-▸arr (MeetArr MeetHoleL MeetHoleR) MAArr = refl
    ⊓-▸arr (MeetArr MeetHoleR MeetHoleL) MAArr = refl
    ⊓-▸arr (MeetArr MeetHoleR MeetHoleR) MAArr = refl

    ⊓-▸forall : ∀{τ1 τ2 τ3} → τ1 ⊓ ·∀ ⦇-⦈ == τ2 → τ1 ▸forall τ3 → τ2 == τ3
    ⊓-▸forall MeetHoleL MFHole = refl     
    ⊓-▸forall (MeetForall MeetHoleL) MFForall = refl 
    ⊓-▸forall (MeetForall MeetHoleR) MFForall = refl 