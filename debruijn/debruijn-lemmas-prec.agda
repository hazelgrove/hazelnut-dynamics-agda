open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-subst
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-consistency

module debruijn.debruijn-lemmas-prec where

  ⊑t-refl : (τ : htyp) → τ ⊑t τ
  ⊑t-refl b = PTBase 
  ⊑t-refl (T x) = PTTVar
  ⊑t-refl ⦇-⦈ = PTHole
  ⊑t-refl (τ ==> τ₁) = PTArr (⊑t-refl τ) (⊑t-refl τ₁)
  ⊑t-refl (·∀ τ) = PTForall (⊑t-refl τ)

  ⊑t-trans : ∀{τ1 τ2 τ3} → τ1 ⊑t τ2 → τ2 ⊑t τ3 → τ1 ⊑t τ3
  ⊑t-trans prec1 PTBase = prec1
  ⊑t-trans prec1 PTHole = PTHole
  ⊑t-trans prec1 PTTVar = prec1
  ⊑t-trans (PTArr prec1 prec2) (PTArr prec3 prec4) = PTArr (⊑t-trans prec1 prec3) (⊑t-trans prec2 prec4)
  ⊑t-trans (PTForall prec1) (PTForall prec2) = PTForall (⊑t-trans prec1 prec2)

  ⊑t-consist : ∀{τ τ'} → τ ⊑t τ' → τ ~ τ'
  ⊑t-consist PTBase = ConsistBase
  ⊑t-consist PTHole = ConsistHole1
  ⊑t-consist PTTVar = ConsistVar
  ⊑t-consist (PTArr prec prec₁) = ConsistArr (⊑t-consist prec) (⊑t-consist prec₁)
  ⊑t-consist (PTForall prec) = ConsistForall (⊑t-consist prec)

  ⊑t-consist-left : ∀{τ τ' τ''} → τ ~ τ' → τ ⊑t τ'' → τ'' ~ τ'  
  ⊑t-consist-left ConsistHole1 prec = ConsistHole1
  ⊑t-consist-left consist PTBase = consist 
  ⊑t-consist-left consist PTHole = ConsistHole2
  ⊑t-consist-left consist PTTVar = consist
  ⊑t-consist-left (ConsistArr con1 con2) (PTArr prec1 prec2) = ConsistArr (⊑t-consist-left con1 prec1) (⊑t-consist-left con2 prec2)
  ⊑t-consist-left (ConsistForall consist) (PTForall prec) = ConsistForall (⊑t-consist-left consist prec)

  ⊑t-consist-right : ∀{τ τ' τ''} → τ ~ τ' → τ' ⊑t τ'' → τ ~ τ''
  ⊑t-consist-right consist prec = ~sym (⊑t-consist-left (~sym consist) prec)

  ⊑t-↑ : ∀{n m τ1 τ2} →
    (τ1 ⊑t τ2) →
    (↑ n m τ1) ⊑t (↑ n m τ2)
  ⊑t-↑ PTBase = PTBase
  ⊑t-↑ PTHole = PTHole
  ⊑t-↑ PTTVar = PTTVar
  ⊑t-↑ (PTArr prec prec₁) = PTArr (⊑t-↑ prec) (⊑t-↑ prec₁)
  ⊑t-↑ (PTForall prec) = PTForall (⊑t-↑ prec)

  ⊑t-↓ : ∀{n m τ1 τ2} →
    (τ1 ⊑t τ2) →
    (↓ n m τ1) ⊑t (↓ n m τ2)
  ⊑t-↓ PTBase = PTBase
  ⊑t-↓ PTHole = PTHole
  ⊑t-↓ PTTVar = PTTVar
  ⊑t-↓ (PTArr prec prec₁) = PTArr (⊑t-↓ prec) (⊑t-↓ prec₁)
  ⊑t-↓ (PTForall prec) = PTForall (⊑t-↓ prec)

  ⊑t-TT : ∀{n τ1 τ2 τ3 τ4} → (τ1 ⊑t τ3) → (τ2 ⊑t τ4) → (TT[ τ1 / n ] τ2) ⊑t (TT[ τ3 / n ] τ4)
  ⊑t-TT prec1 PTBase = PTBase
  ⊑t-TT prec1 PTHole = PTHole
  ⊑t-TT {n = n} prec1 (PTTVar {n = m}) with natEQ n m 
  ... | Inl refl = prec1 
  ... | Inr x = PTTVar
  ⊑t-TT prec1 (PTArr prec2 prec3) = PTArr (⊑t-TT prec1 prec2) (⊑t-TT prec1 prec3)
  ⊑t-TT prec1 (PTForall prec2) = PTForall (⊑t-TT (⊑t-↑ prec1) prec2)

  ⊑t-TTsub : ∀{n τ1 τ2 τ3 τ4} → (τ1 ⊑t τ3) → (τ2 ⊑t τ4) → TTSub n τ1 τ2 ⊑t TTSub n τ3 τ4
  ⊑t-TTsub prec1 PTBase = PTBase
  ⊑t-TTsub prec1 PTHole = PTHole
  ⊑t-TTsub {n = n} prec1 (PTTVar {n = m}) with natEQ n m 
  ... | Inl refl = ⊑t-↓ (⊑t-↑ prec1) 
  ... | Inr neq = PTTVar
  ⊑t-TTsub prec1 (PTArr prec2 prec3) = PTArr (⊑t-TTsub prec1 prec2) (⊑t-TTsub prec1 prec3)
  ⊑t-TTsub {τ3 = τ3} prec1 (PTForall prec2) = PTForall (⊑t-TTsub prec1 prec2) 

  ⊑c-var : ∀{n τ Γ Γ'} → (n , τ ∈ Γ) → Γ ⊑c Γ' → Σ[ τ' ∈ htyp ] ((n , τ' ∈ Γ') × (τ ⊑t τ'))
  ⊑c-var (InCtxSkip inctx) (PCTVar precc) with ⊑c-var inctx precc
  ... | τ' , inctx' , prec' = ↑ Z 1 τ' , InCtxSkip inctx' , ⊑t-↑ prec'
  ⊑c-var InCtxZ (PCVar x precc) = _ , InCtxZ , x
  ⊑c-var (InCtx1+ inctx) (PCVar x precc) with ⊑c-var inctx precc
  ... | τ' , inctx' , prec' = τ' , InCtx1+ inctx' , prec' 