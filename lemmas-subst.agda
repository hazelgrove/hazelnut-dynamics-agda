open import Nat
open import Prelude
open import core-type
open import core-exp
open import core-subst
open import core
open import weakening
open import lemmas-index
open import lemmas-ctx
open import lemmas-consistency
open import lemmas-meet

module lemmas-subst where

  wf-TTSub-helper2 :
    ∀{t n Γ} →
    (t == n → ⊥) →
    (TVar, (ctx-extend-tvars t Γ)) ⊢ T n wf →
    (TVar, (ctx-extend-tvars t Γ)) ⊢ T (1+ (↓Nat t 1 n)) wf
  wf-TTSub-helper2 {t = Z} neq WFVarZ = abort (neq refl)
  wf-TTSub-helper2 {t = 1+ t} neq WFVarZ = WFVarS WFVarZ
  wf-TTSub-helper2 {t = Z} neq (WFVarS wf) = WFVarS wf
  wf-TTSub-helper2 {t = 1+ t} neq (WFVarS {n = n} wf) = WFVarS (wf-TTSub-helper2 {t = t} (h1 neq) wf)
    where 
      h1 : (1+ t == 1+ n → ⊥) → t == n → ⊥
      h1 neq eq rewrite eq = neq refl

  wf-TTSub-helper3 :
    ∀{m n Γ τ} → 
    Γ ⊢ τ wf →
    (ctx-extend-tvars n Γ) ⊢ ↓ (m nat+ n) 1 (↑ m (1+ n) τ) wf
  wf-TTSub-helper3 {m = m} {n = n} {Γ = τ , Γ} (WFSkip wf) with wf-TTSub-helper3 {m = m} {n = n} wf 
  ... | result = weakening-wf-var-n result
  wf-TTSub-helper3 {m = Z} {n = Z} {Γ = TVar, Γ} WFVarZ = WFVarZ
  wf-TTSub-helper3 {m = Z} {n = 1+ n} {Γ = TVar, Γ} WFVarZ = WFVarS (wf-TTSub-helper3 {m = Z} {n = n} WFVarZ)
  wf-TTSub-helper3 {m = 1+ m} {n = n} {Γ = TVar, Γ} WFVarZ rewrite extend-tvar-comm n Γ = WFVarZ
  wf-TTSub-helper3 {m = Z} {n = Z} {Γ = TVar, Γ} (WFVarS wf) = WFVarS wf
  wf-TTSub-helper3 {m = Z} {n = 1+ n} {Γ = TVar, Γ} (WFVarS wf) = WFVarS (wf-TTSub-helper3 {m = Z} {n = n} (WFVarS wf))
  wf-TTSub-helper3 {m = 1+ m} {n = Z} {Γ = TVar, Γ} (WFVarS wf) = WFVarS (wf-TTSub-helper3 {m = m} {n = Z} wf)
  wf-TTSub-helper3 {m = 1+ m} {n = 1+ n} {Γ = TVar, Γ} (WFVarS wf) with wf-TTSub-helper3 {m = m} {n = 1+ n} wf 
  ... | result rewrite sym (extend-tvar-comm n Γ) = WFVarS result
  wf-TTSub-helper3 {m = m} {n = n} {Γ = Γ} WFBase = WFBase
  wf-TTSub-helper3 {m = m} {n = n} {Γ = Γ} WFHole = WFHole
  wf-TTSub-helper3 {m = m} {n = n} {Γ = Γ} (WFArr wf wf₁) = WFArr (wf-TTSub-helper3 wf) (wf-TTSub-helper3 wf₁)
  wf-TTSub-helper3 {m = m} {n = n} {Γ = Γ} (WFForall wf) with wf-TTSub-helper3 {m = 1+ m} {n = n} wf
  ... | result rewrite extend-tvar-comm n Γ = WFForall result 

  wf-TTSub-helper : ∀{Γ n τ1 τ2} → (Γ ⊢ τ1 wf) → (ctx-extend-tvars (1+ n) Γ) ⊢ τ2 wf → ((ctx-extend-tvars n Γ) ⊢ TTSub n τ1 τ2 wf)
  wf-TTSub-helper wf1 WFBase = WFBase
  wf-TTSub-helper wf1 WFHole = WFHole
  wf-TTSub-helper wf1 (WFArr wf2 wf3) = WFArr (wf-TTSub-helper wf1 wf2) (wf-TTSub-helper wf1 wf3)
  wf-TTSub-helper {Γ = ∅} {n = Z} {τ1 = τ1} wf1 WFVarZ rewrite ↓↑-invert {Z} {Z} {τ1} rewrite ↑Z Z τ1 = wf1
  wf-TTSub-helper {n = 1+ n} wf1 WFVarZ = WFVarZ 
  wf-TTSub-helper {Γ = τ , Γ} {n = Z} {τ1 = τ1} wf1 WFVarZ rewrite ↓↑-invert {Z} {Z} {τ1} rewrite ↑Z Z τ1 = wf1
  wf-TTSub-helper {Γ = TVar, Γ} {n = Z} {τ1 = τ1} wf1 WFVarZ rewrite ↓↑-invert {Z} {Z} {τ1} rewrite ↑Z Z τ1 = wf1
  wf-TTSub-helper {n = Z} wf1 (WFVarS wf2) = wf2
  wf-TTSub-helper {n = 1+ n} wf1 (WFVarS {n = m} wf2) with natEQ n m 
  wf-TTSub-helper {Γ = Γ} {1+ n} {τ1 = τ1} wf1 (WFVarS {n = m} wf2) | Inl refl = wf-TTSub-helper3 {m = Z} {n = 1+ n} wf1
  wf-TTSub-helper {n = 1+ n} wf1 (WFVarS {n = m} wf2) | Inr neq = wf-TTSub-helper2 neq wf2
  wf-TTSub-helper {Γ = Γ} {n = n} {τ1 = τ1} wf1 (WFForall wf2) with (↑compose Z (1+ n) τ1)
  ... | eq rewrite eq = WFForall (wf-TTSub-helper wf1 wf2) 

  wf-TTSub : ∀{Γ τ1 τ2} → (Γ ⊢ τ1 wf) → ((TVar, Γ) ⊢ τ2 wf) → (Γ ⊢ (TTSub Z τ1 τ2) wf)
  wf-TTSub {Γ = Γ} {τ1 = τ1} wf1 WFVarZ rewrite ↓↑-invert {Z} {Z} {τ1} rewrite ↑Z Z τ1 = wf1
  wf-TTSub wf1 (WFVarS wf2) = wf2
  wf-TTSub wf1 WFBase = WFBase
  wf-TTSub wf1 WFHole = WFHole
  wf-TTSub wf1 (WFArr wf2 wf3) = WFArr (wf-TTSub wf1 wf2) (wf-TTSub wf1 wf3)
  wf-TTSub {τ1 = τ1} wf1 (WFForall wf2) rewrite ↑compose Z 1 τ1 = WFForall (wf-TTSub-helper wf1 wf2)

  ~TTSub-helper : ∀{n Γ τ1 τ2 τ3} → (ctx-extend-tvars (1+ n) Γ) ⊢ τ2 wf → (ctx-extend-tvars (1+ n) Γ) ⊢ τ3 wf → τ2 ~ τ3 → TTSub n τ1 τ2 ~ TTSub n τ1 τ3
  ~TTSub-helper wf2 wf3 ConsistBase = ConsistBase
  ~TTSub-helper wf2 wf3 ConsistVar = ~refl
  ~TTSub-helper wf2 wf3 ConsistHole1 = ConsistHole1
  ~TTSub-helper wf2 wf3 ConsistHole2 = ConsistHole2 
  ~TTSub-helper (WFArr wf2 wf3) (WFArr wf4 wf5) (ConsistArr con1 con2) = ConsistArr (~TTSub-helper wf2 wf4 con1) (~TTSub-helper wf3 wf5 con2)
  ~TTSub-helper {n = n} {τ1 = τ1} (WFForall wf2) (WFForall wf3) (ConsistForall con) with ↑compose Z (1+ n) τ1
  ...| eq rewrite eq = ConsistForall (~TTSub-helper wf2 wf3 con)

  ~TTSub : ∀ {Γ τ1 τ2 τ3} → (TVar, Γ) ⊢ τ2 wf → (TVar, Γ) ⊢ τ3 wf → τ2 ~ τ3 → TTSub Z τ1 τ2 ~ TTSub Z τ1 τ3
  ~TTSub wf2 wf3 con = ~TTSub-helper wf2 wf3 con