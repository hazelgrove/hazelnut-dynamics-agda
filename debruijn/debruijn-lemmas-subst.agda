-- {-# OPTIONS --allow-unsolved-metas #-}

open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
open import debruijn.debruijn-core-subst
open import debruijn.debruijn-core
open import debruijn.debruijn-weakening
open import debruijn.debruijn-lemmas-index
open import debruijn.debruijn-lemmas-ctx
open import debruijn.debruijn-lemmas-consistency
open import debruijn.debruijn-lemmas-meet

module debruijn.debruijn-lemmas-subst where

  TTSubCorrect : ∀{n τ1 τ2} → TTSub' n τ1 τ2 == TTSub n τ1 τ2
  TTSubCorrect {n} {τ1} {b} = refl
  TTSubCorrect {n} {τ1} {⦇-⦈} = refl
  TTSubCorrect {n} {τ1} {T x} with natEQ n x 
  ... | Inl refl = refl 
  ... | Inr neq = refl
  TTSubCorrect {n} {τ1} {τ2 ==> τ3} rewrite TTSubCorrect {n} {τ1} {τ2} rewrite TTSubCorrect {n} {τ1} {τ3} = refl
  TTSubCorrect {n} {τ1} {·∀ τ2} rewrite ↑compose 0 (1+ n) τ1 rewrite TTSubCorrect {1+ n} {τ1} {τ2} = refl

  TtSubCorrect : ∀{n τ d} → TtSub' n τ d == TtSub n τ d
  TtSubCorrect {n} {τ} {c} = refl
  TtSubCorrect {n} {τ} {X x} = refl
  TtSubCorrect {n} {τ} {⦇-⦈⟨ x ⟩} rewrite TTSubCorrect {n} {τ} {x} = refl
  TtSubCorrect {n} {τ} {⦇⌜ d ⌟⦈⟨ x ⟩} rewrite TTSubCorrect {n} {τ} {x} rewrite TtSubCorrect {n} {τ} {d} = refl
  TtSubCorrect {n} {τ} {d ∘ d₁} rewrite TtSubCorrect {n} {τ} {d} rewrite TtSubCorrect {n} {τ} {d₁} = refl
  TtSubCorrect {n} {τ} {d < x >} rewrite TTSubCorrect {n} {τ} {x} rewrite TtSubCorrect {n} {τ} {d} = refl
  TtSubCorrect {n} {τ} {d ⟨ x ⇒ x₁ ⟩} rewrite TTSubCorrect {n} {τ} {x} rewrite TTSubCorrect {n} {τ} {x₁} rewrite TtSubCorrect {n} {τ} {d} = refl
  TtSubCorrect {n} {τ} {d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩} rewrite TTSubCorrect {n} {τ} {x} rewrite TTSubCorrect {n} {τ} {x₁} rewrite TtSubCorrect {n} {τ} {d} = refl
  TtSubCorrect {n} {τ} {·λ[ x ] d} rewrite TTSubCorrect {n} {τ} {x} rewrite TtSubCorrect {n} {τ} {d} = refl
  TtSubCorrect {n} {τ} {·Λ d} rewrite ↑compose 0 (1+ n) τ rewrite TtSubCorrect {1+ n} {τ} {d} = refl

  ttSubCorrect : ∀{n m d1 d2} → ttSub' n m d1 d2 == ttSub n m d1 d2
  ttSubCorrect {n} {m} {d1} {c} = refl
  ttSubCorrect {n} {m} {d1} {⦇-⦈⟨ x ⟩} = refl
  ttSubCorrect {n} {m} {d1} {⦇⌜ d2 ⌟⦈⟨ x ⟩} rewrite ttSubCorrect {n} {m} {d1} {d2} = refl
  ttSubCorrect {n} {m} {d1} {d2 ∘ d3} rewrite ttSubCorrect {n} {m} {d1} {d2} rewrite ttSubCorrect {n} {m} {d1} {d3} = refl
  ttSubCorrect {n} {m} {d1} {d2 < x >} rewrite ttSubCorrect {n} {m} {d1} {d2} = refl
  ttSubCorrect {n} {m} {d1} {d2 ⟨ x ⇒ x₁ ⟩} rewrite ttSubCorrect {n} {m} {d1} {d2} = refl
  ttSubCorrect {n} {m} {d1} {d2 ⟨ x ⇒⦇-⦈⇏ x₁ ⟩} rewrite ttSubCorrect {n} {m} {d1} {d2} = refl
  ttSubCorrect {n} {m} {d1} {·λ[ x ] d2} 
    rewrite ↑d-↑td-comm {1} {m} {Z} {Z} {d = (↑d 0 (1+ n) d1)} 
    rewrite ↑d-compose Z (1+ n) d1
    rewrite ttSubCorrect {1+ n} {m} {d1} {d2} = refl
  ttSubCorrect {n} {m} {d1} {·Λ d2} 
    rewrite ↑td-compose 0 m (↑d 0 (1+ n) d1)
    rewrite ttSubCorrect {n} {1+ m} {d1} {d2} = refl
  ttSubCorrect {n} {m} {d1} {X x} with natEQ x n
  ... | Inr neq = refl
  ... | Inl refl rewrite sym (↑d-↑td-comm {1+ n} {m} {Z} {Z} {d1}) with ↓↑d-invert {x} {Z} {↑td 0 m d1} 
  ... | eq rewrite nat+1+ n Z rewrite nat+Z n rewrite eq = refl

  -- TTSub-shift : ∀{l n m τ1 τ2} → ↑ n m (TTSub l τ1 τ2) == TTSub l (↑ n m τ1) (↑ (1+ n) m τ2) 
  -- TTSub-shift {l} {n} {m} {τ1} {b} = refl
  -- TTSub-shift {l} {n} {m} {τ1} {⦇-⦈} = refl
  -- TTSub-shift {l} {n} {m} {τ1} {τ2 ==> τ3} rewrite TTSub-shift {l} {n} {m} {τ1} {τ2} rewrite TTSub-shift {l} {n} {m} {τ1} {τ3} = refl
  -- TTSub-shift {l} {n} {m} {τ1} {·∀ τ2} rewrite TTSub-shift {1+ l} {1+ n} {m} {τ1} {τ2} = {!   !}
  -- TTSub-shift {l} {n} {m} {τ1} {T x} = {!   !}
      

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

  -- inctx-sub : ∀ {n Γ τ1 τ2} → 
  --   (n , τ2 ∈ Γ) → 
  --   (n , TTSub τ1 τ2 ∈ TCtxSub τ1 Γ)
  -- inctx-sub InCtxZ = InCtxZ
  -- inctx-sub (InCtx1+ inctx) = InCtx1+ (inctx-sub inctx)
  
  -- SubSub-helper : 
  --   (n m : Nat) → 
  --   (τ1 τ2 τ3 : htyp) →
  --   TTSub (m nat+ n) τ1 (TTSub m τ2 τ3) == 
  --   TTSub m (TTSub n τ1 τ2) (TTSub (m nat+ 1+ n) τ1 τ3)
  -- SubSub-helper n m τ1 τ2 b = refl
  -- -- SubSub-helper n m τ1 τ2 (T x) = {!   !}

  -- SubSub-helper n m τ1 τ2 (T x) with natEQ m x
  -- SubSub-helper n m τ1 τ2 (T x) | Inl refl with natEQ (m nat+ 1+ n) m
  -- SubSub-helper n m τ1 τ2 (T x) | Inl refl | Inl eq = abort (h1 m n eq)
  --   where 
  --     h1 : (m n : Nat) → (m nat+ 1+ n) == m → ⊥
  --     h1 Z n () 
  --     h1 (1+ m) n eq = h1 m n (1+inj (m nat+ 1+ n) m eq)
  -- SubSub-helper n m τ1 τ2 (T x) | Inl refl | Inr neq = {!   !}
  -- SubSub-helper n m τ1 τ2 (T x) | Inr neq with natEQ (m nat+ n) (↓Nat m 1 x) | natEQ (m nat+ 1+ n) x
  -- SubSub-helper n m τ1 τ2 (T x) | Inr neq | Inl eq | Inl eq2 = {! eq  !}
  -- SubSub-helper n m τ1 τ2 (T x) | Inr neq | Inl eq | Inr neq2 = {! eq  !}
  -- SubSub-helper n m τ1 τ2 (T x) | Inr neq | Inr neq2 | Inl eq = {!   !} 
  -- SubSub-helper n m τ1 τ2 (T x) | Inr neq | Inr neq2 | Inr neq3 = {!   !} 

  -- SubSub-helper n m τ1 τ2 ⦇-⦈ = refl
  -- SubSub-helper n m τ1 τ2 (τ3 ==> τ4) rewrite SubSub-helper n m τ1 τ2 τ3 rewrite SubSub-helper n m τ1 τ2 τ4 = refl
  -- SubSub-helper n m τ1 τ2 (·∀ τ3) with SubSub-helper n (1+ m) τ1 τ2 τ3 
  -- ... | result rewrite ↑compose Z (m nat+ 1) τ2   
  --   rewrite ↑compose Z (1+ (m nat+ n)) τ1
  --   rewrite ↑compose Z (1+ m) τ2
  --   rewrite ↑compose Z (1+ m) (↓ n 1 (TT[ ↑ 0 (1+ n) τ1 / n ] τ2)) 
  --   rewrite ↑compose Z (1+ (m nat+ 1+ n)) τ1 rewrite result = refl
 
  -- SubSub : ∀{n τ1 τ2 τ3} → 
  --   TTSub n τ1 (TTSub Z τ2 τ3) == 
  --   TTSub Z (TTSub n τ1 τ2) (TTSub (1+ n) τ1 τ3)          
  -- SubSub {n = n} {τ1 = τ1} {τ2 = τ2} {τ3 = τ3} = SubSub-helper n Z τ1 τ2 τ3 