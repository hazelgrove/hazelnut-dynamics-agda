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
open import debruijn.debruijn-lemmas-subst
open import debruijn.debruijn-lemmas-wf

module debruijn.debruijn-typing-subst where

  -- TtSub section

  -- inctx-sub : ∀ {n m Γ τ1 τ2} → 
  --   (n , τ2 ∈ Γ) → 
  --   n , (TTSub m τ1 τ2) ∈ (TCtxSub m τ1 Γ)
  -- inctx-sub InCtxZ = InCtxZ
  -- inctx-sub (InCtx1+ inctx) = InCtx1+ (inctx-sub inctx)

  -- -- helper-weaken : ∀{Θ n τ} → Γ ⊢ τ wf → 1+ (n nat+ Θ) ⊢ τ wf
  -- -- helper-weaken {Θ = Θ} {n = n} wf with weakening-wf-var-n {Θ = 1+ Θ} {n = n} wf
  -- -- ... | result rewrite nat+1+ n Θ = result

  -- wt-TtSub-helper : ∀{Θ Γ d n τ1 τ2} →
  --   (1+ (n nat+ Θ) ⊢ Γ ctxwf) → 
  --   (Θ ⊢ τ1 wf) → 
  --   (1+ (n nat+ Θ) , Γ ⊢ d :: τ2) → 
  --   ((n nat+ Θ) , TCtxSub n τ1 Γ ⊢ TtSub n τ1 d :: TTSub n τ1 τ2)
  -- wt-TtSub-helper ctxwf wf TAConst = TAConst
  -- wt-TtSub-helper ctxwf wf (TAVar inctx) = TAVar (inctx-sub inctx)
  -- wt-TtSub-helper {n = Z} ctxwf wf1 (TALam wf2 wt) = TALam (wf-TTSub wf1 wf2) (wt-TtSub-helper (CtxWFVar wf2 ctxwf) wf1 wt)
  -- wt-TtSub-helper {Θ = Θ} {n = n} ctxwf wf1 (TALam wf2 wt) with wt-TtSub-helper {n = n} (CtxWFTVar ctxwf) wf1 wt
  -- ... | wt2 rewrite nat+1+ n Θ = TALam (wf-TTSub-helper wf1 wf2) wt2
  -- wt-TtSub-helper {Θ = Θ} {n = n} {τ1 = τ1} ctxwf wf (TATLam wt) with wt-TtSub-helper {Θ = Θ} {n = 1+ n} {!   !} wf wt
  -- ... | result rewrite sym (↑compose Z (1+ n) τ1) rewrite nat+1+ n Θ = TATLam {! result  !}
  -- wt-TtSub-helper ctxwf wf (TAAp wt1 wt2) = TAAp (wt-TtSub-helper ctxwf wf wt1) (wt-TtSub-helper ctxwf wf wt2)
  -- wt-TtSub-helper {Θ = Θ} {n = n} {τ1 = τ1} ctxwf wf (TATAp {τ1 = τ2} {τ2 = τ3} x wt refl) with ? --SubSub {n = n} {τ1 = τ1} {τ2 = τ2} {τ3 = τ3} 
  -- ... | result rewrite sym (↑compose Z (1+ n) τ1) = TATAp (wf-TTSub-helper wf x) (wt-TtSub-helper ctxwf wf wt) (sym result)
  -- wt-TtSub-helper ctxwf wf (TAEHole x) = TAEHole (wf-TTSub-helper wf x)
  -- wt-TtSub-helper ctxwf wf (TANEHole x wt) = TANEHole (wf-TTSub-helper wf x) (wt-TtSub-helper ctxwf wf wt)
  -- wt-TtSub-helper {n = n} ctxwf wf (TACast wt x x₁) = TACast (wt-TtSub-helper ctxwf wf wt) (wf-TTSub-helper wf x) (~TTSub-helper (weakening-wf-var-n {n = n} (wf-ta ctxwf wt)) (weakening-wf-var-n x) x₁) 
  -- wt-TtSub-helper ctxwf wf (TAFailedCast wt GBase GBase incon) = abort (incon ConsistBase)
  -- wt-TtSub-helper ctxwf wf (TAFailedCast wt GArr GArr incon) = abort (incon (ConsistArr ConsistHole1 ConsistHole1))
  -- wt-TtSub-helper ctxwf wf (TAFailedCast wt GForall GForall incon) = abort (incon (ConsistForall ConsistHole1))
  -- wt-TtSub-helper ctxwf wf (TAFailedCast wt GBase GArr incon) = TAFailedCast (wt-TtSub-helper ctxwf wf wt) GBase GArr incon
  -- wt-TtSub-helper ctxwf wf (TAFailedCast wt GBase GForall incon) = TAFailedCast (wt-TtSub-helper ctxwf wf wt) GBase GForall incon
  -- wt-TtSub-helper ctxwf wf (TAFailedCast wt GArr GBase incon) = TAFailedCast (wt-TtSub-helper ctxwf wf wt) GArr GBase incon
  -- wt-TtSub-helper ctxwf wf (TAFailedCast wt GArr GForall incon) = TAFailedCast (wt-TtSub-helper ctxwf wf wt) GArr GForall incon
  -- wt-TtSub-helper ctxwf wf (TAFailedCast wt GForall GBase incon) = TAFailedCast (wt-TtSub-helper ctxwf wf wt) GForall GBase incon
  -- wt-TtSub-helper ctxwf wf (TAFailedCast wt GForall GArr incon) = TAFailedCast (wt-TtSub-helper ctxwf wf wt) GForall GArr incon

  -- wt-TtSub : ∀{Θ Γ d τ1 τ2} →
  --   (1+ Θ ⊢ Γ ctxwf) → 
  --   (Θ ⊢ τ1 wf) → 
  --   (1+ Θ , Γ ⊢ d :: τ2) → 
  --   (Θ , TCtxSub Z τ1 Γ ⊢ TtSub Z τ1 d :: TTSub Z τ1 τ2)
  -- wt-TtSub ctxwf wf wt = wt-TtSub-helper ctxwf wf wt

  sub-shift : (t m : Nat) → (τ' τ : htyp) → ↑ t 1 (TTSub (t nat+ m) τ' τ) == TTSub (1+ (t nat+ m)) τ' (↑ t 1 τ)
  sub-shift t m τ' b = refl
  sub-shift t m τ' (T x) = {!   !}
  -- with natEQ (t nat+ m) x 
  -- ... | Inl refl = {!   !} 
  -- ... | Inr neq = {!   !}
  sub-shift t m τ' ⦇-⦈ = refl
  sub-shift t m τ' (τ ==> τ₁) rewrite sub-shift t m τ' τ rewrite sub-shift t m τ' τ₁ = refl
  sub-shift t m τ' (·∀ τ) rewrite sub-shift (1+ t) m τ' τ = refl

  -- note: not true as written. either induces a shift on tau1, or must assume tau1 has no fvs (which is true, where this lemmas is used)
  inctx-sub : ∀ {n m x Γ τ1 τ2} → 
    context-counter Γ n m → 
    x , τ2 ∈ (Γ ctx+ (TVar, ∅)) → 
    x , TTSub m τ1 τ2 ∈ TCtxSub m τ1 Γ
  inctx-sub CtxCtEmpty (InCtxSkip ())
  inctx-sub {.(1+ _)} {m} {.Z} {x₁ , Γ} (CtxCtVar ctxct) InCtxZ = InCtxZ
  inctx-sub {.(1+ _)} {m} {.(1+ _)} {x₁ , Γ} (CtxCtVar ctxct) (InCtx1+ inctx) = InCtx1+ (inctx-sub ctxct inctx)
  inctx-sub {n} {(1+ m)} {x} {TVar, Γ} {τ1} (CtxCtTVar ctxct) (InCtxSkip inctx) with InCtxSkip (inctx-sub {n} {m} {x} {Γ} {τ1} ctxct inctx)
  ... | thing = {!  ?  !}

  -- example-gamma : ctx
  -- example-gamma = (TVar, (T 3 , (T 2 , (T 2 , (T 1 , (T Z , (TVar, (TVar, (TVar, (TVar, ∅))))))))))

  -- example-gamma-wf : ⊢ example-gamma ctxwf
  -- example-gamma-wf = CtxWFTVar (CtxWFVar (WFSkip  (WFSkip (WFSkip (WFSkip (WFVarS (WFVarS (WFVarS WFVarZ))))))) (CtxWFVar (WFSkip (WFSkip (WFSkip (WFVarS (WFVarS WFVarZ)))))  (CtxWFVar (WFSkip (WFSkip (WFVarS (WFVarS WFVarZ))))    (CtxWFVar (WFSkip (WFVarS WFVarZ))     (CtxWFVar WFVarZ      (CtxWFTVar (CtxWFTVar (CtxWFTVar (CtxWFTVar CtxWFEmpty)))))))))

  -- example-gamma-ct : context-counter example-gamma 5 5 
  -- example-gamma-ct = CtxCtTVar (CtxCtVar  (CtxCtVar   (CtxCtVar    (CtxCtVar     (CtxCtVar      (CtxCtTVar (CtxCtTVar (CtxCtTVar (CtxCtTVar CtxCtEmpty)))))))))

  -- example-gamma-inctx : 3 , T 2 ∈ (example-gamma ctx+ (TVar, ∅))
  -- example-gamma-inctx = InCtxSkip (InCtx1+ (InCtx1+ (InCtx1+ InCtxZ)))

  -- example-gamma-inctx' : 3 , T 2 ∈ TCtxSub 5 b example-gamma 
  -- example-gamma-inctx' = InCtxSkip (InCtx1+ (InCtx1+ (InCtx1+ InCtxZ)))

  convenient-wf-subst : ∀{Γ m τ1 τ2} → ∅ ⊢ τ1 wf → (Γ ctx+ (TVar, ∅)) ⊢ τ2 wf → TCtxSub m τ1 Γ ⊢ TTSub m τ1 τ2 wf
  convenient-wf-subst wf1 wf2 = {!   !} --wf-TCtxSub (wf-TTSub (weakening-wf wf1) (wf-swap-tvar {! wf2  !}))

  wt-TtSub-helper : ∀{Γ n m d τ1 τ2} →
    (⊢ (Γ ctx+ (TVar, ∅)) ctxwf) →
    (context-counter Γ n m) → 
    (∅ ⊢ τ1 wf) → 
    ((Γ ctx+ (TVar, ∅)) ⊢ d :: τ2) → 
    (TCtxSub m τ1 Γ ⊢ TtSub m τ1 d :: TTSub m τ1 τ2)
  wt-TtSub-helper ctxwf ctxct wf TAConst = TAConst
  wt-TtSub-helper ctxwf ctxct wf (TAAp wt wt₁) = TAAp (wt-TtSub-helper ctxwf ctxct wf wt) (wt-TtSub-helper ctxwf ctxct wf wt₁)
  wt-TtSub-helper ctxwf ctxct wf (TATAp x wt x₁) = TATAp (convenient-wf-subst wf x) (wt-TtSub-helper ctxwf ctxct wf wt) {!   !}
  wt-TtSub-helper ctxwf ctxct wf TAEHole = TAEHole
  wt-TtSub-helper ctxwf ctxct wf (TANEHole wt) = TANEHole (wt-TtSub-helper ctxwf ctxct wf wt)
  wt-TtSub-helper {m = m} ctxwf ctxct wf (TACast wt x x₁) = TACast (wt-TtSub-helper ctxwf ctxct wf wt) (convenient-wf-subst wf x) {!   !}
  wt-TtSub-helper ctxwf ctxct wf (TALam x wt) = TALam (convenient-wf-subst wf x) (wt-TtSub-helper (CtxWFVar x ctxwf) (CtxCtVar ctxct) wf wt)
  wt-TtSub-helper ctxwf ctxct wf (TATLam wt) = TATLam (wt-TtSub-helper (CtxWFTVar ctxwf) (CtxCtTVar ctxct) wf wt)
  wt-TtSub-helper ctxwf ctxct wf (TAVar x) = TAVar {!   !} --(inctx-sub ctxct x)
  wt-TtSub-helper ctxwf ctxct wf (TAFailedCast wt GBase GBase incon) = abort (incon ConsistBase)
  wt-TtSub-helper ctxwf ctxct wf (TAFailedCast wt GArr GArr incon) = abort (incon (ConsistArr ConsistHole1 ConsistHole1))
  wt-TtSub-helper ctxwf ctxct wf (TAFailedCast wt GForall GForall incon) = abort (incon (ConsistForall ConsistHole1))
  wt-TtSub-helper ctxwf ctxct wf (TAFailedCast wt GBase GArr incon) = TAFailedCast (wt-TtSub-helper ctxwf ctxct wf wt) GBase GArr incon
  wt-TtSub-helper ctxwf ctxct wf (TAFailedCast wt GBase GForall incon) = TAFailedCast (wt-TtSub-helper ctxwf ctxct wf wt) GBase GForall incon
  wt-TtSub-helper ctxwf ctxct wf (TAFailedCast wt GArr GBase incon) = TAFailedCast (wt-TtSub-helper ctxwf ctxct wf wt) GArr GBase incon
  wt-TtSub-helper ctxwf ctxct wf (TAFailedCast wt GArr GForall incon) = TAFailedCast (wt-TtSub-helper ctxwf ctxct wf wt) GArr GForall incon
  wt-TtSub-helper ctxwf ctxct wf (TAFailedCast wt GForall GBase incon) = TAFailedCast (wt-TtSub-helper ctxwf ctxct wf wt) GForall GBase incon
  wt-TtSub-helper ctxwf ctxct wf (TAFailedCast wt GForall GArr incon) = TAFailedCast (wt-TtSub-helper ctxwf ctxct wf wt) GForall GArr incon

  wt-TtSub : ∀{d τ1 τ2} →
    ∅ ⊢ τ1 wf → 
    (TVar, ∅) ⊢ d :: τ2 →
    ∅ ⊢ TtSub Z τ1 d :: TTSub Z τ1 τ2
  wt-TtSub wf wt = wt-TtSub-helper (CtxWFTVar CtxWFEmpty) CtxCtEmpty wf wt

  no-fvs-lemma-type : ∀{Γ t1 t2 τ} → (m : Nat) → context-counter Γ t1 t2 → Γ ⊢ τ wf → ↑ t2 m τ == τ
  no-fvs-lemma-type m (CtxCtVar ctxct) (WFSkip wf) = no-fvs-lemma-type m ctxct wf 
  no-fvs-lemma-type m (CtxCtTVar ctxct) WFVarZ = refl
  no-fvs-lemma-type m (CtxCtTVar ctxct) (WFVarS wf) with h1 (no-fvs-lemma-type m ctxct wf) 
    where 
      h1 : ∀{x1 x2} → T x1 == T x2 → x1 == x2
      h1 refl = refl
  ... | eq rewrite eq = refl
  no-fvs-lemma-type m ctxct WFBase = refl
  no-fvs-lemma-type m ctxct WFHole = refl
  no-fvs-lemma-type m ctxct (WFArr wf wf₁) rewrite no-fvs-lemma-type m ctxct wf rewrite no-fvs-lemma-type m ctxct wf₁ = refl
  no-fvs-lemma-type m ctxct (WFForall wf) rewrite no-fvs-lemma-type m (CtxCtTVar ctxct) wf = refl
  
  inc-var-eq : ∀{x1 x2 : Nat} → (eq : Prelude._==_ {A = ihexp} (X x1) (X x2)) → (Prelude._==_ {A = ihexp} (X (1+ x1)) (X (1+ x2))) 
  inc-var-eq refl = refl

  no-fvs-lemma : ∀{Γ t1 t2 d τ} → (n m : Nat) → ⊢ Γ ctxwf → context-counter Γ t1 t2 → Γ ⊢ d :: τ → ↑d t1 n t2 m d == d
  no-fvs-lemma n m ctxwf ctxct TAConst = refl
  no-fvs-lemma n m ctxwf (CtxCtVar ctxct) (TAVar InCtxZ) = refl
  no-fvs-lemma n m (CtxWFVar x₁ ctxwf) (CtxCtVar ctxct) (TAVar (InCtx1+ x)) = inc-var-eq (no-fvs-lemma n m ctxwf ctxct (TAVar x))
  no-fvs-lemma n m (CtxWFTVar ctxwf) (CtxCtTVar ctxct) (TAVar (InCtxSkip x)) = no-fvs-lemma n m ctxwf ctxct (TAVar x) 
  no-fvs-lemma n m ctxwf ctxct (TALam x wt) rewrite no-fvs-lemma-type m ctxct x rewrite no-fvs-lemma n m (CtxWFVar x ctxwf) (CtxCtVar ctxct) wt = refl
  no-fvs-lemma n m ctxwf ctxct (TATLam wt) rewrite no-fvs-lemma n m (CtxWFTVar ctxwf) (CtxCtTVar ctxct) wt = refl
  no-fvs-lemma n m ctxwf ctxct (TAAp wt wt₁) rewrite no-fvs-lemma n m ctxwf ctxct wt rewrite no-fvs-lemma n m ctxwf ctxct wt₁ = refl
  no-fvs-lemma n m ctxwf ctxct (TATAp x wt x₁) rewrite no-fvs-lemma-type m ctxct x rewrite no-fvs-lemma n m ctxwf ctxct wt = refl
  no-fvs-lemma n m ctxwf ctxct TAEHole = refl
  no-fvs-lemma n m ctxwf ctxct (TANEHole wt) rewrite no-fvs-lemma n m ctxwf ctxct wt = refl
  no-fvs-lemma n m ctxwf ctxct (TACast wt x x₁) rewrite no-fvs-lemma-type m ctxct x rewrite no-fvs-lemma-type m ctxct (wf-ta ctxwf wt) rewrite no-fvs-lemma n m ctxwf ctxct wt = refl
  no-fvs-lemma n m ctxwf ctxct (TAFailedCast wt x x₁ x₂) rewrite no-fvs-lemma n m ctxwf ctxct wt rewrite no-fvs-lemma-type m ctxct (wf-gnd x) rewrite no-fvs-lemma-type m ctxct (wf-gnd x₁) = refl

  inctx-count1 : ∀{Γ n m τ1 τ2} → context-counter Γ n m → n , τ2 ∈ (Γ ctx+ (τ1 , ∅)) → τ2 == ↑ 0 m τ1
  inctx-count1 {τ1 = τ1} CtxCtEmpty InCtxZ rewrite ↑Z Z τ1 = refl
  inctx-count1 (CtxCtVar ctxct) (InCtx1+ inctx) = inctx-count1 ctxct inctx
  inctx-count1 {m = 1+ m} {τ1 = τ1} (CtxCtTVar ctxct) (InCtxSkip inctx) rewrite inctx-count1 ctxct inctx rewrite ↑compose Z m τ1 = refl

  inctx-count2 : ∀{Γ n m x τ1 τ2} → x ≠ n → context-counter Γ n m → x , τ2 ∈ (Γ ctx+ (τ1 , ∅)) → ↓Nat n 1 x , τ2 ∈ Γ
  inctx-count2 neq CtxCtEmpty InCtxZ = abort (neq refl)
  inctx-count2 neq (CtxCtVar ctxct) InCtxZ = InCtxZ
  inctx-count2 neq (CtxCtVar ctxct) (InCtx1+ inctx) = InCtx1+ (inctx-count2 (\{refl → neq refl}) ctxct inctx)
  inctx-count2 neq (CtxCtTVar ctxct) (InCtxSkip inctx) = InCtxSkip (inctx-count2 neq ctxct inctx)

  wt-ttSub-helper : ∀{Γ n m d1 d2 τ1 τ2} →
    (⊢ Γ ctxwf) →
    (context-counter Γ n m) → 
    (∅ ⊢ d1 :: τ1) → 
    ((Γ ctx+ (τ1 , ∅)) ⊢ d2 :: τ2) → 
    (Γ ⊢ ttSub n m d1 d2 :: τ2)
  wt-ttSub-helper ctxwf ctxct wt1 TAConst = TAConst
  wt-ttSub-helper ctxwf ctxct wt1 (TAAp wt2 wt3) = TAAp (wt-ttSub-helper ctxwf ctxct wt1 wt2) (wt-ttSub-helper ctxwf ctxct wt1 wt3)
  wt-ttSub-helper ctxwf ctxct wt1 (TATAp x wt2 x₁) = TATAp (strengthen-wf-var-reverse x) (wt-ttSub-helper ctxwf ctxct wt1 wt2) x₁
  wt-ttSub-helper ctxwf ctxct wt1 TAEHole = TAEHole 
  wt-ttSub-helper ctxwf ctxct wt1 (TANEHole wt2) = TANEHole (wt-ttSub-helper ctxwf ctxct wt1 wt2)
  wt-ttSub-helper ctxwf ctxct wt1 (TACast wt2 x x₁) = TACast (wt-ttSub-helper ctxwf ctxct wt1 wt2) (strengthen-wf-var-reverse x) x₁
  wt-ttSub-helper ctxwf ctxct wt1 (TAFailedCast wt2 x x₁ x₂) = TAFailedCast (wt-ttSub-helper ctxwf ctxct wt1 wt2) x x₁ x₂
  wt-ttSub-helper {Γ} {n} {m} {d1} ctxwf ctxct wt1 (TALam {τ1 = τ} {d = d} x wt2) = TALam (strengthen-wf-var-reverse x) (wt-ttSub-helper {Γ = (τ , Γ)} (CtxWFVar (strengthen-wf-var-reverse x) ctxwf) (CtxCtVar ctxct) wt1 wt2)
  wt-ttSub-helper {Γ} {n} {m} {d1} ctxwf ctxct wt1 (TATLam {d = d} wt2) = TATLam (wt-ttSub-helper {Γ = (TVar, Γ)} (CtxWFTVar ctxwf) (CtxCtTVar ctxct) wt1 wt2)
  wt-ttSub-helper {Γ} {n} {m} ctxwf ctxct wt1 (TAVar {n = x} inctx) with natEQ x n 
  wt-ttSub-helper {Γ} {n} {m} {d1} ctxwf ctxct wt1 (TAVar inctx) | Inl refl with wf-ta CtxWFEmpty wt1  
  ... | wf rewrite no-fvs-lemma n m CtxWFEmpty CtxCtEmpty wt1 rewrite inctx-count1 ctxct inctx rewrite no-fvs-lemma-type m CtxCtEmpty wf = weakening-wt wt1
  wt-ttSub-helper {Γ} {n} {m} ctxwf ctxct wt1 (TAVar {n = x} inctx) | Inr neq = TAVar (inctx-count2 neq ctxct inctx)
  
  wt-ttSub : ∀{d1 d2 τ1 τ2} →
    (∅ ⊢ d1 :: τ1) → 
    ((τ1 , ∅) ⊢ d2 :: τ2) → 
    (∅ ⊢ ttSub Z Z d1 d2 :: τ2)
  wt-ttSub = wt-ttSub-helper CtxWFEmpty CtxCtEmpty
     