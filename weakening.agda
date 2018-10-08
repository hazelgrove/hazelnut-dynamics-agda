open import Nat
open import Prelude
open import List
open import core
open import contexts
open import lemmas-disjointness
open import exchange

-- this module contains all the proofs of different weakening structural
-- properties that we use for the hypothetical judgements
module weakening where
  mutual
    weaken-subst-Δ : ∀{Δ1 Δ2 Γ σ Γ'} → Δ1 ## Δ2 → Δ1 , Γ ⊢ σ :s: Γ' → (Δ1 ∪ Δ2) , Γ ⊢ σ :s: Γ'
    weaken-subst-Δ disj (STAId x) = STAId x
    weaken-subst-Δ disj (STASubst subst x) = STASubst (weaken-subst-Δ disj subst) (weaken-ta-Δ1 disj x)

    weaken-ta-Δ1 : ∀{Δ1 Δ2 Γ d τ} → Δ1 ## Δ2 → Δ1 , Γ ⊢ d :: τ → (Δ1 ∪ Δ2) , Γ ⊢ d :: τ
    weaken-ta-Δ1 disj TAConst = TAConst
    weaken-ta-Δ1 disj (TAVar x₁) = TAVar x₁
    weaken-ta-Δ1 disj (TALam x₁ wt) = TALam x₁ (weaken-ta-Δ1 disj wt)
    weaken-ta-Δ1 disj (TAAp wt wt₁) = TAAp (weaken-ta-Δ1 disj wt) (weaken-ta-Δ1 disj wt₁)
    weaken-ta-Δ1 {Δ1} {Δ2} {Γ} disj (TAEHole {u = u} {Γ' = Γ'} x x₁) = TAEHole (x∈∪l Δ1 Δ2 u _ x ) (weaken-subst-Δ disj x₁)
    weaken-ta-Δ1 {Δ1} {Δ2} {Γ} disj (TANEHole {Γ' = Γ'} {u = u} x wt x₁) = TANEHole (x∈∪l Δ1 Δ2 u _ x) (weaken-ta-Δ1 disj wt) (weaken-subst-Δ disj x₁)
    weaken-ta-Δ1 disj (TACast wt x) = TACast (weaken-ta-Δ1 disj wt) x
    weaken-ta-Δ1 disj (TAFailedCast wt x x₁ x₂) = TAFailedCast (weaken-ta-Δ1 disj wt) x x₁ x₂

  weaken-ta-Δ2 : ∀{Δ1 Δ2 Γ d τ} → Δ1 ## Δ2 → Δ2 , Γ ⊢ d :: τ → (Δ1 ∪ Δ2) , Γ ⊢ d :: τ
  weaken-ta-Δ2 {Δ1} {Δ2} {Γ} {d} {τ} disj D = tr (λ q → q , Γ ⊢ d :: τ) (∪comm Δ2 Δ1 (##-comm disj)) (weaken-ta-Δ1 (##-comm disj) D)


  mutual
    weaken-synth : ∀{ x Γ e τ τ'} → freshh x e → Γ ⊢ e => τ → (Γ ,, (x , τ')) ⊢ e => τ
    weaken-synth FRHConst SConst = SConst
    weaken-synth (FRHAsc frsh) (SAsc x₁) = SAsc (weaken-ana frsh x₁)
    weaken-synth {Γ = Γ} (FRHVar {x = x} x₁) (SVar {x = y} x₂) = SVar (x∈∪l Γ (■(x , _)) y _  x₂)
    weaken-synth {Γ = Γ} (FRHLam2 x₁ frsh) (SLam x₂ wt) =
                    SLam (apart-extend1 Γ (flip x₁) x₂)
                         (exchange-synth {Γ = Γ} (flip x₁) ((weaken-synth frsh wt)))
    weaken-synth FRHEHole SEHole = SEHole
    weaken-synth (FRHNEHole frsh) (SNEHole x₁ wt) = SNEHole x₁ (weaken-synth frsh wt)
    weaken-synth (FRHAp frsh frsh₁) (SAp x₁ wt x₂ x₃) = SAp x₁ (weaken-synth frsh wt) x₂ (weaken-ana frsh₁ x₃)

    weaken-ana : ∀{x Γ e τ τ'} → freshh x e → Γ ⊢ e <= τ → (Γ ,, (x , τ')) ⊢ e <= τ
    weaken-ana frsh (ASubsume x₁ x₂) = ASubsume (weaken-synth frsh x₁) x₂
    weaken-ana {Γ = Γ} (FRHLam1 neq frsh) (ALam x₂ x₃ wt) =
                     ALam (apart-extend1 Γ (flip neq) x₂)
                          x₃
                          (exchange-ana {Γ = Γ} (flip neq) (weaken-ana frsh wt))
