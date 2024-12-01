
open import Prelude
open import Nat
open import core-type
open import core-exp
open import core-subst
open import core

module core-insert where

  data ∀□_~_ : htyp → htyp → Set where 
    PEForall : ∀{τ τ'} →
      (∀□ (TTSub Z ⦇-⦈ τ) ~ τ') → 
      (∀□ (·∀ τ) ~ τ')
    PEHole : ∀{τ'} →
      (∀□ ⦇-⦈ ~ τ')
    PENotMatch : ∀{τ τ'} →
      (τ ~̸ (·∀ ⦇-⦈)) → 
      (τ ~ τ') → 
      (∀□ τ ~ τ')

  -- data _<=_↬_:_ : hexp → htyp → hexp → htyp → Set where 
  --   ITAp : ∀{τ τ'} →
  --     (τ ~ τ') → 
  --     (τ ~ τ') → 
  --     (e <= τ ↬ e : τ)
  --   IMatch : ∀{τ τ'} →
  --     ((e < ⦇-⦈ >) => ? ↬ e' => τ' ~ τ) → 
  --     (e ↬ (e < τ2 >) => τ ~ τ)

    -- bidirectional cast insertion judgements
  mutual
    -- synthesis
    data _⊢_=>_~>_ : (Γ : ctx) (e : hexp) (τ : htyp) (e' : hexp) → Set where
      ISConst : ∀{Γ} → 
        Γ ⊢ c => b ~> c
      ISVar : ∀{Γ x τ} → 
        x , τ ∈ Γ → 
        Γ ⊢ X x => τ ~> X x
      ISLam : ∀{Γ τ1 τ2 e d} →
        Γ ⊢ τ1 wf →
        (τ1 , Γ) ⊢ e => τ2 ~> d →
        Γ ⊢ (·λ[ τ1 ] e) => (τ1 ==> τ2) ~> (·λ[ τ1 ] d)
      ISTLam : ∀{Γ e τ d} → 
        (TVar, Γ) ⊢ e => τ ~> d → 
        Γ ⊢ (·Λ e) => (·∀ τ) ~> (·Λ d)
      ISAp : ∀{Γ e1 d1 e2 d2 τ1 τ1' τ2} →
        Γ ⊢ e1 <= (⦇-⦈ ==> ⦇-⦈) ~> d1 :: (τ1 ==> τ2) →
        Γ ⊢ e2 <= τ1 ~> d2 :: τ1' →
        Γ ⊢ (e1 ∘ e2) => τ2 ~> (d1 ∘ d2)
      ISTAp : ∀{Γ e τ1 τ2 τ3 d} →
        Γ ⊢ τ1 wf →
        Γ ⊢ e <= (·∀ ⦇-⦈) ~> d :: (·∀ τ2) →
        TTSub Z τ1 τ2 == τ3 →
        Γ ⊢ (e < τ1 >) => τ3 ~> (d < τ1 >)
      ISEHole : ∀{Γ} →
        Γ ⊢ ⦇-⦈ => ⦇-⦈ ~> ⦇-⦈
      ISNEHole : ∀{Γ e τ d} →
        Γ ⊢ e => τ ~> d →
        Γ ⊢ ⦇⌜ e ⌟⦈ => ⦇-⦈ ~> ⦇⌜ d ⌟⦈
      ISAsc : ∀ {Γ e τ d τ'} →
        Γ ⊢ τ wf →
        Γ ⊢ e <= τ ~> d :: τ' →
        Γ ⊢ (e ·: τ) => τ ~> (d ·: τ')

    -- analysis : tau' must be more precise that tau
    data _⊢_<=_~>_::_ : (Γ : ctx) (e : hexp) (τ : htyp) (e : hexp) (τ' : htyp) → Set where
      IALam : ∀{Γ τ τ1 τ2 e d τ2'} →
        τ ⊓ (⦇-⦈ ==> ⦇-⦈) == τ1 ==> τ2 →
        (τ1 , Γ) ⊢ e <= τ2 ~> d :: τ2' →
        Γ ⊢ ·λ e <= τ ~> ·λ[ τ1 ] d :: τ1 ==> τ2'
      IATLam : ∀{Γ e τ1 τ2 τ2' d} → 
        τ1 ⊓ ·∀ ⦇-⦈ == (·∀ τ2) → 
        (TVar, Γ) ⊢ e <= τ2 ~> d :: τ2' →
        Γ ⊢ (·Λ e) <= τ1 ~> (·Λ d) :: (·∀ τ2')
      IASubsume : ∀{e Γ τ1 τ2 τ3 d} →
        e subsumable →
        Γ ⊢ e => τ2 ~> d →
        τ1 ⊓ τ2 == τ3 →
        (Γ ⊢ e <= τ1 ~> d :: τ3)
      IAInsertTAp : ∀{e Γ τ1 τ2 d} →
        e subsumable →
        Γ ⊢ (e < ⦇-⦈ >) <= τ1 ~> d :: τ2 → 
        (Γ ⊢ e <= τ1 ~> d :: τ2)