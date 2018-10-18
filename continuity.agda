open import Nat
open import Prelude
open import core
open import contexts

open import progress
open import preservation
open import elaborability
open import typed-elaboration

module continuity where
  -- we take the sensibilty theorem as a postulate; for a proof, refer to
  -- the POPL17 mechanization. we also postulate some glue that allows us
  -- to use our theorems here on the shape of results from that work.
  postulate
    action : Set
    zexp : Set
    _◆ : zexp → hexp
    _⊢_=>_~_~>_=>_ : (Γ : tctx) → (e1 : zexp) → (t1 : htyp)
                        → (α : action) → (e2 : zexp) → (t2 : htyp) → Set
    sensibility : {Γ : tctx} {e e' : zexp} {τ τ' : htyp} {α : action} →
                  Γ ⊢ (e ◆) => τ →
                  Γ ⊢ e => τ ~ α ~> e' => τ' →
                  Γ ⊢ (e' ◆) => τ'
    binders-unique-h : hexp → Set
    binders-unique-z : zexp → Set
    binders-unique-cursor1 : ∀{e} → binders-unique-z e → binders-unique-h (e ◆)
    binders-unique-cursor2 : ∀{e} → binders-unique-h (e ◆) → binders-unique-z e
    binders-unique-sensibility : {Γ : tctx} {e e' : zexp} {τ τ' : htyp} {α : action} →
                  binders-unique-z e →
                  Γ ⊢ e => τ ~ α ~> e' => τ' →
                  binders-unique-z e'
    expansion-unique : ∀{Γ e τ d Δ} →
                       binders-unique-h e →
                       Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                       binders-unique d


  continuity : ∀{ e τ α e' τ' }
             → binders-unique-z e
             → ∅ ⊢ (e ◆) => τ
             → ∅ ⊢ e => τ ~ α ~> e' => τ'
             → Σ[ Δ ∈ hctx ] Σ[ d ∈ ihexp ]
                (   ∅ ⊢ (e' ◆) ⇒ τ' ~> d ⊣ Δ
                  × Δ , ∅ ⊢ d :: τ'
                  × ( (Σ[ d' ∈ ihexp ]( d ↦ d' × Δ , ∅ ⊢ d' :: τ' ))
                     + d boxedval
                     + d indet
                    )
                )
  continuity bu wt action with sensibility wt action
  ... | sense with elaborability-synth sense
  ... | d , Δ , exp with typed-elaboration-synth exp
  ... | d::τ' with progress d::τ'
  ... | (S (d' , stp)) =  Δ , d , exp , d::τ' , Inl (d' , stp , preservation (expansion-unique (binders-unique-cursor1 (binders-unique-sensibility bu action)) exp) d::τ' stp)
  ... | (I ind) = Δ , d , exp , d::τ' , Inr (Inr ind)
  ... | (BV boxed) = Δ , d , exp , d::τ' , Inr (Inl boxed)
