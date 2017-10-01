open import Nat
open import Prelude
open import List
open import core
open import contexts
open import lemmas-consistency
open import canonical-forms

module progress where
  -- this is a little bit of syntactic sugar to avoid many layer nested Inl
  -- and Inrs that you would get from the more literal transcription of the
  -- consequent of progress as:
  --
  -- d val + d indet + d err[ Δ ] + Σ[ d' ∈ dhexp ] (Δ ⊢ d ↦ d')
  data ok : (d : dhexp) (Δ : hctx) → Set where
    V : ∀{d Δ} → d val → ok d Δ
    I : ∀{d Δ} → d indet → ok d Δ
    E : ∀{d Δ} → Δ ⊢ d err → ok d Δ
    S : ∀{d Δ} → Σ[ d' ∈ dhexp ] (Δ ⊢ d ↦ d') → ok d Δ

  progress : {Δ : hctx} {d : dhexp} {τ : htyp} →
             Δ , ∅ ⊢ d :: τ →
             ok d Δ
  -- constants
  progress TAConst = V VConst

  -- variables
  progress (TAVar x) = abort (somenotnone (! x))

  -- lambdas
  progress (TALam D) = V VLam

  -- applications
  progress (TAAp D1 x D2)
    with progress D1 | progress D2
    -- left applicand value
  progress (TAAp TAConst () D2) | V VConst | _
  progress (TAAp {d2 = d2} D1 MAArr D2) | V (VLam {x = x} {d = d}) | V x₁ = S ([ d2 / x ] d , Step (FHAp1 (FVal VLam) {!!}) (ITLam (FVal x₁)) {!!} )
  progress (TAAp {d2 = d2} D1 MAArr D2) | V (VLam {x = x} {d = d}) | I x₁ = S ([ d2 / x ] d , Step (FHAp1 (FVal VLam) {!!}) (ITLam (FIndet x₁)) {!!} )
    -- errors propagate
  progress (TAAp D1 x₂ D2) | _   | E x₁ = E (EAp2 x₁)
  progress (TAAp D1 x₂ D2) | E x | _    = E (EAp1 x)
    -- indeterminates
  progress (TAAp D1 x₂ D2) | I i | V v = I (IAp i  (FVal v))
  progress (TAAp D1 x₂ D2) | I x | I x₁ = I (IAp x (FIndet x₁))
    -- either applicand steps
  progress (TAAp {d1 = d1} D1 x₄ D2) | _ | S (d , Step x₁ x₂ x₃) = S ((d1 ∘ d) , {!!})
  progress (TAAp {d2 = d2} D1 x₂ D2) | S (π1 , π2) | _ = S ((π1 ∘ d2) , {!!})

  -- empty holes
  progress (TAEHole {m = ✓} x x₁) = I IEHole
  progress (TAEHole {m = ✗} x x₁) = S (_ , Step FHEHole ITEHole FHEHole)

  -- non-empty holes
  progress (TANEHole x D x₁)
    with progress D
  progress (TANEHole {m = ✓} x₁ D x₂) | V v = I (INEHole (FVal v))
  progress (TANEHole {m = ✗} x₁ D x₂) | V v = S ( _ , Step (FHNEHoleFinal (FVal v)) (ITNEHole (FVal v)) FHNEHoleEvaled)
  progress (TANEHole {m = ✓} x₁ D x₂) | I x = I (INEHole (FIndet x))
  progress (TANEHole {m = ✗} x₁ D x₂) | I x = S (_ , Step (FHNEHoleFinal (FIndet x)) (ITNEHole (FIndet x)) FHNEHoleEvaled )
  progress (TANEHole x₁ D x₂) | E x = E (ENEHole x)
  progress (TANEHole {d = d} {u = u} {σ = σ} {m = m} x₃ D x₄) | S (d' , Step x x₁ x₂) = S ( ⦇ d' ⦈⟨ u , σ , m ⟩ , {!!}) -- maybe depends on m

  -- casts
  progress (TACast D x)
    with progress D
  progress (TACast TAConst con) | V VConst = S (c , Step (FHCastFinal (FVal VConst)) (ITCast (FVal VConst) TAConst con) (FHFinal (FVal VConst)))
  progress (TACast D m) | V VLam = S (_ , Step (FHCastFinal (FVal VLam)) (ITCast (FVal VLam) D m) (FHFinal (FVal VLam)))
  progress (TACast D x₁) | I x = S {!!}
  progress (TACast D x₁) | E x = E (ECastProp x)
  progress (TACast D x₃) | S (d , Step x x₁ x₂) = S (_ , Step (FHCast x) x₁ (FHCast x₂))
