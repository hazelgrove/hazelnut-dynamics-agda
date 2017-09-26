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
  progress TAConst = V VConst
  progress (TAVar x) = abort (somenotnone (! x))
  progress (TALam D) = V VLam
  progress (TAAp D1 x D2)
    with progress D1 | progress D2
  progress (TAAp TAConst () D2)       | V VConst | _
  progress {Δ = Δ} (TAAp D1 x₂ D2)    | V VLam | V x₁ = S {Δ = Δ} (_ , Step FDot (ITLam (FVal x₁)) FDot)
  progress (TAAp (TALam D1) MAArr D2) | V VLam | I x₁ = S (_ , Step (FAp1 (FVal VLam) {!!}) (ITLam (FIndet x₁)) {!!}) -- stuck on defining substitution
  progress (TAAp D1 x₂ D2)            | _   | E x₁ = E (EAp2 x₁)
  progress (TAAp D1 x₂ D2)            | E x | _    = E (EAp1 x)
  -- progress (TAAp D1 x₂ D2) | V x | S x₁ = {!!}
  progress (TAAp D1 x₂ D2) | I IEHole | V x₁ = I (IAp IEHole (FVal x₁))
  progress (TAAp D1 x₂ D2) | I (INEHole x) | V x₁ = I (IAp (INEHole x) (FVal x₁))
  progress (TAAp D1 x₃ D2) | I (IAp x x₁) | V x₂ = I (IAp (IAp x x₁) (FVal x₂))
  progress (TAAp D1 x₂ D2) | I (ICast x) | V x₁ = I (IAp (ICast x) (FVal x₁))
  progress (TAAp D1 x₂ D2) | I x | I x₁ = I (IAp x (FIndet x₁))
  progress (TAAp {d1 = d1} D1 x₄ D2) | _ | S (d , Step x₁ x₂ x₃) = S ((d1 ∘ d) , (Step {!!} (ITLam (FIndet {!!})) {!!}))
  progress (TAAp {d2 = d2} D1 x₂ D2) | S (π1 , π2) | _ = S ((π1 ∘ d2) , {!!})
  -- progress (TAAp D1 x₂ D2) | S x | I x₁ = {!!}
  -- progress (TAAp D1 x₂ D2) | S x | S x₁ = {!!}
  progress (TAEHole {m = ✓} x x₁) = I IEHole
  progress (TAEHole {m = ✗} x x₁) = S (_ , Step FDot ITEHole FDot)
  progress (TANEHole x D x₁)
    with progress D
  progress (TANEHole {m = ✓} x₁ D x₂) | V v = I (INEHole (FVal v))
  progress (TANEHole {m = ✗} x₁ D x₂) | V v = S (_ , Step FDot (ITNEHole (FVal v)) FDot)
  progress (TANEHole {m = ✓} x₁ D x₂) | I x = I (INEHole (FIndet x))
  progress (TANEHole {m = ✗} x₁ D x₂) | I x = S (_ , Step FDot (ITNEHole (FIndet x)) FDot)
  progress (TANEHole x₁ D x₂) | E x = E (ENEHole x)
  progress (TANEHole x₃ D x₄) | S (d , Step x x₁ x₂) = S (_ , (Step (FNEHole x) x₁ (FNEHole x₂)))
  progress (TACast D x)
    with progress D
  progress (TACast TAConst TCRefl)  | V VConst = E EConst
  progress (TACast TAConst TCHole2) | V VConst = E EConst
  progress (TACast D x₁) | V VLam
    with invert-lam D
  progress (TACast D TCRefl)        | V VLam | τ1 , τ2 , refl = {!!}
  progress (TACast D TCHole2)       | V VLam | τ1 , τ2 , refl = {!!}
  progress (TACast D (TCArr x₁ x₂)) | V VLam | τ1 , τ2 , refl = {!!}
  progress (TACast D x₁) | I x = I (ICast x)
  progress (TACast D x₁) | E x = E (ECastProp x)
  progress (TACast D x₃) | S (d , Step x x₁ x₂) = S ( _ , Step (FCast x) x₁ (FCast x₂))
