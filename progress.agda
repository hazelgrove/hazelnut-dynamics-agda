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
    S : ∀{d Δ} → Σ[ d' ∈ dhexp ] (Δ ⊢ d ↦ d') → ok d Δ
    E : ∀{d Δ} → d casterr → ok d Δ
    I : ∀{d Δ} → d indet → ok d Δ
    V : ∀{d Δ} → d boxedval → ok d Δ


  progress : {Δ : hctx} {d : dhexp} {τ : htyp} →
             Δ , ∅ ⊢ d :: τ →
             ok d Δ
  -- constants
  progress TAConst = V (BVVal VConst)

  -- variables
  progress (TAVar x₁) = abort (somenotnone (! x₁))

  -- lambdas
  progress (TALam wt) = V (BVVal VLam)

  -- applications
  progress (TAAp wt1 wt2)
    with progress wt1 | progress wt2
  progress (TAAp wt1 wt2) | S x | ih2 = {!!}
  progress (TAAp wt1 wt2) | E x | _ = E (CECong (FHAp1 FHOuter) x)
  progress (TAAp wt1 wt2) | I x | ih2 = {!!}
  progress (TAAp wt1 wt2) | V x | ih2 = {!!}

  -- empty holes
  progress (TAEHole x x₁) = I IEHole

  -- nonempty holes
  progress (TANEHole xin wt x₁)
    with progress wt
  ... | S (d' , Step x y z) = S (_ , Step {!!} {!!} {!!})
  ... | E x = E (CECong (FHNEHole FHOuter) x)
  ... | I x = I (INEHole (FIndet x))
  ... | V x = I (INEHole (FBoxed x))

  -- casts
  progress (TACast wt y)
    with progress wt
  ... | S x = {!!}
  ... | E x = E (CECong (FHCast FHOuter) x)
  ... | I x = {!x!}
  ... | V x = {!!}


  -- -- applications
  -- progress (TAAp D1 x D2)
  --   with progress D1 | progress D2
  --   -- left applicand value
  -- progress (TAAp TAConst () D2) | V VConst | _
  -- progress (TAAp {d2 = d2} D1 MAArr D2) | V (VLam {x = x} {d = d}) | V x₁ = S ([ d2 / x ] d , Step (FHAp1 (FVal VLam) {!!}) (ITLam (FVal x₁)) {!!} )
  -- progress (TAAp {d2 = d2} D1 MAArr D2) | V (VLam {x = x} {d = d}) | I x₁ = S ([ d2 / x ] d , Step (FHAp1 (FVal VLam) {!!}) (ITLam (FIndet x₁)) {!!} )
  --   -- errors propagate
  -- progress (TAAp D1 x₂ D2) | V x | E x₁ = E (EAp2 (FVal x) x₁)
  -- progress (TAAp D1 x₂ D2) | I x | E x₁ = E (EAp2 (FIndet x) x₁)
  -- progress (TAAp D1 x₂ D2) | E x | E x₁ = E (EAp1 x) -- NB: could have picked the other one here, too; this is a source of non-determinism
  -- progress (TAAp D1 x₂ D2) | S x | E x₁ = S {!!}
  -- progress (TAAp D1 x₂ D2) | E x | _    = E (EAp1 x)
  --   -- indeterminates
  -- progress (TAAp D1 x₂ D2) | I i | V v = I (IAp i  (FVal v))
  -- progress (TAAp D1 x₂ D2) | I x | I x₁ = I (IAp x (FIndet x₁))
  --   -- either applicand steps
  -- progress (TAAp D1 x₃ D2) | S (d1' , Step x x₁ x₂)  | _ = S (_ , Step (FHAp2 x) x₁ (FHAp2 x₂))
  -- progress (TAAp D1 x₄ D2) | _ | S (d2' , Step x₁ x₂ x₃) = S (_ , Step (FHAp1 {!!} x₁) x₂ (FHAp1 {!!} x₃))


  -- -- non-empty holes
  -- progress (TANEHole x D x₁)
  --   with progress D
  -- progress (TANEHole x₁ D x₂) | V v = I (INEHole (FVal v))
  -- progress (TANEHole x₁ D x₂) | I x = I (INEHole (FIndet x))
  -- progress (TANEHole x₁ D x₂) | E x = E (ENEHole x)
  -- progress (TANEHole x₃ D x₄) | S (_ , Step x x₁ x₂) = S (_ , Step (FHNEHole x) x₁ (FHNEHole x₂))

  -- -- casts
  -- progress (TACast D x)
  --   with progress D
  -- progress (TACast TAConst con) | V VConst = S (c , Step (FHCastFinal (FVal VConst)) (ITCast (FVal VConst) TAConst con) (FHFinal (FVal VConst)))
  -- progress (TACast D m)  | V VLam = S (_ , Step (FHCastFinal (FVal VLam)) (ITCast (FVal VLam) D m) (FHFinal (FVal VLam)))
  -- progress (TACast D x₁) | I x = I (ICast x)
  -- progress (TACast D x₁) | E x = E (ECastProp x)
  -- progress (TACast D x₃) | S (d , Step x x₁ x₂) = S (_ , Step (FHCast x) x₁ (FHCast x₂))
