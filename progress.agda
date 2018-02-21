open import Nat
open import Prelude
open import List
open import core
open import contexts
open import lemmas-consistency

open import progress-checks

open import canonical-boxed-forms
open import canonical-value-forms
open import canonical-indeterminate-forms

open import ground-decidable
open import htype-decidable

module progress where
  -- this is a little bit of syntactic sugar to avoid many layer nested Inl
  -- and Inrs that you would get from the more literal transcription of the
  -- consequent of progress as:
  --
  -- d boxedval + d indet + Σ[ d' ∈ dhexp ] (d ↦ d')
  data ok : (d : dhexp) (Δ : hctx) → Set where
    S : ∀{d Δ} → Σ[ d' ∈ dhexp ] (d ↦ d') → ok d Δ
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
    -- if the left steps, the whole thing steps
  progress (TAAp wt1 wt2) | S (_ , Step x y z) | _ = S (_ , Step (FHAp1 x) y (FHAp1 z))
    -- if the left is indeterminate, step the right
  progress (TAAp wt1 wt2) | I i | S (_ , Step x y z) = S (_ , Step (FHAp2 x) y (FHAp2  z))
    -- if they're both indeterminate, step when the cast steps and indet otherwise
  progress (TAAp wt1 wt2) | I x | I x₁
    with canonical-indeterminate-forms-arr wt1 x
  progress (TAAp wt1 wt2) | I x | I y | CIFACast (_ , _ , _ , _ , _ , refl , _ , _ ) = S (_ , Step FHOuter ITApCast FHOuter)
  progress (TAAp wt1 wt2) | I x | I y | CIFAEHole (_ , _ , _ , refl , _)             = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress (TAAp wt1 wt2) | I x | I y | CIFANEHole (_ , _ , _ , _ , _ , refl , _)    = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress (TAAp wt1 wt2) | I x | I y | CIFAAp (_ , _ , _ , _ , _ , refl , _)        = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress (TAAp wt1 wt2) | I x | I y | CIFACastHole (_ , refl , refl , refl , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress (TAAp wt1 wt2) | I x | I y | CIFAFailedCast (_ , _ , refl , _ )           = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
    -- if the left is indetermiante but the right is a value
  progress (TAAp wt1 wt2) | I x | V x₁
    with canonical-indeterminate-forms-arr wt1 x
  progress (TAAp wt1 wt2) | I x | V y | CIFACast (_ , _ , _ , _ , _ , refl , _ , _ ) = S (_ , Step FHOuter ITApCast FHOuter)
  progress (TAAp wt1 wt2) | I x | V y | CIFAEHole (_ , _ , _ , refl , _)             = I (IAp (λ _ _ _ _ _ ()) x (FBoxed y))
  progress (TAAp wt1 wt2) | I x | V y | CIFANEHole (_ , _ , _ , _ , _ , refl , _)    = I (IAp (λ _ _ _ _ _ ()) x (FBoxed y))
  progress (TAAp wt1 wt2) | I x | V y | CIFAAp (_ , _ , _ , _ , _ , refl , _)        = I (IAp (λ _ _ _ _ _ ()) x (FBoxed y))
  progress (TAAp wt1 wt2) | I x | V y | CIFACastHole (_ , refl , refl , refl , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FBoxed y))
  progress (TAAp wt1 wt2) | I x | V y | CIFAFailedCast (_ , _ , refl , _ )           = I (IAp (λ _ _ _ _ _ ()) x (FBoxed y))
    -- if the left is a boxed value, inspect the right
  progress (TAAp wt1 wt2) | V v | S (_ , Step x y z) = S (_ , Step (FHAp2  x) y (FHAp2  z))
  progress (TAAp wt1 wt2) | V v | I i
    with canonical-boxed-forms-arr wt1 v
  ... | Inl (_ , _ , refl , _)         = S (_ , Step FHOuter ITLam FHOuter)
  ... | Inr (_ , _ , _ , refl , _ , _) = S (_ , Step FHOuter ITApCast FHOuter)
  progress (TAAp wt1 wt2) | V v | V v₂
    with canonical-boxed-forms-arr wt1 v
  ... | Inl (_ , _ , refl , _)         = S (_ , Step FHOuter ITLam FHOuter)
  ... | Inr (_ , _ , _ , refl , _ , _) = S (_ , Step FHOuter ITApCast FHOuter)

    -- empty holes
  progress (TAEHole x x₁) = I IEHole

    -- nonempty holes
  progress (TANEHole xin wt x₁)
    with progress wt
  ... | S (_ , Step x y z) = S (_ , Step (FHNEHole x) y (FHNEHole z))
  ... | I x = I (INEHole (FIndet x))
  ... | V x = I (INEHole (FBoxed x))

    -- casts
  progress (TACast wt con)
    with progress wt
  ... | S (_ , Step x y z) = S (_ , Step (FHCast x) y (FHCast z))
  -- indet cases, inspect how the casts are realted by consistency
  progress (TACast wt TCRefl)  | I x = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt TCHole1) | I x = I (ICastGroundHole {!!} x) -- cyrus
  progress (TACast wt TCHole2) | I x -- I (ICastHoleGround {!!} x {!!}) -- cyrus
    with canonical-indeterminate-forms-hole wt x
  progress (TACast wt TCHole2) | I x | Inl (_ , _ , _ , refl , f) = {!!}
  progress (TACast wt TCHole2) | I x | Inr (Inl (_ , _ , _ , _ , _ , refl , _ , _ , _)) = {!!}
  progress (TACast wt TCHole2) | I x | Inr (Inr (Inl (_ , _ , _ , refl , _ , _ , _ , _ , _))) = {!!}
  progress (TACast wt TCHole2) | I x | Inr (Inr (Inr (_ , _ , refl , _ , _ ))) = {!!}
  progress (TACast wt (TCArr c1 c2)) | I x = I (ICastArr {!!} x) -- cyrus
  -- boxed value cases, inspect how the casts are realted by consistency
  progress (TACast wt TCRefl)  | V x = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt TCHole1) | V x = V (BVHoleCast {!!} x) -- cyrus

  -- this is the case i was working on on friday; this part seems ok if maybe redundant
  progress {τ = τ} (TACast wt TCHole2) | V x
    with ground-decidable τ | canonical-boxed-forms-hole wt x
  progress {τ = τ} (TACast wt TCHole2) | V x₁ | Inl x | d' , τ' , refl , gnd , wt'
    with htype-dec τ' τ
  progress (TACast wt TCHole2) | V x₁ | Inl x₂ | d' , τ , refl , gnd , wt'  | Inl refl = S (_ , Step FHOuter (ITCastSucceed gnd) FHOuter )
  progress (TACast wt TCHole2) | V x₁ | Inl x₂ | d' , τ' , refl , gnd , wt' | Inr x    = S (_ , Step FHOuter (ITCastFail gnd x₂ x) FHOuter )
  progress {τ = τ} (TACast wt TCHole2) | V x₁ | Inr x  | d' , τ' , refl , gnd , wt' -- this case goes off the rails here
    with htype-dec τ' τ
  progress (TACast wt TCHole2) | V x₁ | Inr x₂ | d' , τ , refl , gnd , wt'  | Inl refl = abort (x₂ gnd)
  progress (TACast wt TCHole2) | V x₁ | Inr x₂ | d' , τ' , refl , gnd , wt' | Inr x = {!!}

  -- progress (TACast wt TCHole2) | V x₁ | Inr x₂ | d' , .b , refl , GBase , wt' | Inr x = {!!}
  -- progress {τ = b} (TACast wt TCHole2) | V x₁ | Inr x₂ | d' , .(⦇⦈ ==> ⦇⦈) , refl , GHole , wt' | Inr x = abort (x₂ GBase)
  -- progress {τ = ⦇⦈} (TACast wt TCHole2) | V x₁ | Inr x₂ | d' , .(⦇⦈ ==> ⦇⦈) , refl , GHole , wt' | Inr x = {!!} -- S (_ , Step (FHCast FHOuter) {!ground-arr-lem _ x₂ !} (FHCast FHOuter))
  -- progress {τ = τ1 ==> τ2} (TACast wt TCHole2) | V x₁ | Inr x₂ | d' , .(⦇⦈ ==> ⦇⦈) , refl , GHole , wt' | Inr x = {!!}

  -- this is the beginning of the next case -- cyrus
  progress (TACast wt (TCArr c1 c2)) | V x = {!!}


-- S {!!} --S ( _ , Step (FHCast FHOuter) (ITGround {!!}) (FHCast FHOuter))


   -- failed casts
  progress (TAFailedCast wt y z w)
    with progress wt
  progress (TAFailedCast wt y z w) | S (_ , Step x a q) = S (_ , Step {!!} (ITCastFail y z w) {!!} )
  progress (TAFailedCast wt y z w) | I x = I (IFailedCast (FIndet x) y z w)
  progress (TAFailedCast wt y z w) | V x = I (IFailedCast (FBoxed x) y z w)
