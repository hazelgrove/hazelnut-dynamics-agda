open import Nat
open import Prelude
open import List
open import core
open import contexts
open import lemmas-consistency
open import lemmas-ground

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
    BV : ∀{d Δ} → d boxedval → ok d Δ

  progress : {Δ : hctx} {d : dhexp} {τ : htyp} →
             Δ , ∅ ⊢ d :: τ →
             ok d Δ
    -- constants
  progress TAConst = BV (BVVal VConst)

    -- variables
  progress (TAVar x₁) = abort (somenotnone (! x₁))

    -- lambdas
  progress (TALam wt) = BV (BVVal VLam)

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
  progress (TAAp wt1 wt2) | I x | BV x₁
    with canonical-indeterminate-forms-arr wt1 x
  progress (TAAp wt1 wt2) | I x | BV y | CIFACast (_ , _ , _ , _ , _ , refl , _ , _ ) = S (_ , Step FHOuter ITApCast FHOuter)
  progress (TAAp wt1 wt2) | I x | BV y | CIFAEHole (_ , _ , _ , refl , _)             = I (IAp (λ _ _ _ _ _ ()) x (FBoxed y))
  progress (TAAp wt1 wt2) | I x | BV y | CIFANEHole (_ , _ , _ , _ , _ , refl , _)    = I (IAp (λ _ _ _ _ _ ()) x (FBoxed y))
  progress (TAAp wt1 wt2) | I x | BV y | CIFAAp (_ , _ , _ , _ , _ , refl , _)        = I (IAp (λ _ _ _ _ _ ()) x (FBoxed y))
  progress (TAAp wt1 wt2) | I x | BV y | CIFACastHole (_ , refl , refl , refl , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FBoxed y))
  progress (TAAp wt1 wt2) | I x | BV y | CIFAFailedCast (_ , _ , refl , _ )           = I (IAp (λ _ _ _ _ _ ()) x (FBoxed y))
    -- if the left is a boxed value, inspect the right
  progress (TAAp wt1 wt2) | BV v | S (_ , Step x y z) = S (_ , Step (FHAp2  x) y (FHAp2  z))
  progress (TAAp wt1 wt2) | BV v | I i
    with canonical-boxed-forms-arr wt1 v
  ... | Inl (_ , _ , refl , _)         = S (_ , Step FHOuter ITLam FHOuter)
  ... | Inr (_ , _ , _ , refl , _ , _) = S (_ , Step FHOuter ITApCast FHOuter)
  progress (TAAp wt1 wt2) | BV v | BV v₂
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
  ... | BV x = I (INEHole (FBoxed x))

    -- casts
  progress (TACast wt con)
    with progress wt
  ... | S (_ , Step x y z) = S (_ , Step (FHCast x) y (FHCast z))
  -- indet cases, inspect how the casts are realted by consistency
  progress (TACast wt TCRefl)  | I x = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast {τ1 = τ1} wt TCHole1) | I x
    with τ1
  progress (TACast wt TCHole1) | I x | b = I (ICastGroundHole GBase x)
  progress (TACast wt TCHole1) | I x | ⦇⦈ = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt TCHole1) | I x | τ11 ==> τ12
    with ground-decidable (τ11 ==> τ12)
  progress (TACast wt TCHole1) | I x₁ | .⦇⦈ ==> .⦇⦈ | Inl GHole = I (ICastGroundHole GHole x₁)
  progress (TACast wt TCHole1) | I x₁ | τ11 ==> τ12 | Inr x =  S (_ , Step FHOuter (ITGround (MGArr (ground-arr-not-hole x))) FHOuter)
  progress (TACast wt (TCHole2 {b})) | I x
    with canonical-indeterminate-forms-hole wt x
  progress (TACast wt (TCHole2 {b})) | I x | Inl (_ , _ , _ , refl , f)                             = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress (TACast wt (TCHole2 {b})) | I x | Inr (Inl (_ , _ , _ , _ , _ , refl , _ , _ , _))       = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress (TACast wt (TCHole2 {b})) | I x | Inr (Inr (Inl (_ , _ , _ , refl , _ , _ , _ , _ , _))) = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress (TACast wt (TCHole2 {b})) | I x | Inr (Inr (Inr (_ , τ , refl , _ , _)))
    with htype-dec τ b
  progress (TACast wt (TCHole2 {b})) | I x₁ | Inr (Inr (Inr (_ , ._ , refl , gnd , _))) | Inl refl = S (_ , Step FHOuter (ITCastSucceed gnd) FHOuter)
  progress (TACast wt (TCHole2 {b})) | I x₁ | Inr (Inr (Inr (_ , _ , refl , gnd , _)))  | Inr neq = S (_ , Step FHOuter (ITCastFail gnd GBase neq) FHOuter)

  progress (TACast wt (TCHole2 {⦇⦈})) | I x = S (_ , Step FHOuter ITCastID FHOuter)

  progress (TACast wt (TCHole2 {τ11 ==> τ12})) | I x
    with ground-decidable (τ11 ==> τ12)
  progress (TACast wt (TCHole2 {.⦇⦈ ==> .⦇⦈})) | I x₁ | Inl GHole
    with canonical-indeterminate-forms-hole wt x₁
  progress (TACast wt (TCHole2 {.⦇⦈ ==> .⦇⦈})) | I x | Inl GHole | Inl (_ , _ , _ , refl , _)                             = I (ICastHoleGround (λ _ _ ()) x GHole)
  progress (TACast wt (TCHole2 {.⦇⦈ ==> .⦇⦈})) | I x | Inl GHole | Inr (Inl (_ , _ , _ , _ , _ , refl , _ , _ , _))       = I (ICastHoleGround (λ _ _ ()) x GHole)
  progress (TACast wt (TCHole2 {.⦇⦈ ==> .⦇⦈})) | I x | Inl GHole | Inr (Inr (Inl (_ , _ , _ , refl , _ , _ , _ , _ , _))) = I (ICastHoleGround (λ _ _ ()) x GHole)
  progress (TACast wt (TCHole2 {.⦇⦈ ==> .⦇⦈})) | I x | Inl GHole | Inr (Inr (Inr (_ , ._ , refl , GBase , _))) = S (_ , Step FHOuter (ITCastFail GBase GHole (λ ())) FHOuter )
  progress (TACast wt (TCHole2 {.⦇⦈ ==> .⦇⦈})) | I x | Inl GHole | Inr (Inr (Inr (_ , ._ , refl , GHole , _))) = S (_ , Step FHOuter (ITCastSucceed GHole) FHOuter)

  progress (TACast wt (TCHole2 {τ11 ==> τ12})) | I x₁ | Inr x = S (_ , Step FHOuter (ITExpand (MGArr (ground-arr-not-hole x))) FHOuter)

  progress (TACast wt (TCArr {τ1} {τ2} {τ1'} {τ2'} c1 c2)) | I x
    with htype-dec (τ1 ==> τ2)  (τ1' ==> τ2')
  progress (TACast wt (TCArr c1 c2)) | I x₁ | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt (TCArr c1 c2)) | I x₁ | Inr x = I (ICastArr x x₁)

  -- boxed value cases, inspect how the casts are realted by consistency
  progress (TACast wt TCRefl)  | BV x = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt (TCHole1 {τ = τ})) | BV x
    with ground-decidable τ
  progress (TACast wt TCHole1) | BV x₁ | Inl g = BV (BVHoleCast g x₁)
  progress (TACast wt (TCHole1 {b})) | BV x₁ | Inr x = abort (x GBase)
  progress (TACast wt (TCHole1 {⦇⦈})) | BV x₁ | Inr x = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt (TCHole1 {τ1 ==> τ2})) | BV x₁ | Inr x
    with (htype-dec  (τ1 ==> τ2) (⦇⦈ ==> ⦇⦈))
  progress (TACast wt (TCHole1 {.⦇⦈ ==> .⦇⦈})) | BV x₂ | Inr x₁ | Inl refl = BV (BVHoleCast GHole x₂)
  progress (TACast wt (TCHole1 {τ1 ==> τ2})) | BV x₂ | Inr x₁ | Inr x = S (_ , Step FHOuter (ITGround (MGArr x)) FHOuter)


  -- this is the case i was working on on friday; this part seems ok if maybe redundant
  progress {τ = τ} (TACast wt TCHole2) | BV x
    with ground-decidable τ | canonical-boxed-forms-hole wt x
  progress {τ = τ} (TACast wt TCHole2) | BV x₁ | Inl x | d' , τ' , refl , gnd , wt'
    with htype-dec τ' τ
  progress (TACast wt TCHole2) | BV x₁ | Inl x₂ | d' , τ , refl , gnd , wt'  | Inl refl = S (_ , Step FHOuter (ITCastSucceed gnd) FHOuter )
  progress (TACast wt TCHole2) | BV x₁ | Inl x₂ | d' , τ' , refl , gnd , wt' | Inr x    = S (_ , Step FHOuter (ITCastFail gnd x₂ x) FHOuter )
  progress {τ = τ} (TACast wt TCHole2) | BV x₁ | Inr x  | d' , τ' , refl , gnd , wt' -- this case goes off the rails here
    with htype-dec τ' τ
  progress (TACast wt TCHole2) | BV x₁ | Inr x₂ | d' , τ , refl , gnd , wt'  | Inl refl = abort (x₂ gnd)
  progress (TACast wt TCHole2) | BV x₁ | Inr x₂ | d' , τ' , refl , gnd , wt' | Inr x = {!!} -- S (_ , Step {!!} (ITCastFail gnd {!!} x) {!!})

  -- this is the beginning of the next case
  progress (TACast wt (TCArr {τ1} {τ2} {τ1'} {τ2'} c1 c2)) | BV x
    with htype-dec (τ1 ==> τ2) (τ1' ==> τ2')
  progress (TACast wt (TCArr c1 c2)) | BV x₁ | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt (TCArr c1 c2)) | BV x₁ | Inr x = BV (BVArrCast x x₁)

   -- failed casts
  progress (TAFailedCast wt y z w)
    with progress wt
  progress (TAFailedCast wt y z w) | S (d' , Step x a q) = S(_ , Step (FHFailedCast (FHCast x)) a (FHFailedCast (FHCast q)))
  progress (TAFailedCast wt y z w) | I x = I (IFailedCast (FIndet x) y z w)
  progress (TAFailedCast wt y z w) | BV x = I (IFailedCast (FBoxed x) y z w)
