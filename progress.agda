open import Nat
open import Prelude
open import core
open typctx
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
  -- consequent of progress
  data ok : (d : ihexp) (Δ : hctx) → Set where
    S  : ∀{d Δ} → Σ[ d' ∈ ihexp ] (d ↦ d') → ok d Δ
    I  : ∀{d Δ} → d indet → ok d Δ
    BV : ∀{d Δ} → d boxedval → ok d Δ

  forall-lemma : ∀{τ1 τ2} → (τ1 == τ2) → ·∀ τ1 == ·∀ τ2
  forall-lemma e rewrite e = refl 

  progress : {Δ : hctx} {d : ihexp} {τ : htyp} →
             Δ , ∅ , ~∅ ⊢ d :: τ →
             ok d Δ
    -- constants
  progress TAConst = BV (BVVal VConst)

    -- variables
  progress (TAVar x₁) = abort (somenotnone (! x₁))

    -- lambdas
  progress (TALam _ wt) = BV (BVVal VLam)

    -- Lambdas 

  progress (TATLam wt) = BV (BVVal VTLam)

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
  progress (TAAp wt1 wt2) | I x | I y | CIFATApArr (_ , _ , _ , _ , refl , _ , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress (TAAp wt1 wt2) | I x | I y | CIFATApId (_ , _ , _ , refl , _ , _ )        = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress (TAAp wt1 wt2) | I x | I y | CIFACastHole (_ , refl , refl , refl , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress (TAAp wt1 wt2) | I x | I y | CIFAFailedCast (_ , _ , refl , _ )           = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
    -- similar if the left is indetermiante but the right is a boxed val
  progress (TAAp wt1 wt2) | I x | BV x₁
    with canonical-indeterminate-forms-arr wt1 x
  progress (TAAp wt1 wt2) | I x | BV y | CIFACast (_ , _ , _ , _ , _ , refl , _ , _ ) = S (_ , Step FHOuter ITApCast FHOuter)
  progress (TAAp wt1 wt2) | I x | BV y | CIFAEHole (_ , _ , _ , refl , _)             = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress (TAAp wt1 wt2) | I x | BV y | CIFANEHole (_ , _ , _ , _ , _ , refl , _)    = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress (TAAp wt1 wt2) | I x | BV y | CIFAAp (_ , _ , _ , _ , _ , refl , _)        = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress (TAAp wt1 wt2) | I x | BV y | CIFATApArr (_ , _ , _ , _ , refl , _ , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress (TAAp wt1 wt2) | I x | BV y | CIFATApId (_ , _ , _ , refl , _ , _ )        = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress (TAAp wt1 wt2) | I x | BV y | CIFACastHole (_ , refl , refl , refl , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress (TAAp wt1 wt2) | I x | BV y | CIFAFailedCast (_ , _ , refl , _ )           = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
    -- if the left is a boxed value, inspect the right
  progress (TAAp wt1 wt2) | BV v | S (_ , Step x y z) = S (_ , Step (FHAp2  x) y (FHAp2  z))
  progress (TAAp wt1 wt2) | BV v | I i
    with canonical-boxed-forms-arr wt1 v
  ... | CBFLam (_ , _ , refl , _)             = S (_ , Step FHOuter ITLam FHOuter)
  ... | CBFCastArr (_ , _ , _ , refl , _ , _) = S (_ , Step FHOuter ITApCast FHOuter)
  progress (TAAp wt1 wt2) | BV v | BV v₂
    with canonical-boxed-forms-arr wt1 v
  ... | CBFLam (_ , _ , refl , _)             = S (_ , Step FHOuter ITLam FHOuter)
  ... | CBFCastArr (_ , _ , _ , refl , _ , _) = S (_ , Step FHOuter ITApCast FHOuter)

    -- type applications
  
  progress (TATAp wt eq) with progress wt 
  ... | S (_ , Step x y z) = S (_ , (Step (FHTAp x) y (FHTAp z)))
  ... | I x = {!   !}
  ... | (BV v) with canonical-boxed-forms-forall wt v 
  ... | CBFTLam (x , y , z) rewrite y = S (_ , Step FHOuter ITTLam FHOuter)
  ... | CBFCastForall (x , y , z , w , v) rewrite z = S (_ , Step FHOuter ITTApCast FHOuter) 
  -- progress (TATAp (TAEHole x x₁) eq) = I (ITAp (λ τ1 τ2 d' ()) IEHole)
  

    -- empty holes are indeterminate
  progress (TAEHole _ _ ) = I IEHole

    -- nonempty holes step if the innards step, indet otherwise
  progress (TANEHole xin wt x₁)
    with progress wt
  ... | S (_ , Step x y z) = S (_ , Step (FHNEHole x) y (FHNEHole z))
  ... | I  x = I (INEHole (FIndet x))
  ... | BV x = I (INEHole (FBoxedVal x))

    -- casts
  progress (TACast wt con)
    with progress wt
    -- step if the innards step
  progress (TACast wt con) | S (_ , Step x y z) = S (_ , Step (FHCast x) y (FHCast z))
    -- if indet, inspect how the types in the cast are realted by consistency:
    -- if they're the same, step by ID
  -- progress (TACast wt TCRefl)  | I x = S (_ , Step FHOuter {! ITC  !} {!   !}) -- S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt TCBase) | _ = S (_ , (Step FHOuter ITCastID FHOuter))
  progress (TACast wt TCVar) | _ = S (_ , (Step FHOuter ITCastID FHOuter))
    -- if first type is hole
  progress (TACast {τ1 = τ1} wt TCHole1) | I x
    with τ1
  progress (TACast wt TCHole1) | I x | b = I (ICastGroundHole GBase x)
  progress (TACast wt TCHole1) | I x | T n = {!   !}
  progress (TACast wt TCHole1) | I x | ⦇-⦈ = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt TCHole1) | I x | τ11 ==> τ12
    with ground-decidable (τ11 ==> τ12)
  progress (TACast wt TCHole1) | I x₁ | .⦇-⦈ ==> .⦇-⦈ | Inl GArr = I (ICastGroundHole GArr x₁)
  progress (TACast wt TCHole1) | I x₁ | τ11 ==> τ12 | Inr x =  S (_ , Step FHOuter (ITGround (MGArr (ground-arr-not-hole x))) FHOuter)
  progress (TACast wt TCHole1) | I x | ·∀ τ with ground-decidable (·∀ τ)
  progress (TACast wt TCHole1) | I x | ·∀ .⦇-⦈ | Inl GForall = I (ICastGroundHole GForall x)
  progress (TACast wt TCHole1) | I x₁ | ·∀ τ | Inr x  = S (_ , Step FHOuter (ITGround (MGForall (ground-forall-not-hole x))) FHOuter)
    -- if second type is hole
  progress (TACast wt (TCHole2 {b})) | I x
    with canonical-indeterminate-forms-hole wt x
  progress (TACast wt (TCHole2 {b})) | I x | CIFHEHole (_ , _ , _ , refl , f)           = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress (TACast wt (TCHole2 {b})) | I x | CIFHNEHole (_ , _ , _ , _ , _ , refl , _ ) = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress (TACast wt (TCHole2 {b})) | I x | CIFHAp (_ , _ , _ , refl , _ )             = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress (TACast wt (TCHole2 {b})) | I x | CIFHTApHole (_ , _ , refl , _ )        = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress (TACast wt (TCHole2 {b})) | I x | CIFHTApId (_ , _ , refl , _ )          = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress (TACast wt (TCHole2 {b})) | I x | CIFHCast (_ , τ , refl , _)
    with htype-dec τ b
  progress (TACast wt (TCHole2 {b})) | I x₁ | CIFHCast (_ , .b , refl , _ , grn , _) | Inl refl = S (_ , Step FHOuter (ITCastSucceed grn ) FHOuter)
  progress (TACast wt (TCHole2 {b})) | I x₁ | CIFHCast (_ , _ , refl , π2 , grn , _)  | Inr x =    S (_ , Step FHOuter (ITCastFail grn GBase x) FHOuter)
  progress (TACast wt (TCHole2 {T x})) | _ = {!   !}
  progress (TACast wt (TCHole2 {⦇-⦈})) | I x = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt (TCHole2 {τ11 ==> τ12})) | I x
    with ground-decidable (τ11 ==> τ12)
  progress (TACast wt (TCHole2 {.⦇-⦈ ==> .⦇-⦈})) | I x₁ | Inl GArr
    with canonical-indeterminate-forms-hole wt x₁
  progress (TACast wt (TCHole2 {.⦇-⦈ ==> .⦇-⦈})) | I x | Inl GArr | CIFHEHole (_ , _ , _ , refl , _)          = I (ICastHoleGround (λ _ _ ()) x GArr)
  progress (TACast wt (TCHole2 {.⦇-⦈ ==> .⦇-⦈})) | I x | Inl GArr | CIFHNEHole (_ , _ , _ , _ , _ , refl , _) = I (ICastHoleGround (λ _ _ ()) x GArr)
  progress (TACast wt (TCHole2 {.⦇-⦈ ==> .⦇-⦈})) | I x | Inl GArr | CIFHAp (_ , _ , _ , refl , _ )            = I (ICastHoleGround (λ _ _ ()) x GArr)
  progress (TACast wt (TCHole2 {.⦇-⦈ ==> .⦇-⦈})) | I x | Inl GArr | CIFHTApHole (_ , _ , refl , _ )            = I (ICastHoleGround (λ _ _ ()) x GArr)
  progress (TACast wt (TCHole2 {.⦇-⦈ ==> .⦇-⦈})) | I x | Inl GArr | CIFHTApId (_ , _ , refl , _ )            = I (ICastHoleGround (λ _ _ ()) x GArr)
  progress (TACast wt (TCHole2 {.⦇-⦈ ==> .⦇-⦈})) | I x | Inl GArr | CIFHCast (_ , ._ , refl , _ , GBase , _)  = S (_ , Step FHOuter (ITCastFail GBase GArr (λ ())) FHOuter )
  progress (TACast wt (TCHole2 {.⦇-⦈ ==> .⦇-⦈})) | I x | Inl GArr | CIFHCast (_ , ._ , refl , _ , GArr , _)  = S (_ , Step FHOuter (ITCastSucceed GArr) FHOuter)
  progress (TACast wt (TCHole2 {.⦇-⦈ ==> .⦇-⦈})) | I x | Inl GArr | CIFHCast (_ , ._ , refl , _ , GForall , _)  = S (_ , Step FHOuter (ITCastFail GForall GArr (λ ())) FHOuter )
  progress (TACast wt (TCHole2 {τ11 ==> τ12})) | I x₁ | Inr x = S (_ , Step FHOuter (ITExpand (MGArr (ground-arr-not-hole x))) FHOuter)
  progress (TACast wt (TCHole2 {·∀ τ})) | _ = {!   !}
    -- if both are arrows
  progress (TACast wt (TCArr {τ1} {τ2} {τ1'} {τ2'} c1 c2)) | I x
    with htype-dec (τ1 ==> τ2)  (τ1' ==> τ2')
  progress (TACast wt (TCArr c1 c2)) | I x₁ | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt (TCArr c1 c2)) | I x₁ | Inr x = I (ICastArr x x₁)
    -- if both are foralls 
  progress (TACast wt (TCForall {τ1} {τ2} con)) | I x
    with htype-dec (·∀ τ1) (·∀ τ2) 
  progress (TACast wt (TCForall con)) | I x | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt (TCForall con)) | I x₁ | Inr x = I (ICastForall (λ {e → x (forall-lemma e)}) x₁)

    -- boxed value cases, inspect how the casts are realted by consistency
    -- step by ID if the casts are the same
  -- progress (TACast wt TCRefl)  | BV x = {!   !} -- S (_ , Step FHOuter ITCastID FHOuter)
    -- if left is hole
  progress (TACast wt (TCHole1 {τ = τ})) | BV x
    with ground-decidable τ
  progress (TACast wt TCHole1) | BV x₁ | Inl g = BV (BVHoleCast g x₁)
  progress (TACast wt (TCHole1 {b})) | BV x₁ | Inr x = abort (x GBase)
  progress (TACast wt (TCHole1 {T n})) | BV x₁ | Inr x = {!   !}
  progress (TACast wt (TCHole1 {⦇-⦈})) | BV x₁ | Inr x = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt (TCHole1 {τ1 ==> τ2})) | BV x₁ | Inr x
    with (htype-dec  (τ1 ==> τ2) (⦇-⦈ ==> ⦇-⦈))
  progress (TACast wt (TCHole1 {.⦇-⦈ ==> .⦇-⦈})) | BV x₂ | Inr x₁ | Inl refl = BV (BVHoleCast GArr x₂)
  progress (TACast wt (TCHole1 {τ1 ==> τ2})) | BV x₂ | Inr x₁ | Inr x = S (_ , Step FHOuter (ITGround (MGArr x)) FHOuter)
  progress (TACast wt (TCHole1 {·∀ τ})) | BV x₁ | Inr x 
    with (htype-dec  (·∀ τ) (·∀ ⦇-⦈))
  progress (TACast wt (TCHole1 {·∀ .⦇-⦈})) | BV x₁ | Inr x | Inl refl = BV (BVHoleCast GForall x₁)
  progress (TACast wt (TCHole1 {·∀ τ})) | BV x₁ | Inr x₂ | Inr x = S (_ , Step FHOuter (ITGround (MGForall x)) FHOuter) 
    -- if right is hole
  progress {τ = τ} (TACast wt TCHole2) | BV x
    with canonical-boxed-forms-hole wt x
  progress {τ = τ} (TACast wt TCHole2) | BV x | d' , τ' , refl , gnd , wt'
    with htype-dec τ τ'
  progress (TACast wt TCHole2) | BV x₁ | d' , τ , refl , gnd , wt' | Inl refl = S (_  , Step FHOuter (ITCastSucceed gnd) FHOuter)
  progress {τ = τ} (TACast wt TCHole2) | BV x₁ | _ , _ , refl , _ , _ | Inr _
    with ground-decidable τ
  progress (TACast wt TCHole2) | BV x₂ | _ , _ , refl , gnd , _ | Inr x₁ | Inl x = S(_ , Step FHOuter (ITCastFail gnd x (flip x₁)) FHOuter)
  progress (TACast wt TCHole2) | BV x₂ | _ , _ , refl , _ , _ | Inr x₁ | Inr x
    with notground x
  progress (TACast wt TCHole2) | BV x₃ | _ , _ , refl , _ , _ | Inr _ | Inr _ | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt TCHole2) | BV x₃ | _ , _ , refl , gnd , _ | Inr _ | Inr x | Inr (Inl (_ , refl)) =  {!   !} 
  progress (TACast wt TCHole2) | BV x₃ | _ , _ , refl , _ , _ | Inr _ | Inr x | Inr (Inr (Inl (_ , _ , refl))) = S(_ , Step FHOuter (ITExpand (MGArr (ground-arr-not-hole x))) FHOuter )
  progress {τ = ·∀ τ} (TACast wt TCHole2) | BV x₃ | _ , _ , refl , _ , _ | Inr _ | Inr x | Inr (Inr (Inr (_ , refl))) = S(_ , Step FHOuter (ITExpand (MGForall (ground-forall-not-hole x))) FHOuter )
    -- if both arrows
  progress (TACast wt (TCArr {τ1} {τ2} {τ1'} {τ2'} c1 c2)) | BV x
    with htype-dec (τ1 ==> τ2) (τ1' ==> τ2')
  progress (TACast wt (TCArr c1 c2)) | BV x₁ | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt (TCArr c1 c2)) | BV x₁ | Inr x = BV (BVArrCast x x₁)
  progress (TACast wt (TCForall {τ1} {τ2} _)) | BV x
    with htype-dec (·∀ τ1) (·∀ τ2)
  progress (TACast wt (TCForall {τ1} {τ2} _)) | BV x₁ | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt (TCForall {τ1} {τ2} _)) | BV x₁ | Inr x = BV (BVForallCast (λ {e → x ((forall-lemma e))}) x₁)

   -- failed casts
  progress (TAFailedCast wt y z w)
    with progress wt
  progress (TAFailedCast wt y z w) | S (d' , Step x a q) = S (_ , Step (FHFailedCast x) a (FHFailedCast q))
  progress (TAFailedCast wt y z w) | I x = I (IFailedCast (FIndet x) y z w)
  progress (TAFailedCast wt y z w) | BV x = I (IFailedCast (FBoxedVal x) y z w)
