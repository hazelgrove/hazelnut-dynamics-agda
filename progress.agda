open import Nat
open import Prelude
open import core
open alpha

open import contexts
open import lemmas-consistency
open import lemmas-ground

open import progress-checks

open import canonical-boxed-forms
open import canonical-value-forms
open import canonical-indeterminate-forms

open import ground-decidable
open import htype-decidable

open import lemmas-well-formed
open import rewrite-util

module progress where
  -- this is a little bit of syntactic sugar to avoid many layer nested Inl
  -- and Inrs that you would get from the more literal transcription of the
  -- consequent of progress
  data ok : (d : ihexp) (Δ : hctx) → Set where
    S  : ∀{d Δ} → Σ[ d' ∈ ihexp ] (d ↦ d') → ok d Δ
    I  : ∀{d Δ} → d indet → ok d Δ
    BV : ∀{d Δ} → d boxedval → ok d Δ

  forall-lemma : ∀{t τ1 τ2} → (τ1 == τ2) → ·∀ t τ1 == ·∀ t τ2
  forall-lemma e rewrite e = refl 

  progress : {Δ : hctx} {d : ihexp} {τ : htyp} →
             Δ hctxwf →
             Δ , ∅ , ∅ ⊢ d :: τ →
             ok d Δ
    -- constants
  progress hctxwf TAConst = BV (BVVal VConst)

    -- variables
  progress hctxwf (TAVar x₁) = abort (somenotnone (! x₁))

    -- lambdas
  progress hctxwf (TALam _ _ wt) = BV (BVVal VLam)

    -- Lambdas 

  progress hctxwf (TATLam wt) = BV (BVVal VTLam)

    -- applications
  progress hctxwf (TAAp wt1 wt2)
    with progress hctxwf wt1 | progress hctxwf wt2
    -- if the left steps, the whole thing steps
  progress hctxwf (TAAp wt1 wt2) | S (_ , Step x y z) | _ = S (_ , Step (FHAp1 x) y (FHAp1 z))
    -- if the left is indeterminate, step the right
  progress hctxwf (TAAp wt1 wt2) | I i | S (_ , Step x y z) = S (_ , Step (FHAp2 x) y (FHAp2  z))
    -- if they're both indeterminate, step when the cast steps and indet otherwise
  progress hctxwf (TAAp wt1 wt2) | I x | I x₁
    with canonical-indeterminate-forms-arr wt1 x
  progress hctxwf (TAAp wt1 wt2) | I x | I y | CIFACast (_ , _ , _ , _ , _ , refl , _ , _ ) = S (_ , Step FHOuter ITApCast FHOuter)
  progress hctxwf (TAAp wt1 wt2) | I x | I y | CIFAEHole (_ , _ , _ , _ , _ , _ , refl , _)             = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress hctxwf (TAAp wt1 wt2) | I x | I y | CIFANEHole (_ , _ , _ , _ , _ , _ , _ , _ , refl , _)    = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress hctxwf (TAAp wt1 wt2) | I x | I y | CIFAAp (_ , _ , _ , _ , _ , refl , _)        = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress hctxwf (TAAp wt1 wt2) | I x | I y | CIFATApArr (_ , _ , _ , _ , _ , refl , _ , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress hctxwf (TAAp wt1 wt2) | I x | I y | CIFATApId (_ , _ , _ , _ , refl , _ , _ )        = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress hctxwf (TAAp wt1 wt2) | I x | I y | CIFACastHole (_ , refl , refl , refl , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress hctxwf (TAAp wt1 wt2) | I x | I y | CIFAFailedCast (_ , _ , refl , _ )           = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
    -- similar if the left is indetermiante but the right is a boxed val
  progress hctxwf (TAAp wt1 wt2) | I x | BV x₁
    with canonical-indeterminate-forms-arr wt1 x
  progress hctxwf (TAAp wt1 wt2) | I x | BV y | CIFACast (_ , _ , _ , _ , _ , refl , _ , _ ) = S (_ , Step FHOuter ITApCast FHOuter)
  progress hctxwf (TAAp wt1 wt2) | I x | BV y | CIFAEHole (_ , _ , _ , _ , _ , _ , refl , _)             = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress hctxwf (TAAp wt1 wt2) | I x | BV y | CIFANEHole (_ , _ , _ , _ , _ , _ , _ , _ , refl , _)    = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress hctxwf (TAAp wt1 wt2) | I x | BV y | CIFAAp (_ , _ , _ , _ , _ , refl , _)        = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress hctxwf (TAAp wt1 wt2) | I x | BV y | CIFATApArr (_ , _ , _ , _ , _ , refl , _ , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress hctxwf (TAAp wt1 wt2) | I x | BV y | CIFATApId (_ , _ , _ , _ , refl , _ , _ )        = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress hctxwf (TAAp wt1 wt2) | I x | BV y | CIFACastHole (_ , refl , refl , refl , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress hctxwf (TAAp wt1 wt2) | I x | BV y | CIFAFailedCast (_ , _ , refl , _ )           = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
    -- if the left is a boxed value, inspect the right
  progress hctxwf (TAAp wt1 wt2) | BV v | S (_ , Step x y z) = S (_ , Step (FHAp2  x) y (FHAp2  z))
  progress hctxwf (TAAp wt1 wt2) | BV v | I i
    with canonical-boxed-forms-arr wt1 v
  ... | CBFLam (_ , _ , refl , _)             = S (_ , Step FHOuter ITLam FHOuter)
  ... | CBFCastArr (_ , _ , _ , refl , _ , _) = S (_ , Step FHOuter ITApCast FHOuter)
  progress hctxwf (TAAp wt1 wt2) | BV v | BV v₂
    with canonical-boxed-forms-arr wt1 v
  ... | CBFLam (_ , _ , refl , _)             = S (_ , Step FHOuter ITLam FHOuter)
  ... | CBFCastArr (_ , _ , _ , refl , _ , _) = S (_ , Step FHOuter ITApCast FHOuter)

    -- type applications
  
  -- progress hctxwf (TATAp wf wt eq) = {!   !}

  progress hctxwf (TATAp wf wt eq) with progress hctxwf wt 
  progress hctxwf (TATAp wf wt eq) | S (_ , Step x y z) = S (_ , (Step (FHTAp x) y (FHTAp z)))
  progress hctxwf (TATAp wf wt eq) | I x with canonical-indeterminate-forms-forall wt x 
  progress hctxwf (TATAp wf wt eq) | I x | CIFFEHole (_ , _ , _ , _ , _ , _ , refl , _) = I (ITAp (λ t1 t2 τ1 τ2 d' ()) x)
  progress hctxwf (TATAp wf wt eq) | I x | CIFFNEHole (_ , _ , _ , _ , _ , _ , _ , _ , refl , _) = I (ITAp (λ t1 t2 τ1 τ2 d' ()) x)
  progress hctxwf (TATAp wf wt eq) | I x | CIFFAp (_ , _ , _ , refl , _) = I (ITAp (λ t1 t2 τ1 τ2 d' ()) x)
  progress hctxwf (TATAp wf wt eq) | I x | CIFFTApForall (_ , _ , _ , _ , _ , refl , _ ) = I (ITAp (λ t1 t2 τ1 τ2 d' ()) x)
  progress hctxwf (TATAp wf wt eq) | I x | CIFFTApId (_ , _ , _ , refl , _ ) = I (ITAp (λ t1 t2 τ1 τ2 d' ()) x)
  progress hctxwf (TATAp wf wt eq) | I x | CIFFCast (a , d , e , _ , _ , refl , f , g , h) = S (_ , Step FHOuter ITTApCast FHOuter)
  
  progress hctxwf (TATAp wf wt eq) | I x | CIFFCastHole (_ , refl , refl , _ ) = I (ITAp (λ t1 t2 τ1 τ2 d' ()) x)
  progress hctxwf (TATAp wf wt eq) | I x | CIFFFailedCast (_ , _ , refl , refl , _) = I (ITAp (λ t1 t2 τ1 τ2 d' ()) x)
  progress hctxwf (TATAp wf wt eq) | (BV v) with canonical-boxed-forms-forall wt v 
  progress hctxwf (TATAp wf wt eq) | (BV v) | CBFTLam (x , y , z) rewrite y = S (_ , Step FHOuter ITTLam FHOuter)
  progress hctxwf (TATAp wf wt eq) | (BV _) | CBFCastForall (_ , _ , _ , eq2 , neq , wt2) rewrite eq2 = S (_ , Step FHOuter ITTApCast FHOuter) 
  -- progress hctxwf (TATAp (TAEHole x x₁) eq) = I (ITAp (λ τ1 τ2 d' ()) IEHole)
  

    -- empty holes are indeterminate
  progress hctxwf (TAEHole _ _ _ ) = I IEHole

    -- nonempty holes step if the innards step, indet otherwise
  progress hctxwf (TANEHole xin wt x₁ eq)
    with progress hctxwf wt
  ... | S (_ , Step x y z) = S (_ , Step (FHNEHole x) y (FHNEHole z))
  ... | I  x = I (INEHole (FIndet x))
  ... | BV x = I (INEHole (FBoxedVal x))

    -- casts
  progress hctxwf (TACast wt wf con)
    with progress hctxwf wt
    -- step if the innards step
  progress hctxwf (TACast wt wf con) | S (_ , Step x y z) = S (_ , Step (FHCast x) y (FHCast z))
    -- if indet, inspect how the types in the cast are realted by consistency:
    -- if they're the same, step by ID
  -- progress (TACast wt wf TCRefl)  | I x = S (_ , Step FHOuter {! ITC  !} {!   !}) -- S (_ , Step FHOuter ITCastID FHOuter)
  progress hctxwf (TACast wt wf ConsistBase) | _ = S (_ , (Step FHOuter (ITCastID AlphaBase) FHOuter))
  progress hctxwf (TACast wt wf (ConsistVarFree f1 f2)) | _ = S (_ , (Step FHOuter (ITCastID (AlphaVarFree refl refl)) FHOuter))
  progress hctxwf (TACast wt wf (ConsistVarBound b1 b2)) | _ = S (_ , (Step FHOuter (ITCastID (AlphaVarBound b1 b2)) FHOuter))
    -- if first type is hole
  progress hctxwf (TACast {τ1 = τ1} wt wf ConsistHole1) | I x
    with τ1
  progress hctxwf (TACast wt wf ConsistHole1) | I x | b = I (ICastGroundHole GBase x)
  progress hctxwf (TACast wt wf ConsistHole1) | I x | T n with wf-ta (CCtx (λ ())) hctxwf wt 
  ... | WFVar ()
  progress hctxwf (TACast wt wf ConsistHole1) | I x | ⦇-⦈ = S (_ , Step FHOuter (ITCastID AlphaHole) FHOuter)
  progress hctxwf (TACast wt wf ConsistHole1) | I x | τ11 ==> τ12
    with ground-decidable (τ11 ==> τ12)
  progress hctxwf (TACast wt wf ConsistHole1) | I x₁ | .⦇-⦈ ==> .⦇-⦈ | Inl GArr = I (ICastGroundHole GArr x₁)
  progress hctxwf (TACast wt wf ConsistHole1) | I x₁ | τ11 ==> τ12 | Inr x =  S (_ , Step FHOuter (ITGround (MGArr (ground-arr-not-hole x))) FHOuter)
  progress hctxwf (TACast wt wf ConsistHole1) | I x | ·∀ t τ with ground-decidable (·∀ t τ)
  progress hctxwf (TACast wt wf ConsistHole1) | I x | ·∀ t .⦇-⦈ | Inl GForall = I (ICastGroundHole GForall x)
  progress hctxwf (TACast wt wf ConsistHole1) | I x₁ | ·∀ t τ | Inr x  = S (_ , Step FHOuter (ITGround (MGForall (ground-forall-not-hole x))) FHOuter)
    -- if second type is hole
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = b})) | I x
    with canonical-indeterminate-forms-hole wt x
  progress hctxwf (TACast wt wf (ConsistHole2)) | I x | CIFHEHole (_ , _ , _ , _ , _ , _ , refl , f)           = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress hctxwf (TACast wt wf (ConsistHole2)) | I x | CIFHNEHole (_ , _ , _ , _ , _ , _ , _ , _ , refl , _ ) = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress hctxwf (TACast wt wf (ConsistHole2)) | I x | CIFHAp (_ , _ , _ , refl , _ )             = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress hctxwf (TACast wt wf (ConsistHole2)) | I x | CIFHTApHole (_ , _ , _ , refl , _ )        = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress hctxwf (TACast wt wf (ConsistHole2)) | I x | CIFHTApId (_ , _ , _ , refl , _ )          = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress hctxwf (TACast wt wf (ConsistHole2)) | I x | CIFHCast (_ , τ , refl , _)
    with htype-dec τ b
  progress hctxwf (TACast wt wf (ConsistHole2)) | I x₁ | CIFHCast (_ , .b , refl , _ , grn , _) | Inl refl = S (_ , Step FHOuter (ITCastSucceed grn grn AlphaBase) FHOuter)
  progress hctxwf (TACast wt wf (ConsistHole2)) | I x₁ | CIFHCast (_ , _ , refl , π2 , GBase , _) | Inr x =  S (_ , Step FHOuter (ITCastSucceed GBase GBase AlphaBase) FHOuter)  
  progress hctxwf (TACast wt wf (ConsistHole2)) | I x₁ | CIFHCast (_ , _ , refl , π2 , GArr , _) | Inr x = S (_ , Step FHOuter (ITCastFail GArr GBase λ ()) FHOuter)
  progress hctxwf (TACast wt wf (ConsistHole2)) | I x₁ | CIFHCast (_ , _ , refl , π2 , GForall , _) | Inr x = S (_ , Step FHOuter (ITCastFail GForall GBase λ ()) FHOuter)
  progress hctxwf (TACast wt (WFVar ()) (ConsistHole2 {τ = .(T _)})) | _
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = ⦇-⦈})) | I x = S (_ , Step FHOuter (ITCastID AlphaHole) FHOuter)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = τ11 ==> τ12})) | I x
    with ground-decidable (τ11 ==> τ12)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈})) | I x₁ | Inl GArr
    with canonical-indeterminate-forms-hole wt x₁
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈})) | I x | Inl GArr | CIFHEHole (_ , _ , _ , _ , _ , _ , refl , _)          = I (ICastHoleGround (λ _ _ ()) x GArr)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈})) | I x | Inl GArr | CIFHNEHole (_ , _ , _ , _ , _ , _ , _ , _ , refl , _) = I (ICastHoleGround (λ _ _ ()) x GArr)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈})) | I x | Inl GArr | CIFHAp (_ , _ , _ , refl , _ )            = I (ICastHoleGround (λ _ _ ()) x GArr)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈})) | I x | Inl GArr | CIFHTApHole (_ , _ , _ , refl , _ )            = I (ICastHoleGround (λ _ _ ()) x GArr)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈})) | I x | Inl GArr | CIFHTApId (_ , _ , _ , refl , _ )            = I (ICastHoleGround (λ _ _ ()) x GArr)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈})) | I x | Inl GArr | CIFHCast (_ , ._ , refl , _ , GBase , _)  = S (_ , Step FHOuter (ITCastFail GBase GArr (λ ())) FHOuter )
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈})) | I x | Inl GArr | CIFHCast (_ , ._ , refl , _ , GArr , _)  = S (_ , Step FHOuter (ITCastSucceed GArr GArr (AlphaArr AlphaHole AlphaHole)) FHOuter)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈})) | I x | Inl GArr | CIFHCast (_ , ._ , refl , _ , GForall , _)  = S (_ , Step FHOuter (ITCastFail GForall GArr (λ ())) FHOuter )
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = τ11 ==> τ12})) | I x₁ | Inr x = S (_ , Step FHOuter (ITExpand (MGArr (ground-arr-not-hole x))) FHOuter)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = ·∀ t τ})) | I x
    with ground-decidable (·∀ t τ)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = ·∀ t ⦇-⦈})) | I x | Inl GForall 
    with canonical-indeterminate-forms-hole wt x
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)})) | I x | Inl GForall | CIFHEHole (_ , _ , _ , _ , _ , _ , refl , _) = I (ICastHoleGround (λ d' τ' ()) x GForall)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)})) | I x | Inl GForall | CIFHNEHole (_ , _ , _ , _ , _ , _ , _ , _ , refl , _) = I (ICastHoleGround (λ d' τ' ()) x GForall)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)})) | I x | Inl GForall | CIFHAp (_ , _ , _ , refl , _ ) = I (ICastHoleGround (λ d' τ' ()) x GForall)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)})) | I x | Inl GForall | CIFHTApHole (_ , _ , _ , refl , _ ) = I (ICastHoleGround (λ d' τ' ()) x GForall)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)})) | I x | Inl GForall | CIFHTApId (_ , _ , _ , refl , _ )   = I (ICastHoleGround (λ d' τ' ()) x GForall)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)})) | I x | Inl GForall | CIFHCast (_ , ._ , refl , _ , GBase , _) = S (_ , Step FHOuter (ITCastFail GBase GForall (λ ())) FHOuter )
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)})) | I x | Inl GForall | CIFHCast (_ , ._ , refl , _ , GArr , _) = S (_ , Step FHOuter (ITCastFail GArr GForall (λ ())) FHOuter)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = (·∀ t ⦇-⦈)})) | I x | Inl GForall | CIFHCast (_ , ._ , refl , _ , GForall {t = t'} , _) = S (_ , Step FHOuter (ITCastSucceed GForall GForall (AlphaForall AlphaHole)) FHOuter)
  -- with natEQ t t' 
  -- progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)})) | I x | Inl GForall | CIFHCast (_ , .(·∀ _ ⦇-⦈) , refl , _ , GForall {_} , _) | Inl refl = S (_ , Step FHOuter (ITCastSucceed GForall GForall (AlphaForall AlphaHole)) FHOuter)
  -- progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)})) | I x | Inl GForall | CIFHCast (_ , .(·∀ _ ⦇-⦈) , refl , _ , GForall {_} , _) | Inr neq = S (_ , Step FHOuter (ITCastSucceed GForall GForall (AlphaForall AlphaHole)) FHOuter) -- {! λ x₁ → neq (forall-inj1 (sym x₁))!}
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = ·∀ _ τ})) | I x₁ | Inr x = S (_ , Step FHOuter (ITExpand (MGForall (ground-forall-not-hole x))) FHOuter)
    -- if both are arrows
  progress hctxwf (TACast wt wf (ConsistArr {τ1 = τ1} {τ2 = τ2} {τ3 = τ3} {τ4 = τ4} c1 c2)) | I x
    with alpha-dec (τ1 ==> τ2)  (τ3 ==> τ4)
  progress hctxwf (TACast wt wf (ConsistArr {τ1 = τ1} {τ2 = τ2} c1 c2)) | I x₁ | Inl eq = S (_ , Step FHOuter (ITCastID eq) FHOuter)
  progress hctxwf (TACast wt wf (ConsistArr c1 c2)) | I x₁ | Inr x = I (ICastArr x x₁)
    -- if both are foralls 
  progress hctxwf (TACast wt wf (ConsistForall {τ1 = τ1} {τ2 = τ2} {x = x'} {y = y} con)) | I x
    with alpha-dec (·∀ x' τ1) (·∀ y τ2) 
  progress hctxwf (TACast wt wf (ConsistForall {τ1 = τ1} {x = x'} con)) | I x | Inl eq = S (_ , Step FHOuter (ITCastID eq) FHOuter)
  progress hctxwf (TACast wt wf (ConsistForall con)) | I x₁ | Inr x = I (ICastForall x x₁)

    -- boxed value cases, inspect how the casts are realted by consistency
    -- step by ID if the casts are the same
  -- progress hctxwf (TACast wt wf TCRefl)  | BV x = {!   !} -- S (_ , Step FHOuter ITCastID FHOuter)
    -- if left is hole
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = τ})) | BV x
    with ground-decidable τ
  progress hctxwf (TACast wt wf ConsistHole1) | BV x₁ | Inl g = BV (BVHoleCast g x₁)
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = b})) | BV x₁ | Inr x = abort (x GBase)
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = T n})) | BV x₁ | Inr x with wf-ta (CCtx (λ ())) hctxwf wt 
  ... | WFVar ()
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = ⦇-⦈})) | BV x₁ | Inr x = S (_ , Step FHOuter (ITCastID AlphaHole) FHOuter)
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = τ1 ==> τ2})) | BV x₁ | Inr x
    with (htype-dec  (τ1 ==> τ2) (⦇-⦈ ==> ⦇-⦈))
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = .⦇-⦈ ==> .⦇-⦈})) | BV x₂ | Inr x₁ | Inl refl = BV (BVHoleCast GArr x₂)
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = τ1 ==> τ2})) | BV x₂ | Inr x₁ | Inr x = S (_ , Step FHOuter (ITGround (MGArr x)) FHOuter)
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = ·∀ t τ})) | BV x₁ | Inr x 
    with (htype-dec  (·∀ t τ) (·∀ t ⦇-⦈))
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = ·∀ _ .⦇-⦈})) | BV x₁ | Inr x | Inl refl = BV (BVHoleCast GForall x₁)
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = ·∀ _ τ})) | BV x₁ | Inr x₂ | Inr x = S (_ , Step FHOuter (ITGround (MGForall x)) FHOuter) 
    -- if right is hole
  progress {τ = τ} hctxwf (TACast wt wf ConsistHole2) | BV x
    with canonical-boxed-forms-hole wt x
  progress {τ = τ} hctxwf (TACast wt wf ConsistHole2) | BV x | d' , τ' , refl , gnd , wt'
    with alpha-dec τ τ'
  progress hctxwf (TACast wt wf ConsistHole2) | BV x₁ | d' , τ' , refl , gnd , wt' | Inl eq = S (_  , Step FHOuter (ITCastSucceed gnd (ground-alpha-ground gnd (alpha-sym eq)) (alpha-sym eq)) FHOuter)
  progress {τ = τ} hctxwf (TACast wt wf ConsistHole2) | BV x₁ | _ , _ , refl , _ , _ | Inr _
    with ground-decidable τ
  progress hctxwf (TACast wt wf ConsistHole2) | BV x₂ | _ , _ , refl , gnd , _ | Inr x₁ | Inl x = S(_ , Step FHOuter (ITCastFail gnd x λ x₃ → x₁ (ground-eq-~ x gnd (~sym x₃))) FHOuter)
  progress hctxwf (TACast wt wf ConsistHole2) | BV x₂ | _ , _ , refl , _ , _ | Inr x₁ | Inr x
    with notground x
  progress hctxwf (TACast wt wf ConsistHole2) | BV x₃ | _ , _ , refl , _ , _ | Inr _ | Inr _ | Inl refl = S (_ , Step FHOuter (ITCastID AlphaHole) FHOuter)
  progress {τ = _} hctxwf (TACast wt (WFVar ()) ConsistHole2) | BV x₃ | _ , _ , refl , gnd , _ | Inr _ | Inr x | Inr (Inl (_ , refl))
  progress hctxwf (TACast wt wf ConsistHole2) | BV x₃ | _ , _ , refl , _ , _ | Inr _ | Inr x | Inr (Inr (Inl (_ , _ , refl))) = S(_ , Step FHOuter (ITExpand (MGArr (ground-arr-not-hole x))) FHOuter )
  progress {τ = ·∀ t τ} hctxwf (TACast wt wf ConsistHole2) | BV x₃ | _ , _ , refl , _ , _ | Inr _ | Inr x | Inr (Inr (Inr (_ , (_ , refl)))) = S(_ , Step FHOuter (ITExpand (MGForall (ground-forall-not-hole x))) FHOuter )
    -- if both arrows
  progress hctxwf (TACast wt wf (ConsistArr {τ1 = τ1} {τ2 = τ2} {τ3 = τ3} {τ4 = τ4} c1 c2)) | BV x
    with alpha-dec (τ1 ==> τ2) (τ3 ==> τ4)
  progress hctxwf (TACast wt wf (ConsistArr {τ1 = τ1} {τ2 = τ2} c1 c2)) | BV x₁ | Inl eq = S (_ , Step FHOuter (ITCastID eq) FHOuter)
  progress hctxwf (TACast wt wf (ConsistArr c1 c2)) | BV x₁ | Inr x = BV (BVArrCast x x₁)
  progress hctxwf (TACast wt wf (ConsistForall {τ1 = τ1} {τ2 = τ2} {x = x'} {y = y} _)) | BV x
    with alpha-dec (·∀ x' τ1) (·∀ y τ2)
  progress hctxwf (TACast wt wf (ConsistForall {τ1 = τ1} {τ2 = τ2} {x = x'} _)) | BV x₁ | Inl eq = S (_ , Step FHOuter (ITCastID eq) FHOuter)
  progress hctxwf (TACast wt wf (ConsistForall {τ1 = τ1} {τ2 = τ2} _)) | BV x₁ | Inr x = BV (BVForallCast x x₁)

   -- failed casts
  progress hctxwf (TAFailedCast wt y z w)
    with progress hctxwf wt
  progress hctxwf (TAFailedCast wt y z w) | S (d' , Step x a q) = S (_ , Step (FHFailedCast x) a (FHFailedCast q))
  progress hctxwf (TAFailedCast wt y z w) | I x = I (IFailedCast (FIndet x) y z (λ x₁ → w (alpha-~ x₁)))
  progress hctxwf (TAFailedCast wt y z w) | BV x = I (IFailedCast (FBoxedVal x) y z (λ x₁ → w (alpha-~ x₁)))
 