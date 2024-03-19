{-# OPTIONS --allow-unsolved-metas #-}

open import Nat
open import Prelude
open import core
open alpha
open import lemmas-alpha

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

  progress hctxwf (TATLam apt wt) = BV (BVVal VTLam)

    -- applications
  progress hctxwf (TAAp wt1 wt2 eq)
    with progress hctxwf wt1 | progress hctxwf wt2
    -- if the left steps, the whole thing steps
  progress hctxwf (TAAp wt1 wt2 eq) | S (_ , Step x y z) | _ = S (_ , Step (FHAp1 x) y (FHAp1 z))
    -- if the left is indeterminate, step the right
  progress hctxwf (TAAp wt1 wt2 eq) | I i | S (_ , Step x y z) = S (_ , Step (FHAp2 x) y (FHAp2  z))
    -- if they're both indeterminate, step when the cast steps and indet otherwise
  progress hctxwf (TAAp wt1 wt2 eq) | I x | I x₁
    with canonical-indeterminate-forms-arr wt1 x
  progress hctxwf (TAAp wt1 wt2 eq) | I x | I y | CIFACast (_ , _ , _ , _ , _ , _ , refl , _ , _ ) = S (_ , Step FHOuter ITApCast FHOuter)
  progress hctxwf (TAAp wt1 wt2 eq) | I x | I y | CIFAEHole (_ , _ , _ , _ , _ , _ , _ , refl , _)             = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress hctxwf (TAAp wt1 wt2 eq) | I x | I y | CIFANEHole (_ , _ , _ , _ , _ , _ , _ , _ , _ , refl , _)    = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress hctxwf (TAAp wt1 wt2 eq) | I x | I y | CIFAAp (_ , _ , _ , _ , _ , _ , refl , _)        = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress hctxwf (TAAp wt1 wt2 eq) | I x | I y | CIFATApArr (_ , _ , _ , _ , _ , refl , _ , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress hctxwf (TAAp wt1 wt2 eq) | I x | I y | CIFATApId (_ , _ , _ , _ , refl , _ , _ )        = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress hctxwf (TAAp wt1 wt2 eq) | I x | I y | CIFACastHole (_ , refl , refl , refl , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress hctxwf (TAAp wt1 wt2 eq) | I x | I y | CIFAFailedCast (_ , _ , _ , refl , _ )           = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
    -- similar if the left is indetermiante but the right is a boxed val
  progress hctxwf (TAAp wt1 wt2 eq) | I x | BV x₁
    with canonical-indeterminate-forms-arr wt1 x
  progress hctxwf (TAAp wt1 wt2 eq) | I x | BV y | CIFACast (_ , _ , _ , _ , _ , _ , refl , _ , _ ) = S (_ , Step FHOuter ITApCast FHOuter)
  progress hctxwf (TAAp wt1 wt2 eq) | I x | BV y | CIFAEHole (_ , _ , _ , _ , _ , _ , _ , refl , _)             = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress hctxwf (TAAp wt1 wt2 eq) | I x | BV y | CIFANEHole (_ , _ , _ , _ , _ , _ , _ , _ , _ , refl , _)    = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress hctxwf (TAAp wt1 wt2 eq) | I x | BV y | CIFAAp (_ , _ , _ , _ , _ , _ , refl , _)        = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress hctxwf (TAAp wt1 wt2 eq) | I x | BV y | CIFATApArr (_ , _ , _ , _ , _ , refl , _ , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress hctxwf (TAAp wt1 wt2 eq) | I x | BV y | CIFATApId (_ , _ , _ , _ , refl , _ , _ )        = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress hctxwf (TAAp wt1 wt2 eq) | I x | BV y | CIFACastHole (_ , refl , refl , refl , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress hctxwf (TAAp wt1 wt2 eq) | I x | BV y | CIFAFailedCast (_ , _ , _ , refl , _ )           = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
    -- if the left is a boxed value, inspect the right
  progress hctxwf (TAAp wt1 wt2 eq) | BV v | S (_ , Step x y z) = S (_ , Step (FHAp2  x) y (FHAp2  z))
  progress hctxwf (TAAp wt1 wt2 eq) | BV v | I i
    with canonical-boxed-forms-arr wt1 v
  ... | CBFLam (_ , _ , refl , _)             = S (_ , Step FHOuter ITLam FHOuter)
  ... | CBFCastArr (_ , _ , _ , _ , refl , _ , _) = S (_ , Step FHOuter ITApCast FHOuter)
  progress hctxwf (TAAp wt1 wt2 eq) | BV v | BV v₂
    with canonical-boxed-forms-arr wt1 v
  ... | CBFLam (_ , _ , refl , _)             = S (_ , Step FHOuter ITLam FHOuter)
  ... | CBFCastArr (_ , _ , _ , _ , refl , _ , _) = S (_ , Step FHOuter ITApCast FHOuter)

    -- type applications
  
  -- progress hctxwf (TATAp wf wt eq) = {!   !}

  progress hctxwf (TATAp wf wt eq) with progress hctxwf wt 
  progress hctxwf (TATAp wf wt eq) | S (_ , Step x y z) = S (_ , (Step (FHTAp x) y (FHTAp z)))
  progress hctxwf (TATAp wf wt eq) | I x with canonical-indeterminate-forms-forall wt x 
  progress hctxwf (TATAp wf wt eq) | I x | CIFFEHole (_ , _ , _ , _ , _ , _ , _ , refl , _) = I (ITAp (λ t1 t2 τ1 τ2 d' ()) x)
  progress hctxwf (TATAp wf wt eq) | I x | CIFFNEHole (_ , _ , _ , _ , _ , _ , _ , _ , _ , refl , _) = I (ITAp (λ t1 t2 τ1 τ2 d' ()) x)
  progress hctxwf (TATAp wf wt eq) | I x | CIFFAp (_ , _ , _ , _ , refl , _) = I (ITAp (λ t1 t2 τ1 τ2 d' ()) x)
  progress hctxwf (TATAp wf wt eq) | I x | CIFFTApForall (_ , _ , _ , _ , _ , refl , _ ) = I (ITAp (λ t1 t2 τ1 τ2 d' ()) x)
  progress hctxwf (TATAp wf wt eq) | I x | CIFFTApId (_ , _ , _ , refl , _ ) = I (ITAp (λ t1 t2 τ1 τ2 d' ()) x)
  progress hctxwf (TATAp wf wt eq) | I x | CIFFCast (a , d , e , _ , _ , _ , refl , f , g , h) = S (_ , Step FHOuter ITTApCast FHOuter)
  
  progress hctxwf (TATAp wf wt eq) | I x | CIFFCastHole (_ , _ , refl , refl , _ ) = I (ITAp (λ t1 t2 τ1 τ2 d' ()) x)
  progress hctxwf (TATAp wf wt eq) | I x | CIFFFailedCast (_ , _ , _ , refl , refl , _) = I (ITAp (λ t1 t2 τ1 τ2 d' ()) x)
  progress hctxwf (TATAp wf wt eq) | (BV v) with canonical-boxed-forms-forall wt v 
  progress hctxwf (TATAp wf wt eq) | (BV v) | CBFTLam (x , y , z) rewrite y = S (_ , Step FHOuter ITTLam FHOuter)
  progress hctxwf (TATAp wf wt eq) | (BV _) | CBFCastForall (_ , _ , _ , _ , eq2 , neq , wt2) rewrite eq2 = S (_ , Step FHOuter ITTApCast FHOuter) 
  -- progress hctxwf (TATAp (TAEHole x x₁) eq) = I (ITAp (λ τ1 τ2 d' ()) IEHole)
  

    -- empty holes are indeterminate
  progress hctxwf (TAEHole _ _ _ _ ) = I IEHole

    -- nonempty holes step if the innards step, indet otherwise
  progress hctxwf (TANEHole xin wt x₁ eq eq2)
    with progress hctxwf wt
  ... | S (_ , Step x y z) = S (_ , Step (FHNEHole x) y (FHNEHole z))
  ... | I  x = I (INEHole (FIndet x))
  ... | BV x = I (INEHole (FBoxedVal x))

    -- casts
  progress hctxwf (TACast wt wf con eq)
    with progress hctxwf wt
    -- step if the innards step
  progress hctxwf (TACast wt wf con eq) | S (_ , Step x y z) = S (_ , Step (FHCast x) y (FHCast z))
    -- if indet, inspect how the types in the cast are realted by consistency:
    -- if they're the same, step by ID
  -- progress (TACast wt wf TCRefl)  | I x = S (_ , Step FHOuter {! ITC  !} {!   !}) -- S (_ , Step FHOuter ITCastID FHOuter)
  progress hctxwf (TACast wt wf ConsistBase eq) | _ = S (_ , (Step FHOuter (ITCastID AlphaBase) FHOuter))
  progress hctxwf (TACast wt wf (ConsistVarFree f1 f2) eq) | _ = S (_ , (Step FHOuter (ITCastID (AlphaVarFree refl refl)) FHOuter))
  progress hctxwf (TACast wt wf (ConsistVarBound b1 b2) eq) | _ = S (_ , (Step FHOuter (ITCastID (AlphaVarBound b1 b2)) FHOuter))
    -- if first type is hole
  progress hctxwf (TACast {τ1 = τ1} wt wf ConsistHole1 eq) | I x
    with τ1
  progress hctxwf (TACast wt wf ConsistHole1 eq) | I x | b = I (ICastGroundHole GBase x)
  progress hctxwf (TACast wt wf ConsistHole1 eq) | I x | T n with wf-ta {!   !} (CCtx (λ ())) hctxwf wt 
  ... | WFVar ()
  progress hctxwf (TACast wt wf ConsistHole1 eq) | I x | ⦇-⦈ = S (_ , Step FHOuter (ITCastID AlphaHole) FHOuter)
  progress hctxwf (TACast wt wf ConsistHole1 eq) | I x | τ11 ==> τ12
    with ground-decidable (τ11 ==> τ12)
  progress hctxwf (TACast wt wf ConsistHole1 eq) | I x₁ | .⦇-⦈ ==> .⦇-⦈ | Inl GArr = I (ICastGroundHole GArr x₁)
  progress hctxwf (TACast wt wf ConsistHole1 eq) | I x₁ | τ11 ==> τ12 | Inr x =  S (_ , Step FHOuter (ITGround (MGArr (ground-arr-not-hole x))) FHOuter)
  progress hctxwf (TACast wt wf ConsistHole1 eq) | I x | ·∀ t τ with ground-decidable (·∀ t τ)
  progress hctxwf (TACast wt wf ConsistHole1 eq) | I x | ·∀ t .⦇-⦈ | Inl GForall = I (ICastGroundHole GForall x)
  progress hctxwf (TACast wt wf ConsistHole1 eq) | I x₁ | ·∀ t τ | Inr x  = S (_ , Step FHOuter (ITGround (MGForall (ground-forall-not-hole x))) FHOuter)
    -- if second type is hole
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = b}) eq) | I x
    rewrite (alpha-hole _ (alpha-sym eq))
    with canonical-indeterminate-forms-hole wt x
  progress hctxwf (TACast wt wf ConsistHole2 eq) | I x | CIFHEHole (_ , _ , _ , _ , _ , _ , _ , refl , f)           = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress hctxwf (TACast wt wf ConsistHole2 eq) | I x | CIFHNEHole (_ , _ , _ , _ , _ , _ , _ , _ , _ , refl , _ ) = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress hctxwf (TACast wt wf ConsistHole2 eq) | I x | CIFHAp (_ , _ , _ , _ , refl , _ )             = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress hctxwf (TACast wt wf ConsistHole2 eq) | I x | CIFHTApHole (_ , _ , _ , refl , _ )        = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress hctxwf (TACast wt wf ConsistHole2 eq) | I x | CIFHTApId (_ , _ , _ , refl , _ )          = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress hctxwf (TACast wt wf ConsistHole2 eq) | I x | CIFHCast (_ , τ , _ , refl , _)
    with htype-dec τ b
  progress hctxwf (TACast wt wf ConsistHole2 eq) | I x₁ | CIFHCast (_ , .b , _ , refl , _ , _ , grn , _) | Inl refl = S (_ , Step FHOuter (ITCastSucceed grn grn AlphaBase) FHOuter)
  progress hctxwf (TACast wt wf ConsistHole2 eq) | I x₁ | CIFHCast (_ , _ , _ , refl , π2 , _ , GBase , _) | Inr x =  S (_ , Step FHOuter (ITCastSucceed GBase GBase AlphaBase) FHOuter)  
  progress hctxwf (TACast wt wf ConsistHole2 eq) | I x₁ | CIFHCast (_ , _ , _ , refl , π2 , _ , GArr , _) | Inr x = S (_ , Step FHOuter (ITCastFail GArr GBase λ ()) FHOuter)
  progress hctxwf (TACast wt wf ConsistHole2 eq) | I x₁ | CIFHCast (_ , _ , _ , refl , π2 , _ , GForall , _) | Inr x = S (_ , Step FHOuter (ITCastFail GForall GBase λ ()) FHOuter)
  progress hctxwf (TACast wt (WFVar ()) (ConsistHole2 {τ = .(T _)}) eq) | _
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = ⦇-⦈}) eq) | I x = S (_ , Step FHOuter (ITCastID AlphaHole) FHOuter)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = τ11 ==> τ12}) eq) | I x
    with ground-decidable (τ11 ==> τ12)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈}) eq) | I x₁ | Inl GArr
    rewrite (alpha-hole _ (alpha-sym eq))
    with canonical-indeterminate-forms-hole wt x₁
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈}) eq) | I x | Inl GArr | CIFHEHole (_ , _ , _ , _ , _ , _ , _ , refl , _)          = I (ICastHoleGround (λ _ _ ()) x GArr)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈}) eq) | I x | Inl GArr | CIFHNEHole (_ , _ , _ , _ , _ , _ , _ , _ , _ , refl , _) = I (ICastHoleGround (λ _ _ ()) x GArr)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈}) eq) | I x | Inl GArr | CIFHAp (_ , _ , _ , _ , refl , _ )            = I (ICastHoleGround (λ _ _ ()) x GArr)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈}) eq) | I x | Inl GArr | CIFHTApHole (_ , _ , _ , refl , _ )            = I (ICastHoleGround (λ _ _ ()) x GArr)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈}) eq) | I x | Inl GArr | CIFHTApId (_ , _ , _ , refl , _ )            = I (ICastHoleGround (λ _ _ ()) x GArr)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈}) eq) | I x | Inl GArr | CIFHCast (_ , ._ , _ , refl , _ , _ , GBase , _)  = S (_ , Step FHOuter (ITCastFail GBase GArr (λ ())) FHOuter )
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈}) eq) | I x | Inl GArr | CIFHCast (_ , ._ , _ , refl , _ , _ , GArr , _)  = S (_ , Step FHOuter (ITCastSucceed GArr GArr (AlphaArr AlphaHole AlphaHole)) FHOuter)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .⦇-⦈ ==> .⦇-⦈}) eq) | I x | Inl GArr | CIFHCast (_ , ._ , _ , refl , _ , _ , GForall , _)  = S (_ , Step FHOuter (ITCastFail GForall GArr (λ ())) FHOuter )
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = τ11 ==> τ12}) eq) | I x₁ | Inr x = S (_ , Step FHOuter (ITExpand (MGArr (ground-arr-not-hole x))) FHOuter)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = ·∀ t τ}) eq) | I x
    with ground-decidable (·∀ t τ)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = ·∀ t ⦇-⦈}) eq) | I x | Inl GForall 
    rewrite (alpha-hole _ (alpha-sym eq))
    with canonical-indeterminate-forms-hole wt x
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)}) eq) | I x | Inl GForall | CIFHEHole (_ , _ , _ , _ , _ , _ , _ , refl , _) = I (ICastHoleGround (λ d' τ' ()) x GForall)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)}) eq) | I x | Inl GForall | CIFHNEHole (_ , _ , _ , _ , _ , _ , _ , _ , _ , refl , _) = I (ICastHoleGround (λ d' τ' ()) x GForall)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)}) eq) | I x | Inl GForall | CIFHAp (_ , _ , _ , _ , refl , _ ) = I (ICastHoleGround (λ d' τ' ()) x GForall)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)}) eq) | I x | Inl GForall | CIFHTApHole (_ , _ , _ , refl , _ ) = I (ICastHoleGround (λ d' τ' ()) x GForall)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)}) eq) | I x | Inl GForall | CIFHTApId (_ , _ , _ , refl , _ )   = I (ICastHoleGround (λ d' τ' ()) x GForall)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)}) eq) | I x | Inl GForall | CIFHCast (_ , ._ , _ , refl , _ , _ , GBase , _) = S (_ , Step FHOuter (ITCastFail GBase GForall (λ ())) FHOuter )
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)}) eq) | I x | Inl GForall | CIFHCast (_ , ._ , _ , refl , _ , _ , GArr , _) = S (_ , Step FHOuter (ITCastFail GArr GForall (λ ())) FHOuter)
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = (·∀ t ⦇-⦈)}) eq) | I x | Inl GForall | CIFHCast (_ , ._ , _ , refl , _ , _ , GForall {t = t'} , _) = S (_ , Step FHOuter (ITCastSucceed GForall GForall (AlphaForall AlphaHole)) FHOuter)
  -- with natEQ t t' 
  -- progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)}) eq) | I x | Inl GForall | CIFHCast (_ , .(·∀ _ ⦇-⦈) , refl , _ , GForall {_} , _) | Inl refl = S (_ , Step FHOuter (ITCastSucceed GForall GForall (AlphaForall AlphaHole)) FHOuter)
  -- progress hctxwf (TACast wt wf (ConsistHole2 {τ = .(·∀ _ ⦇-⦈)}) eq) | I x | Inl GForall | CIFHCast (_ , .(·∀ _ ⦇-⦈) , refl , _ , GForall {_} , _) | Inr neq = S (_ , Step FHOuter (ITCastSucceed GForall GForall (AlphaForall AlphaHole)) FHOuter) -- {! λ x₁ → neq (forall-inj1 (sym x₁))!}
  progress hctxwf (TACast wt wf (ConsistHole2 {τ = ·∀ _ τ}) eq) | I x₁ | Inr x = S (_ , Step FHOuter (ITExpand (MGForall (ground-forall-not-hole x))) FHOuter)
    -- if both are arrows
  progress hctxwf (TACast wt wf (ConsistArr {τ1 = τ1} {τ2 = τ2} {τ3 = τ3} {τ4 = τ4} c1 c2) eq) | I x
    with alpha-dec (τ1 ==> τ2)  (τ3 ==> τ4)
  progress hctxwf (TACast wt wf (ConsistArr {τ1 = τ1} {τ2 = τ2} c1 c2) _) | I x₁ | Inl eq = S (_ , Step FHOuter (ITCastID eq) FHOuter)
  progress hctxwf (TACast wt wf (ConsistArr c1 c2) eq) | I x₁ | Inr x = I (ICastArr x x₁)
    -- if both are foralls 
  progress hctxwf (TACast wt wf (ConsistForall {τ1 = τ1} {τ2 = τ2} {x = x'} {y = y} con) eq) | I x
    with alpha-dec (·∀ x' τ1) (·∀ y τ2) 
  progress hctxwf (TACast wt wf (ConsistForall {τ1 = τ1} {x = x'} con) _) | I x | Inl eq = S (_ , Step FHOuter (ITCastID eq) FHOuter)
  progress hctxwf (TACast wt wf (ConsistForall con) eq) | I x₁ | Inr x = I (ICastForall x x₁)

    -- boxed value cases, inspect how the casts are realted by consistency
    -- step by ID if the casts are the same
  -- progress hctxwf (TACast wt wf TCRefl)  | BV x = {!   !} -- S (_ , Step FHOuter ITCastID FHOuter)
    -- if left is hole
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = τ}) eq) | BV x
    with ground-decidable τ
  progress hctxwf (TACast wt wf ConsistHole1 eq) | BV x₁ | Inl g = BV (BVHoleCast g x₁)
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = b}) eq) | BV x₁ | Inr x = abort (x GBase)
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = T n}) eq) | BV x₁ | Inr x with wf-ta {!   !} (CCtx (λ ())) hctxwf wt 
  ... | WFVar ()
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = ⦇-⦈}) eq) | BV x₁ | Inr x = S (_ , Step FHOuter (ITCastID AlphaHole) FHOuter)
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = τ1 ==> τ2}) eq) | BV x₁ | Inr x
    with (htype-dec  (τ1 ==> τ2) (⦇-⦈ ==> ⦇-⦈))
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = .⦇-⦈ ==> .⦇-⦈}) eq) | BV x₂ | Inr x₁ | Inl refl = BV (BVHoleCast GArr x₂)
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = τ1 ==> τ2}) eq) | BV x₂ | Inr x₁ | Inr x = S (_ , Step FHOuter (ITGround (MGArr x)) FHOuter)
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = ·∀ t τ}) eq) | BV x₁ | Inr x 
    with (htype-dec  (·∀ t τ) (·∀ t ⦇-⦈))
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = ·∀ _ .⦇-⦈}) eq) | BV x₁ | Inr x | Inl refl = BV (BVHoleCast GForall x₁)
  progress hctxwf (TACast wt wf (ConsistHole1 {τ = ·∀ _ τ}) eq) | BV x₁ | Inr x₂ | Inr x = S (_ , Step FHOuter (ITGround (MGForall x)) FHOuter) 
    -- if right is hole
  progress {τ = τ} hctxwf (TACast wt wf ConsistHole2 eq) | BV x
    rewrite (alpha-hole _ (alpha-sym eq))
    with canonical-boxed-forms-hole wt x
  progress {τ = τ} hctxwf (TACast wt wf ConsistHole2 eq) | BV x | d' , τ' , _ , refl , gnd , wt'
    with alpha-dec τ τ'
  progress hctxwf (TACast wt wf ConsistHole2 _) | BV x₁ | d' , τ' , _ , refl , gnd , wt' | Inl eq = S (_  , Step FHOuter (ITCastSucceed gnd (ground-alpha-ground gnd (alpha-sym eq)) (alpha-sym eq)) FHOuter)
  progress {τ = τ} hctxwf (TACast wt wf ConsistHole2 eq) | BV x₁ | _ , _ , _ , refl , _ , _ | Inr _
    with ground-decidable τ
  progress hctxwf (TACast wt wf ConsistHole2 eq) | BV x₂ | _ , _ , _ , refl , gnd , _ | Inr x₁ | Inl x = S(_ , Step FHOuter (ITCastFail gnd x λ x₃ → x₁ (ground-eq-~ x gnd (~sym x₃))) FHOuter)
  progress hctxwf (TACast wt wf ConsistHole2 eq) | BV x₂ | _ , _ , _ , refl , _ , _ | Inr x₁ | Inr x
    with notground x
  progress hctxwf (TACast wt wf ConsistHole2 eq) | BV x₃ | _ , _ , _ , refl , _ , _ | Inr _ | Inr _ | Inl refl = S (_ , Step FHOuter (ITCastID AlphaHole) FHOuter)
  progress {τ = _} hctxwf (TACast wt (WFVar ()) ConsistHole2 eq) | BV x₃ | _ , _ , _ , refl , gnd , _ | Inr _ | Inr x | Inr (Inl (_ , refl))
  progress hctxwf (TACast wt wf ConsistHole2 eq) | BV x₃ | _ , _ , _ , refl , _ , _ | Inr _ | Inr x | Inr (Inr (Inl (_ , _ , refl))) = S(_ , Step FHOuter (ITExpand (MGArr (ground-arr-not-hole x))) FHOuter )
  progress {τ = ·∀ t τ} hctxwf (TACast wt wf ConsistHole2 eq) | BV x₃ | _ , _ , _ , refl , _ , _ | Inr _ | Inr x | Inr (Inr (Inr (_ , (_ , refl)))) = S(_ , Step FHOuter (ITExpand (MGForall (ground-forall-not-hole x))) FHOuter )
    -- if both arrows
  progress hctxwf (TACast wt wf (ConsistArr {τ1 = τ1} {τ2 = τ2} {τ3 = τ3} {τ4 = τ4} c1 c2) eq) | BV x
    with alpha-dec (τ1 ==> τ2) (τ3 ==> τ4)
  progress hctxwf (TACast wt wf (ConsistArr {τ1 = τ1} {τ2 = τ2} c1 c2) _) | BV x₁ | Inl eq = S (_ , Step FHOuter (ITCastID eq) FHOuter)
  progress hctxwf (TACast wt wf (ConsistArr c1 c2) eq) | BV x₁ | Inr x = BV (BVArrCast x x₁)
  progress hctxwf (TACast wt wf (ConsistForall {τ1 = τ1} {τ2 = τ2} {x = x'} {y = y} _) eq) | BV x
    with alpha-dec (·∀ x' τ1) (·∀ y τ2)
  progress hctxwf (TACast wt wf (ConsistForall {τ1 = τ1} {τ2 = τ2} {x = x'} _) _) | BV x₁ | Inl eq = S (_ , Step FHOuter (ITCastID eq) FHOuter)
  progress hctxwf (TACast wt wf (ConsistForall {τ1 = τ1} {τ2 = τ2} _) eq) | BV x₁ | Inr x = BV (BVForallCast x x₁)

   -- failed casts
  progress hctxwf (TAFailedCast wt y z w eq)
    with progress hctxwf wt
  progress hctxwf (TAFailedCast wt y z w eq) | S (d' , Step x a q) = S (_ , Step (FHFailedCast x) a (FHFailedCast q))
  progress hctxwf (TAFailedCast wt y z w eq) | I x = I (IFailedCast (FIndet x) y z (λ x₁ → w (alpha-~ x₁)))
  progress hctxwf (TAFailedCast wt y z w eq) | BV x = I (IFailedCast (FBoxedVal x) y z (λ x₁ → w (alpha-~ x₁)))
 