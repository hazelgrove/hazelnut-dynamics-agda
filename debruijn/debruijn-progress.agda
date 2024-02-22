open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
open import debruijn.debruijn-core

open import debruijn.debruijn-eq-dec
open import debruijn.debruijn-ground-dec

open import debruijn.debruijn-lemmas-consistency
open import debruijn.debruijn-lemmas-wf
open import debruijn.debruijn-lemmas-ground

module debruijn.debruijn-progress where

  data ok : (d : ihexp) → Set where
    S  : ∀{d} → Σ[ d' ∈ ihexp ] (d ↦ d') → ok d
    I  : ∀{d} → d indet → ok d
    BV : ∀{d} → d boxedval → ok d

  progress : {d : ihexp} {τ : htyp} →
    ∅ ⊢ d :: τ →
    ok d
  progress TAConst = BV (BVVal VConst) 
  progress (TALam x wt) = BV (BVVal VLam)
  progress (TATLam wt) = BV (BVVal VTLam)
  progress (TAEHole x) = I IEHole
  progress (TANEHole x wt) with progress wt 
  ... | S (_ , Step x y z) = S (_ , (Step (FHNEHole x) y (FHNEHole z)))
  ... | I x = I (INEHole (FIndet x))
  ... | BV x = I (INEHole (FBoxedVal x))
  progress (TAFailedCast wt y z w) with progress wt
  ... | S (d' , Step x a q) = S (_ , Step (FHFailedCast x) a (FHFailedCast q))
  ... | I x = I (IFailedCast (FIndet x) y z λ eq → w (~refl-convenience eq))
  ... | BV x = I (IFailedCast (FBoxedVal x) y z (λ eq → w (~refl-convenience eq)))
  progress (TATAp wf wt refl) with progress wt 
  ... | S (_ , Step x y z) = S (_ , (Step (FHTAp x) y (FHTAp z)))
  ... | I IEHole = I (ITAp (λ τ1 τ2 d' ()) IEHole)
  ... | I (INEHole x) = I (ITAp (λ τ1 τ2 d' ()) (INEHole x))
  ... | I (IAp x ind x₁) = I (ITAp (λ τ1 τ2 d' ()) (IAp x ind x₁))
  ... | I (ITAp x ind) = I (ITAp (λ τ1 τ2 d' ()) (ITAp x ind))
  ... | I (ICastForall x ind) = S (_ , Step FHOuter ITTApCast FHOuter)
  ... | I (ICastHoleGround x ind x₁) = I (ITAp (λ τ1 τ2 d' ()) (ICastHoleGround x ind x₁))
  ... | I (IFailedCast x x₁ x₂ x₃) = I (ITAp (λ τ1 τ2 d' ()) (IFailedCast x x₁ x₂ x₃))
  ... | BV (BVVal VTLam) = S (_ , Step FHOuter ITTLam FHOuter)
  ... | BV (BVForallCast neq bv) = S (_ , Step FHOuter ITTApCast FHOuter) 
  
  progress (TAAp wt1 wt2) with progress wt1 | progress wt2
  ... | S (_ , Step x y z) | _ = S (_ , Step (FHAp1 x) y (FHAp1 z))
  ... | I _ | S (_ , Step x y z) = S (_ , Step (FHAp2 x) y (FHAp2  z))
  ... | I (ICastArr x ind) | I x₁ = S (_ , Step FHOuter ITApCast FHOuter)
  ... | I (ICastArr x ind) | BV x₁ = S (_ , Step FHOuter ITApCast FHOuter)
  ... | I IEHole | I x = I (IAp (λ _ _ _ _ _ ()) IEHole (FIndet x))
  ... | I IEHole | BV x = I (IAp (λ _ _ _ _ _ ()) IEHole (FBoxedVal x))
  ... | I (INEHole x) | I x₁ = I (IAp (λ _ _ _ _ _ ()) (INEHole x) (FIndet x₁))
  ... | I (INEHole x) | BV x₁ = I (IAp (λ _ _ _ _ _ ()) (INEHole x) (FBoxedVal x₁))
  ... | I (IAp x ind x₁) | I x₂ = I (IAp (λ _ _ _ _ _ ()) (IAp x ind x₁) (FIndet x₂))
  ... | I (IAp x ind x₁) | BV x₂ = I (IAp (λ _ _ _ _ _ ()) (IAp x ind x₁) (FBoxedVal x₂))
  ... | I (ITAp x ind) | I x₁ = I (IAp (λ _ _ _ _ _ ()) (ITAp x ind) (FIndet x₁))
  ... | I (ITAp x ind) | BV x₁ = I (IAp (λ _ _ _ _ _ ()) (ITAp x ind) (FBoxedVal x₁))
  ... | I (ICastHoleGround x ind x₁) | I x₂ = I (IAp (λ _ _ _ _ _ ()) (ICastHoleGround x ind x₁) (FIndet x₂))
  ... | I (ICastHoleGround x ind x₁) | BV x₂ = I (IAp (λ _ _ _ _ _ ()) (ICastHoleGround x ind x₁) (FBoxedVal x₂))
  ... | I (IFailedCast x x₁ x₂ x₃) | I x₄ = I (IAp (λ _ _ _ _ _ ()) (IFailedCast x x₁ x₂ x₃) (FIndet x₄))
  ... | I (IFailedCast x x₁ x₂ x₃) | BV x₄ = I (IAp (λ _ _ _ _ _ ()) (IFailedCast x x₁ x₂ x₃) (FBoxedVal x₄))
  ... | BV bv | S (_ , Step x y z) = S (_ , Step (FHAp2  x) y (FHAp2  z))
  ... | BV (BVVal VLam) | I x = S (_ , Step FHOuter ITLam FHOuter)
  ... | BV (BVVal VLam) | BV x = S (_ , Step FHOuter ITLam FHOuter)
  ... | BV (BVArrCast x₁ bv) | I x = S (_ , Step FHOuter ITApCast FHOuter)
  ... | BV (BVArrCast x₁ bv) | BV x = S (_ , Step FHOuter ITApCast FHOuter)
 
  progress (TACast wt wf con) with progress wt
  progress (TACast wt wf con) | S (_ , Step x y z) = S (_ , Step (FHCast x) y (FHCast z))
  progress (TACast wt wf ConsistBase) | x =  S (_ , (Step FHOuter ITCastID FHOuter))
  progress (TACast wt wf (ConsistArr {τ1 = τ1} {τ2 = τ2} {τ3 = τ3} {τ4 = τ4} con1 con2)) | I x with htyp-eq-dec (τ1 ==> τ2) (τ3 ==> τ4) 
  ... | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  ... | Inr neq =  I (ICastArr neq x)
  progress (TACast wt wf (ConsistArr {τ1 = τ1} {τ2 = τ2} {τ3 = τ3} {τ4 = τ4} con1 con2)) | BV x with htyp-eq-dec (τ1 ==> τ2) (τ3 ==> τ4) 
  ... | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  ... | Inr neq = BV (BVArrCast neq x)
  progress (TACast wt wf (ConsistForall {τ1 = τ1} {τ2 = τ2} con)) | I x with htyp-eq-dec (·∀ τ1) (·∀ τ2)
  ... | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  ... | Inr neq = I (ICastForall neq x)
  progress (TACast wt wf (ConsistForall {τ1 = τ1} {τ2 = τ2} con)) | BV x with htyp-eq-dec (·∀ τ1) (·∀ τ2)
  ... | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  ... | Inr neq = BV (BVForallCast neq x)

  progress {_ ⟨ b ⇒ _ ⟩} (TACast wt wf ConsistHole1) | I x = I (ICastGroundHole GBase x)
  progress {_ ⟨ T _ ⇒ _ ⟩} (TACast wt wf ConsistHole1) | I x with wf-ta CtxWFEmpty wt 
  ... | ()
  progress {_ ⟨ ⦇-⦈ ⇒ _ ⟩} (TACast wt wf ConsistHole1) | I x = S (_ , Step FHOuter ITCastID FHOuter)
  progress {_ ⟨ τ1 ==> τ2 ⇒ _ ⟩} (TACast wt wf ConsistHole1) | I x with ground-dec (τ1 ==> τ2) 
  ... | Inl GArr = I (ICastGroundHole GArr x)
  ... | Inr ngdn = S (_ , Step FHOuter (ITGround (MGArr (ground-arr-not-hole ngdn))) FHOuter)
  progress {_ ⟨ ·∀ τ ⇒ _ ⟩} (TACast wt wf ConsistHole1) | I x with ground-dec (·∀ τ) 
  ... | Inl GForall = I (ICastGroundHole GForall x)
  ... | Inr ngdn = S (_ , Step FHOuter (ITGround (MGForall (ground-forall-not-hole ngdn))) FHOuter)
  
  progress (TACast (TACast wt x₃ x₄) wf ConsistHole2) | I (ICastHoleGround x x₁ x₂) = S (_ , Step (FHCast FHOuter) ITCastID (FHCast FHOuter))
  progress {τ = b} (TACast wt wf ConsistHole2) | I IEHole = I (ICastHoleGround (λ _ _ ()) IEHole GBase)
  progress {τ = b} (TACast wt wf ConsistHole2) | I (INEHole x) = I (ICastHoleGround (λ _ _ ()) (INEHole x) GBase)
  progress {τ = b} (TACast wt wf ConsistHole2) | I (IAp x x₁ x₂) = I (ICastHoleGround (λ _ _ ()) (IAp x x₁ x₂) GBase)
  progress {τ = b} (TACast wt wf ConsistHole2) | I (ITAp x x₁) = I (ICastHoleGround (λ _ _ ()) (ITAp x x₁) GBase)
  progress {τ = b} (TACast wt wf ConsistHole2) | I (IFailedCast x x₁ x₂ x₃) = I (ICastHoleGround (λ _ _ ()) (IFailedCast x x₁ x₂ x₃) GBase)
  progress {τ = b} (TACast wt wf ConsistHole2) | I (ICastGroundHole GBase x₁) = S (_ , Step FHOuter (ITCastSucceed GBase) FHOuter)
  progress {τ = b} (TACast wt wf ConsistHole2) | I (ICastGroundHole GArr x₁) = S (_ , Step FHOuter (ITCastFail GArr GBase λ ()) FHOuter)
  progress {τ = b} (TACast wt wf ConsistHole2) | I (ICastGroundHole GForall x₁) = S (_ , Step FHOuter (ITCastFail GForall GBase λ ()) FHOuter)
  progress {τ = ⦇-⦈} (TACast wt wf ConsistHole2) | I x = S (_ , Step FHOuter ITCastID FHOuter)
  progress {τ = τ1 ==> τ2} (TACast wt wf ConsistHole2) | I x with ground-dec (τ1 ==> τ2) 
  progress (TACast wt wf ConsistHole2) | I x | Inr ngnd = S (_ , Step FHOuter (ITExpand (MGArr (ground-arr-not-hole ngnd))) FHOuter)
  progress (TACast wt wf ConsistHole2) | I IEHole | Inl GArr = I (ICastHoleGround (λ _ _ ()) IEHole GArr)
  progress (TACast wt wf ConsistHole2) | I (INEHole x) | Inl GArr = I (ICastHoleGround (λ _ _ ()) (INEHole x) GArr)
  progress (TACast wt wf ConsistHole2) | I (IAp x x₁ x₂) | Inl GArr = I (ICastHoleGround (λ _ _ ()) (IAp x x₁ x₂) GArr)
  progress (TACast wt wf ConsistHole2) | I (ITAp x x₁) | Inl GArr = I (ICastHoleGround (λ _ _ ()) (ITAp x x₁) GArr)
  progress (TACast wt wf ConsistHole2) | I (IFailedCast x x₁ x₂ x₃) | Inl GArr = I (ICastHoleGround (λ _ _ ()) (IFailedCast x x₁ x₂ x₃) GArr)
  progress (TACast (TACast wt x₃ x₄) wf ConsistHole2) | I (ICastHoleGround x x₁ x₂) | Inl GArr = S (_ , Step (FHCast FHOuter) ITCastID (FHCast FHOuter))
  progress (TACast wt wf ConsistHole2) | I (ICastGroundHole {τ = .b} GBase x₁) | Inl GArr = S (_ , Step FHOuter (ITCastFail GBase GArr (λ ())) FHOuter )
  progress (TACast wt wf ConsistHole2) | I (ICastGroundHole {τ = .(⦇-⦈ ==> ⦇-⦈)} GArr x₁) | Inl GArr = S (_ , Step FHOuter (ITCastSucceed GArr) FHOuter )
  progress (TACast wt wf ConsistHole2) | I (ICastGroundHole {τ = .(·∀ ⦇-⦈)} GForall x₁) | Inl GArr = S (_ , Step FHOuter (ITCastFail GForall GArr (λ ())) FHOuter )
  progress {τ = ·∀ τ} (TACast wt wf ConsistHole2) | I x with ground-dec (·∀ τ) 
  progress {τ = ·∀ τ} (TACast wt wf ConsistHole2) | I x | Inr ngnd = S (_ , Step FHOuter (ITExpand (MGForall (ground-forall-not-hole ngnd))) FHOuter)
  progress (TACast wt wf ConsistHole2) | I IEHole | Inl GForall = I (ICastHoleGround (λ _ _ ()) IEHole GForall)
  progress (TACast wt wf ConsistHole2) | I (INEHole x) | Inl GForall = I (ICastHoleGround (λ _ _ ()) (INEHole x) GForall)
  progress (TACast wt wf ConsistHole2) | I (IAp x x₁ x₂) | Inl GForall = I (ICastHoleGround (λ _ _ ()) (IAp x x₁ x₂) GForall)
  progress (TACast wt wf ConsistHole2) | I (ITAp x x₁) | Inl GForall = I (ICastHoleGround (λ _ _ ()) (ITAp x x₁) GForall)
  progress (TACast wt wf ConsistHole2) | I (IFailedCast x x₁ x₂ x₃) | Inl GForall = I (ICastHoleGround (λ _ _ ()) (IFailedCast x x₁ x₂ x₃) GForall)
  progress (TACast (TACast wt x₃ x₄) wf ConsistHole2) | I (ICastHoleGround x x₁ x₂) | Inl GForall = S (_ , Step (FHCast FHOuter) ITCastID (FHCast FHOuter))
  progress (TACast wt wf ConsistHole2) | I (ICastGroundHole GBase x₁) | Inl GForall = S (_ , Step FHOuter (ITCastFail GBase GForall (λ ())) FHOuter )
  progress (TACast wt wf ConsistHole2) | I (ICastGroundHole GArr x₁) | Inl GForall = S (_ , Step FHOuter (ITCastFail GArr GForall (λ ())) FHOuter )
  progress (TACast wt wf ConsistHole2) | I (ICastGroundHole GForall x₁) | Inl GForall = S (_ , Step FHOuter (ITCastSucceed GForall) FHOuter )

  progress (TACast wt wf (ConsistHole1 {τ = τ})) | BV x with ground-dec τ 
  progress (TACast wt wf (ConsistHole1 {τ = τ})) | BV x | Inl gnd = BV (BVHoleCast gnd x)
  progress {_ ⟨ b ⇒ .⦇-⦈ ⟩} (TACast wt wf (ConsistHole1 {b})) | BV x | Inr ngnd = abort (ngnd GBase)
  progress {_ ⟨ T x₁ ⇒ .⦇-⦈ ⟩} (TACast wt wf (ConsistHole1 {T x₁})) | BV x | Inr ngnd with wf-ta CtxWFEmpty wt 
  ... | ()
  progress {_ ⟨ ⦇-⦈ ⇒ .⦇-⦈ ⟩} (TACast wt wf (ConsistHole1 {⦇-⦈})) | BV x | Inr ngnd = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt wf (ConsistHole1 {τ1 ==> τ2})) | BV x | Inr ngnd = S (_ , Step FHOuter (ITGround (MGArr (ground-arr-not-hole ngnd))) FHOuter)
  progress {_ ⟨ ·∀ τ ⇒ .⦇-⦈ ⟩} (TACast wt wf (ConsistHole1 {·∀ τ})) | BV x | Inr ngnd = S (_ , Step FHOuter (ITGround (MGForall (ground-forall-not-hole ngnd))) FHOuter)
  progress (TACast () wf ConsistHole2) | BV (BVVal VConst)
  progress (TACast () wf ConsistHole2) | BV (BVVal VLam) 
  progress (TACast () wf ConsistHole2) | BV (BVVal VTLam)
  progress {τ = τ1} (TACast wt wf ConsistHole2) | BV (BVHoleCast {τ = τ2} gnd bv) with htyp-eq-dec τ2 τ1
  progress {τ = τ1} (TACast wt wf ConsistHole2) | BV (BVHoleCast {τ = τ2} gnd bv) | Inl refl = S (_ , Step FHOuter (ITCastSucceed gnd) FHOuter) 
  progress {τ = τ1} (TACast wt wf ConsistHole2) | BV (BVHoleCast {τ = τ2} gnd bv) | Inr neq with ground-dec τ1 
  progress {τ = τ1} (TACast wt wf ConsistHole2) | BV (BVHoleCast {τ = τ2} gnd bv) | Inr neq | Inl gnd' = S (_ , Step FHOuter (ITCastFail gnd gnd' (ground-neq~ gnd gnd' neq)) FHOuter)
  progress {τ = b} (TACast wt wf ConsistHole2) | BV (BVHoleCast gnd bv) | Inr neq | Inr ngnd = abort (ngnd GBase)
  progress {τ = ⦇-⦈} (TACast wt wf ConsistHole2) | BV (BVHoleCast gnd bv) | Inr neq | Inr ngnd = S (_ , Step FHOuter ITCastID FHOuter)
  progress {τ = τ1 ==> τ2} (TACast wt wf ConsistHole2) | BV (BVHoleCast gnd bv) | Inr neq | Inr ngnd = S (_ , Step FHOuter (ITExpand (MGArr (ground-arr-not-hole ngnd))) FHOuter)
  progress {τ = ·∀ τ1} (TACast wt wf ConsistHole2) | BV (BVHoleCast gnd bv) | Inr neq | Inr ngnd = S (_ , Step FHOuter (ITExpand (MGForall (ground-forall-not-hole ngnd))) FHOuter)