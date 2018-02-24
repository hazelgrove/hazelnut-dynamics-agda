open import Nat
open import Prelude
open import List
open import core
open import contexts

open import progress
open import htype-decidable

module complete-progress where

  data okc : (d : dhexp) (Δ : hctx) → Set where
    V : ∀{d Δ} → d val → okc d Δ
    S : ∀{d Δ} → Σ[ d' ∈ dhexp ] (d ↦ d') → okc d Δ

  lem-ind-comp : ∀{d} → d dcomplete → d indet → ⊥
  lem-ind-comp DCVar ()
  lem-ind-comp DCConst ()
  lem-ind-comp (DCLam comp x₁) ()
  lem-ind-comp (DCAp comp comp₁) (IAp x ind x₁) = lem-ind-comp comp ind
  lem-ind-comp (DCCast comp x x₁) (ICastArr x₂ ind) = lem-ind-comp comp ind
  lem-ind-comp (DCCast comp x x₁) (ICastGroundHole x₂ ind) = lem-ind-comp comp ind
  lem-ind-comp (DCCast comp x x₁) (ICastHoleGround x₂ ind x₃) = lem-ind-comp comp ind
  lem-ind-comp (DCFailedCast comp x x₁) (IFailedCast x₂ GBase GBase x₅) = x₅ refl
  lem-ind-comp (DCFailedCast comp x (TCArr () x₂)) (IFailedCast x₃ GBase GHole x₅)
  lem-ind-comp (DCFailedCast comp (TCArr x ()) x₂) (IFailedCast x₃ GHole GBase x₅)
  lem-ind-comp (DCFailedCast comp x x₁) (IFailedCast x₂ GHole GHole x₅) = x₅ refl

  complete-progress : {Δ : hctx} {d : dhexp} {τ : htyp} →
                       Δ , ∅ ⊢ d :: τ →
                       d dcomplete →
                       okc d Δ
  complete-progress wt comp with progress wt
  complete-progress wt comp | S x = S x
  complete-progress wt comp | BV (BVVal x) = V x

  complete-progress wt comp | I x = abort (lem-ind-comp comp x)
  complete-progress (TACast wt x) (DCCast comp x₃ ()) | BV (BVHoleCast x₁ x₂)
  complete-progress (TACast wt con) (DCCast comp (TCArr x₃ x₄) (TCArr x₅ x₆)) | BV (BVArrCast x₁ x₂) = {!!}
  --   with complete-progress wt comp
  -- complete-progress (TACast wt con) (DCCast comp (TCArr x₃ x₄) (TCArr x₅ x₆)) | BV (BVArrCast x₁ x₂) | V x = {!!}
  -- complete-progress (TACast wt con) (DCCast comp (TCArr x₃ x₄) (TCArr x₅ x₆)) | BV (BVArrCast x₁ x₂) | S x = {!!}
