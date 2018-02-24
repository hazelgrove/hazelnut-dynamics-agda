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

  complete-progress : {Δ : hctx} {d : dhexp} {τ : htyp} →
                       Δ , ∅ ⊢ d :: τ →
                       d dcomplete →
                       okc d Δ
  complete-progress wt comp with progress wt
  complete-progress wt comp | S x = S x
  complete-progress wt comp | BV (BVVal x) = V x

  complete-progress wt comp | I x = abort (lem-ind-comp comp x)
  complete-progress (TACast wt x) (DCCast comp x₃ ()) | BV (BVHoleCast x₁ x₂)
  complete-progress (TACast (TAVar x₁) con) (DCCast comp (TCArr x₄ x₅) (TCArr x₆ x₇)) | BV (BVArrCast x₂ x₃) = {!!}
  complete-progress (TACast (TALam wt) con) (DCCast comp (TCArr x₃ x₄) (TCArr x₅ x₆)) | BV (BVArrCast x₁ x₂) = {!!}
  complete-progress (TACast (TAAp wt wt₁) con) (DCCast comp (TCArr x₃ x₄) (TCArr x₅ x₆)) | BV (BVArrCast x₁ x₂) = {!!}
  complete-progress (TACast (TAEHole x x₁) con) (DCCast comp (TCArr x₄ x₅) (TCArr x₆ x₇)) | BV (BVArrCast x₂ x₃) = {!!}
  complete-progress (TACast (TANEHole x wt x₁) con) (DCCast comp (TCArr x₄ x₅) (TCArr x₆ x₇)) | BV (BVArrCast x₂ x₃) = {!!}
  complete-progress (TACast (TACast wt x) con) (DCCast comp (TCArr x₃ x₄) (TCArr x₅ x₆)) | BV (BVArrCast x₁ x₂) = {!!}
  complete-progress (TACast (TAFailedCast wt x x₁ x₂) con) (DCCast comp (TCArr x₅ x₆) (TCArr x₇ x₈)) | BV (BVArrCast x₃ x₄) = {!!}
  --   with complete-progress wt comp
  -- complete-progress (TACast wt con) (DCCast comp (TCArr x₃ x₄) (TCArr x₅ x₆)) | BV (BVArrCast x₁ x₂) | V x = {!!}
  -- complete-progress (TACast wt con) (DCCast comp (TCArr x₃ x₄) (TCArr x₅ x₆)) | BV (BVArrCast x₁ x₂) | S x = {!!}
