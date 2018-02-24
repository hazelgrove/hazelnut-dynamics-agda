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

  -- no term is both complete and indeterminate
  lem-ind-comp : ∀{d} → d dcomplete → d indet → ⊥
  lem-ind-comp DCVar ()
  lem-ind-comp DCConst ()
  lem-ind-comp (DCLam comp x₁) ()
  lem-ind-comp (DCAp comp comp₁) (IAp x ind x₁) = lem-ind-comp comp ind
  lem-ind-comp (DCCast comp x x₁) (ICastArr x₂ ind) = lem-ind-comp comp ind
  lem-ind-comp (DCCast comp x x₁) (ICastGroundHole x₂ ind) = lem-ind-comp comp ind
  lem-ind-comp (DCCast comp x x₁) (ICastHoleGround x₂ ind x₃) = lem-ind-comp comp ind

  -- if an arrow is disequal, it disagrees in the first or second argument
  ne-factor : ∀{τ1 τ2 τ3 τ4} → (τ1 ==> τ2) ≠ (τ3 ==> τ4) → (τ1 ≠ τ3) + (τ2 ≠ τ4)
  ne-factor {τ1} {τ2} {τ3} {τ4} ne with htype-dec τ1 τ3 | htype-dec τ2 τ4
  ne-factor ne | Inl refl | Inl refl = Inl (λ x → ne refl)
  ne-factor ne | Inl x | Inr x₁ = Inr x₁
  ne-factor ne | Inr x | Inl x₁ = Inl x
  ne-factor ne | Inr x | Inr x₁ = Inl x

  -- disequal complete types are not consistent
  eq-com-con : ∀{τ1 τ2} → τ1 tcomplete → τ2 tcomplete → τ1 ≠ τ2 → τ1 ~ τ2 → ⊥
  eq-com-con tc1 tc2 ne TCRefl = ne refl
  eq-com-con tc1 () ne TCHole1
  eq-com-con () tc2 ne TCHole2
  eq-com-con (TCArr tc1 tc2) (TCArr tc3 tc4) ne (TCArr con con₁) with ne-factor ne
  eq-com-con (TCArr tc1 tc2) (TCArr tc3 tc4) ne (TCArr con con₁) | Inl x = eq-com-con tc1 tc3 x con
  eq-com-con (TCArr tc1 tc2) (TCArr tc3 tc4) ne (TCArr con con₁) | Inr x = eq-com-con tc2 tc4 x con₁

  complete-progress : {Δ : hctx} {d : dhexp} {τ : htyp} →
                       Δ , ∅ ⊢ d :: τ →
                       d dcomplete →
                       okc d Δ
  complete-progress wt comp with progress wt
  complete-progress wt comp | I x = abort (lem-ind-comp comp x)
  complete-progress wt comp | S x = S x
  complete-progress wt comp | BV (BVVal x) = V x
  complete-progress wt (DCCast comp x₂ ()) | BV (BVHoleCast x x₁)
  complete-progress (TACast wt x) (DCCast comp x₃ x₄) | BV (BVArrCast x₁ x₂) = abort (eq-com-con x₃ x₄ x₁ x)
