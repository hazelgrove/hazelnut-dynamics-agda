open import Nat
open import Prelude
open import core
open import core-type
open import core-exp

open import parametricity2-defs
open import parametricity2-lemmas1
open import parametricity2-lemmas2

open import preservation
open import progress-checks

module parametricity2 where

  parametricity21 :
    ∀{d1 d2 v1 τ1 τ2} →
    ∅ ⊢ d1 :: τ1 →
    ∅ ⊢ d2 :: τ2 →
    d1 =0c d2 →
    d1 ↦* v1 →
    v1 boxedval →
    Σ[ v2 ∈ ihexp ]( d2 ↦* v2 × ((v2 boxedval × v1 =0c v2) + v2 indet ))
  parametricity21 wt1 wt2 eq0 MSRefl bv with parametricity-onesided-lemma wt1 wt2 eq0 bv
  ... | d2' , eq0' , steps , FBoxedVal x = d2' , steps , Inl (x , eq0')
  ... | d2' , eq0' , steps , FIndet x = d2' , steps , Inr x
  parametricity21 wt1 wt2 eq0 (MSStep x step) bv with parametricity21-lemma-ctx wt1 wt2 eq0 x
  ... | d2' , steps , Inr x₁ = d2' , steps , Inr x₁
  ... | d2' , steps , Inl x₁ with parametricity21 (preservation wt1 x) (preservation-trans wt2 steps) x₁ step bv
  ...   | v2 , steps' , next = v2 , mstrans steps steps' , next

  parametricity22 : 
    ∀{d1 d2 v1 v2 τ1 τ2} →
    confluence →
    ∅ ⊢ d1 :: τ1 →
    ∅ ⊢ d2 :: τ2 →
    d1 =0c d2 →
    d1 ↦* v1 →
    d2 ↦* v2 →
    v1 boxedval →
    v2 boxedval →
    v1 =0c v2
  parametricity22 conf wt1 wt2 eq0 steps1 steps2 bv1 bv2
    with parametricity21 wt1 wt2 eq0 steps1 bv1
  ... | d2' , steps2' , Inl (bv2' , eq0') with confluence-implies-unique-normal-form conf steps2 steps2' (FBoxedVal bv2) (FBoxedVal bv2')
  ...   | refl = eq0'
  parametricity22 conf wt1 wt2 eq0 steps1 steps2 bv1 bv2 | d2' , steps2' , Inr ind with confluence-implies-unique-normal-form conf steps2 steps2' (FBoxedVal bv2) (FIndet ind)
  ...   | refl = abort (boxedval-not-indet bv2 ind)
