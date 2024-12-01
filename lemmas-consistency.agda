open import Nat
open import Prelude
open import core-type
open import core
open import lemmas-index

module lemmas-consistency where

  ~refl : {τ : htyp} → τ ~ τ
  ~refl {τ = b} = ConsistBase
  ~refl {τ = T x} = ConsistVar
  ~refl {τ = ⦇-⦈} = ConsistHole1
  ~refl {τ = τ ==> τ₁} = ConsistArr ~refl ~refl
  ~refl {τ = ·∀ τ} = ConsistForall ~refl
  
  ~sym : {τ1 τ2 : htyp} → τ1 ~ τ2 → τ2 ~ τ1
  ~sym ConsistBase = ConsistBase
  ~sym ConsistVar = ConsistVar 
  ~sym ConsistHole1 = ConsistHole2
  ~sym ConsistHole2 = ConsistHole1
  ~sym (ConsistArr con1 con2) = ConsistArr (~sym con1) (~sym con2)
  ~sym (ConsistForall consist) = ConsistForall (~sym consist)

  ~dec : (τ1 τ2 : htyp) → (τ1 ~ τ2) + (τ1 ~̸ τ2)
  ~dec _ ⦇-⦈ = Inl ConsistHole1
  ~dec ⦇-⦈ _ = Inl ConsistHole2
  ~dec b b = Inl ConsistBase
  ~dec (T x) (T x₁) with natEQ x x₁
  ... | Inl refl = Inl ConsistVar
  ... | Inr neq = Inr (λ{ConsistVar -> neq refl})
  ~dec (τ1 ==> τ2) (τ3 ==> τ4) with ~dec τ1 τ3 | ~dec τ2 τ4 
  ... | Inl x | Inl y = Inl (ConsistArr x y)
  ... | Inl _ | Inr y = Inr (\{(ConsistArr l r) -> y r})
  ... | Inr x | _     = Inr (\{(ConsistArr l r) -> x l})
  ~dec (·∀ τ1) (·∀ τ2) with ~dec τ1 τ2
  ... | Inl yes = Inl (ConsistForall yes)
  ... | Inr no = Inr (λ {(ConsistForall x) → no x})
  ~dec b (T x) = Inr (λ ())
  ~dec b (τ2 ==> τ3) = Inr (λ ())
  ~dec b (·∀ τ2) = Inr (λ ())
  ~dec (T x) b = Inr (λ ())
  ~dec (T x) (τ2 ==> τ3) = Inr (λ ())
  ~dec (T x) (·∀ τ2) = Inr (λ ())
  ~dec (τ1 ==> τ2) b = Inr (λ ())
  ~dec (τ1 ==> τ2) (T x) = Inr (λ ())
  ~dec (τ1 ==> τ2) (·∀ τ3) = Inr (λ ())
  ~dec (·∀ τ1) b = Inr (λ ())
  ~dec (·∀ τ1) (T x) = Inr (λ ())
  ~dec (·∀ τ1) (τ2 ==> τ3) = Inr (λ ())

  ~̸-≠ : ∀{τ1 τ2} → τ1 ~̸ τ2 → τ1 ≠ τ2
  ~̸-≠ inconsis eq rewrite ! eq = abort (inconsis ~refl)
 