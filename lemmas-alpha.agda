{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude
open import core
open import contexts
open import Nat

module lemmas-alpha where

  open alpha

  reflex-extend : {x' y : Nat} {Γ : Nat ctx} → (x : Nat) → (∀ {x y} → (x , y) ∈ Γ → (x , x) ∈ Γ) → (x' , y) ∈ (■ (x , x) ∪ Γ) → (x' , x') ∈ (■ (x , x) ∪ Γ)
  reflex-extend {x' = x'} {y = y} x reflex elem with natEQ x x' 
  reflex-extend {x' = x'} {y = y} x reflex elem | Inl refl = refl
  reflex-extend {x' = x'} {y = y} x reflex elem | Inr neq = reflex elem
  
  alpha-refl-ctx : (Γ : Nat ctx) → (∀ {x y} → (x , y) ∈ Γ → (x , x) ∈ Γ) → (τ : htyp) → Γ , Γ ⊢ τ =α τ
  alpha-refl-ctx _ _ b = AlphaBase
  alpha-refl-ctx Γ reflex (T x) with (Γ x) in eq
  alpha-refl-ctx Γ reflex (T x) | Some y = AlphaVarBound (reflex eq) (reflex eq)
  alpha-refl-ctx Γ reflex (T x) | None = AlphaVarFree eq eq 
  alpha-refl-ctx _ _ ⦇-⦈ = AlphaHole
  alpha-refl-ctx Γ reflex (τ ==> τ₁) = AlphaArr (alpha-refl-ctx Γ reflex τ) (alpha-refl-ctx Γ reflex τ₁)
  alpha-refl-ctx Γ reflex (·∀ x τ) = AlphaForall (alpha-refl-ctx (■ (x , x) ∪ Γ) (reflex-extend x reflex) τ )

  alpha-refl : (τ : htyp) → τ =α τ
  alpha-refl τ = alpha-refl-ctx ∅ (λ ()) τ


  alpha-sym-ctx : (ΓL ΓR : Nat ctx) → (τ1 τ2 : htyp) → ΓL , ΓR ⊢ τ1 =α τ2 → ΓR , ΓL ⊢ τ2 =α τ1
  alpha-sym-ctx ΓL ΓR b b eq = AlphaBase
  alpha-sym-ctx ΓL ΓR (T x) (T y) (AlphaVarBound l r) = AlphaVarBound r l
  alpha-sym-ctx ΓL ΓR (T x) (T y) (AlphaVarFree l r) = AlphaVarFree r l 
  alpha-sym-ctx ΓL ΓR ⦇-⦈ ⦇-⦈ eq = AlphaHole
  alpha-sym-ctx ΓL ΓR (τ1 ==> τ3) (τ2 ==> τ4) (AlphaArr l r) = 
    AlphaArr 
      (alpha-sym-ctx ΓL ΓR τ1 τ2 l)
      (alpha-sym-ctx ΓL ΓR τ3 τ4 r)
  alpha-sym-ctx ΓL ΓR (·∀ x τ1) (·∀ y τ2) (AlphaForall eq) = 
    AlphaForall (alpha-sym-ctx ((■ (x , y)) ∪ ΓL) ((■ (y , x)) ∪ ΓR) τ1 τ2 eq)

  alpha-sym : {τ1 τ2 : htyp} → τ1 =α τ2 → τ2 =α τ1
  alpha-sym {τ1} {τ2} = alpha-sym-ctx ∅ ∅ τ1 τ2

  alpha-hole : (τ : htyp) → (τ =α ⦇-⦈) → τ == ⦇-⦈
  alpha-hole .⦇-⦈ AlphaHole = refl

  _<=<_ : Nat ctx → Nat ctx → Nat ctx
  (ΓL <=< ΓR) x with ΓR x
  ... | Some y = ΓL y
  ... | None = None

  comp-elem : ∀{x y z} → (Γ1 Γ2 : Nat ctx) → (x , y) ∈ Γ2 → (y , z) ∈ Γ1 → (x , z) ∈ (Γ1 <=< Γ2)
  comp-elem {x} {y} {z} Γ1 Γ2 i1 i2 with ctxindirect Γ2 x
  ... | Inl (y' , ing) rewrite ing rewrite someinj i1 = i2
  ... | Inr ning = {!   !}

  data dom-cod : Nat ctx → Nat ctx → Set where 
    DC : ∀{Γ1 Γ2} → ((y : Nat) → dom Γ2 y → (Σ[ x ∈ Nat ] ((x , y) ∈ Γ1))) → dom-cod Γ1 Γ2


  prunel : Nat ctx → Nat ctx → Nat ctx
  prunel Γ1 Γ2 x with Γ1 x
  ... | None = None
  ... | Some y with Γ2 y
  ...   | Some x = Some y
  ...   | _ = None
  
  pruner : Nat ctx → Nat ctx → Nat ctx
  pruner Γ1 Γ2 x with Γ2 x
  ... | None = None
  ... | Some y with Γ1 y
  ...   | Some x = Some y
  ...   | _ = None

  prunel-def : ∀{x y ΓL ΓR} → (x , y) ∈ ΓL → (y , x) ∈ ΓR → (x , y) ∈ prunel ΓL ΓR
  prunel-def = {!   !}

  prune-pres-alpha1 : ∀{ΓL ΓR τ1 τ2} → ΓL , ΓR ⊢ τ1 =α τ2 → prunel ΓL ΓR , pruner ΓL ΓR ⊢ τ1 =α τ2
  prune-pres-alpha1 AlphaBase = AlphaBase
  prune-pres-alpha1 {ΓL} {ΓR} (AlphaVarBound {x = x} {y = y} meml memr) with ctxindirect ΓL x | ctxindirect ΓR y
  ... | Inl (y , inl) | Inl (x , inr) = AlphaVarBound (prunel-def meml inr) {!  !}
  ... | _ | _ = {!   !}
  prune-pres-alpha1 (AlphaVarFree x x₁) = {!   !}
  prune-pres-alpha1 AlphaHole = AlphaHole
  prune-pres-alpha1 (AlphaArr alpha alpha₁) = AlphaArr (prune-pres-alpha1 alpha) (prune-pres-alpha1 alpha₁)
  prune-pres-alpha1 (AlphaForall alpha) = {!   !}


  prune-pres-alpha2 : ∀{ΓL ΓR τ1 τ2} → prunel ΓL ΓR , pruner ΓL ΓR ⊢ τ1 =α τ2 → ΓL , ΓR ⊢ τ1 =α τ2
  prune-pres-alpha2 = {!   !}

  comp-lextend : (x y z : Nat) → (Γ1 Γ2 : Nat ctx) → ((■ (x , z)) ∪ (Γ2 <=< Γ1)) == ((■ (y , z)) ∪ Γ2) <=< ((■ (x , y)) ∪ Γ1)
  comp-lextend x y z Γ1 Γ2 = funext (λ w → foo w)
    where
      foo : (w : Nat) → ((■ (x , z)) ∪ (Γ2 <=< Γ1)) w == (((■ (y , z)) ∪ Γ2) <=< ((■ (x , y)) ∪ Γ1)) w
      foo w with natEQ x w
      ... | Inl refl rewrite natEQrefl {x} rewrite natEQrefl {y} = refl
      ... | Inr neq rewrite natEQneq neq with ctxindirect Γ1 w 
      ...   | Inr ning1 rewrite ning1 = refl
      ...   | Inl (w' , ing1) rewrite ing1 with natEQ y w' 
      ...     | Inl refl = {!   !}
      ...     | Inr neq' = refl

  comp-lextend-prunel : (x y z : Nat) → (ΓL1 ΓL2 ΓR1 ΓR2 : Nat ctx) → 
    prunel ((■ (x , z)) ∪ (ΓL2 <=< ΓL1)) 
           ((■ (z , x)) ∪ (ΓR1 <=< ΓR2)) == 
    (prunel ((■ (y , z)) ∪ ΓL2) ((■ (z , y)) ∪ ΓR2) <=< 
     prunel ((■ (x , y)) ∪ ΓL1) ((■ (y , x)) ∪ ΓR1))
  comp-lextend-prunel x y z ΓL1 ΓL2 ΓR1 ΓR2 = {!   !}

  comp-lextend-pruner : (x y z : Nat) → (ΓL1 ΓL2 ΓR1 ΓR2 : Nat ctx) → pruner ((■ (x , z)) ∪ (ΓL2 <=< ΓL1)) ((■ (z , x)) ∪ (ΓR1 <=< ΓR2)) == pruner (((■ (y , z)) ∪ ΓL2) <=< ((■ (x , y)) ∪ ΓL1)) (((■ (y , x)) ∪ ΓR1) <=< ((■ (z , y)) ∪ ΓR2))
  comp-lextend-pruner = {!   !}

  alpha-rewrite-gamma : ∀{ΓL ΓL' ΓR ΓR' τ1 τ2} → ΓL == ΓL' → ΓR == ΓR' → ΓL , ΓR ⊢ τ1 =α τ2 → ΓL' , ΓR' ⊢ τ1 =α τ2
  alpha-rewrite-gamma eq1 eq2 alpha rewrite ! eq1 rewrite ! eq2 = alpha

  ⊢alpha-trans : {ΓL1 ΓR1 ΓL2 ΓR2 : Nat ctx} {τ1 τ2 τ3 : htyp} → ΓL1 , ΓR1 ⊢ τ1 =α τ2 → ΓL2 , ΓR2 ⊢ τ2 =α τ3 → (ΓL2 <=< ΓL1) , (ΓR1 <=< ΓR2) ⊢ τ1 =α τ3
  ⊢alpha-trans AlphaBase AlphaBase = AlphaBase
  ⊢alpha-trans {ΓL1} {ΓR1} {ΓL2} {ΓR2} (AlphaVarBound x₁ x₂) (AlphaVarBound x₃ x₄) = AlphaVarBound (comp-elem ΓL2 ΓL1 x₁ x₃) (comp-elem ΓR1 ΓR2 x₄ x₂)
  ⊢alpha-trans (AlphaVarBound x₁ x₂) (AlphaVarFree x₃ x₄) = {!   !}
  ⊢alpha-trans {ΓL2 = ΓL2} {ΓR2 = ΓR2} (AlphaVarFree x x₁) (AlphaVarBound x₂ x₃) = {!   !}
  ⊢alpha-trans {ΓL1} {ΓR1} {ΓL2} {ΓR2} (AlphaVarFree x x₁) (AlphaVarFree x₂ x₃) = AlphaVarFree {!   !} {!   !}
  ⊢alpha-trans {ΓL2 = ΓL2} {ΓR2 = ΓR2} AlphaHole AlphaHole = AlphaHole
  ⊢alpha-trans (AlphaArr a1 a3) (AlphaArr a2 a4) = {!   !} -- AlphaArr (alpha-trans a1 a2) (alpha-trans a3 a4)
  ⊢alpha-trans {ΓL1} {ΓR1} {ΓL2} {ΓR2} (AlphaForall {x = x} {y = y} a1) (AlphaForall {x = y} {y = y'} a2) = 
    AlphaForall (prune-pres-alpha2 (alpha-rewrite-gamma (! (comp-lextend-prunel x y y' ΓL1 ΓL2 ΓR1 ΓR2)) {!   !} (⊢alpha-trans (prune-pres-alpha1 a1) (prune-pres-alpha1 a2))))
    
  alpha-trans : ∀{τ1 τ2 τ3} → τ1 =α τ2 → τ2 =α τ3 → τ1 =α τ3
  alpha-trans = ⊢alpha-trans

     -- AlphaForall (prune-pres-alpha2 (alpha-rewrite-gamma (! (comp-lextend-prunel x y y' ΓL1 ΓL2 ΓR1 ΓR2)) (! (comp-lextend-pruner x y y' ΓL1 ΓL2 ΓR1 ΓR2)) (prune-pres-alpha1 (alpha-trans a1 a2)))) -- (alpha-rewrite-gamma (! (comp-lextend x y y' ΓL1 ΓL2)) (! (comp-lextend y' y x ΓR2 ΓR1)) (alpha-trans a1 a2)) -- AlphaForall {!   !}
