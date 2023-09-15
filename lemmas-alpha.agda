{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude
open import core
open import contexts
open import Nat
open import rewrite-util

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

  alpha-refl-ta : ∀{ Δ Θ Γ d τ } → Δ , Θ , Γ ⊢ d :: τ → Σ[ τ' ∈ htyp ] (τ' =α τ × Δ , Θ , Γ ⊢ d :: τ')
  alpha-refl-ta {τ = τ} ta = τ , alpha-refl τ , ta

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

  -- _<=<_ : Nat ctx → Nat ctx → Nat ctx
  -- (ΓL <=< ΓR) x with ΓR x
  -- ... | Some y = ΓL y
  -- ... | None = None

  -- comp-elem : ∀{x y z} → (Γ1 Γ2 : Nat ctx) → (x , y) ∈ Γ2 → (y , z) ∈ Γ1 → (x , z) ∈ (Γ1 <=< Γ2)
  -- comp-elem {x} {y} {z} Γ1 Γ2 i1 i2 with ctxindirect Γ2 x
  -- ... | Inl (y' , ing) rewrite ing rewrite someinj i1 = i2
  -- ... | Inr ning = {!   !}

  -- data dom-cod : Nat ctx → Nat ctx → Set where 
  --   DC : ∀{Γ1 Γ2} → ((y : Nat) → dom Γ2 y → (Σ[ x ∈ Nat ] ((x , y) ∈ Γ1))) → dom-cod Γ1 Γ2


  -- prunel : Nat ctx → Nat ctx → Nat ctx
  -- prunel Γ1 Γ2 x with Γ1 x
  -- ... | None = None
  -- ... | Some y with Γ2 y
  -- ...   | Some x = Some y
  -- ...   | _ = None
  
  -- pruner : Nat ctx → Nat ctx → Nat ctx
  -- pruner Γ1 Γ2 x with Γ2 x
  -- ... | None = None
  -- ... | Some y with Γ1 y
  -- ...   | Some x = Some y
  -- ...   | _ = None

  -- prunel-def : ∀{x y ΓL ΓR} → (x , y) ∈ ΓL → (y , x) ∈ ΓR → (x , y) ∈ prunel ΓL ΓR
  -- prunel-def = {!   !}

  -- prune-pres-alpha1 : ∀{ΓL ΓR τ1 τ2} → ΓL , ΓR ⊢ τ1 =α τ2 → prunel ΓL ΓR , pruner ΓL ΓR ⊢ τ1 =α τ2
  -- prune-pres-alpha1 AlphaBase = AlphaBase
  -- prune-pres-alpha1 {ΓL} {ΓR} (AlphaVarBound {x = x} {y = y} meml memr) with ctxindirect ΓL x | ctxindirect ΓR y
  -- ... | Inl (y , inl) | Inl (x , inr) = AlphaVarBound (prunel-def meml inr) {!  !}
  -- ... | _ | _ = {!   !}
  -- prune-pres-alpha1 (AlphaVarFree x x₁) = {!   !}
  -- prune-pres-alpha1 AlphaHole = AlphaHole
  -- prune-pres-alpha1 (AlphaArr alpha alpha₁) = AlphaArr (prune-pres-alpha1 alpha) (prune-pres-alpha1 alpha₁)
  -- prune-pres-alpha1 (AlphaForall alpha) = {!   !}


  -- prune-pres-alpha2 : ∀{ΓL ΓR τ1 τ2} → prunel ΓL ΓR , pruner ΓL ΓR ⊢ τ1 =α τ2 → ΓL , ΓR ⊢ τ1 =α τ2
  -- prune-pres-alpha2 = {!   !}

  -- comp-lextend : (x y z : Nat) → (Γ1 Γ2 : Nat ctx) → ((■ (x , z)) ∪ (Γ2 <=< Γ1)) == ((■ (y , z)) ∪ Γ2) <=< ((■ (x , y)) ∪ Γ1)
  -- comp-lextend x y z Γ1 Γ2 = funext (λ w → foo w)
  --   where
  --     foo : (w : Nat) → ((■ (x , z)) ∪ (Γ2 <=< Γ1)) w == (((■ (y , z)) ∪ Γ2) <=< ((■ (x , y)) ∪ Γ1)) w
  --     foo w with natEQ x w
  --     ... | Inl refl rewrite natEQrefl {x} rewrite natEQrefl {y} = refl
  --     ... | Inr neq rewrite natEQneq neq with ctxindirect Γ1 w 
  --     ...   | Inr ning1 rewrite ning1 = refl
  --     ...   | Inl (w' , ing1) rewrite ing1 with natEQ y w' 
  --     ...     | Inl refl = {!   !}
  --     ...     | Inr neq' = refl

  -- comp-lextend-prunel : (x y z : Nat) → (ΓL1 ΓL2 ΓR1 ΓR2 : Nat ctx) → 
  --   prunel ((■ (x , z)) ∪ (ΓL2 <=< ΓL1)) 
  --          ((■ (z , x)) ∪ (ΓR1 <=< ΓR2)) == 
  --   (prunel ((■ (y , z)) ∪ ΓL2) ((■ (z , y)) ∪ ΓR2) <=< 
  --    prunel ((■ (x , y)) ∪ ΓL1) ((■ (y , x)) ∪ ΓR1))
  -- comp-lextend-prunel x y z ΓL1 ΓL2 ΓR1 ΓR2 = {!   !}

  -- comp-lextend-pruner : (x y z : Nat) → (ΓL1 ΓL2 ΓR1 ΓR2 : Nat ctx) → pruner ((■ (x , z)) ∪ (ΓL2 <=< ΓL1)) ((■ (z , x)) ∪ (ΓR1 <=< ΓR2)) == pruner (((■ (y , z)) ∪ ΓL2) <=< ((■ (x , y)) ∪ ΓL1)) (((■ (y , x)) ∪ ΓR1) <=< ((■ (z , y)) ∪ ΓR2))
  -- comp-lextend-pruner = {!   !}

  -- ⊢alpha-trans : {ΓL1 ΓR1 ΓL2 ΓR2 : Nat ctx} {τ1 τ2 τ3 : htyp} → ΓL1 , ΓR1 ⊢ τ1 =α τ2 → ΓL2 , ΓR2 ⊢ τ2 =α τ3 → (ΓL2 <=< ΓL1) , (ΓR1 <=< ΓR2) ⊢ τ1 =α τ3
  -- ⊢alpha-trans AlphaBase AlphaBase = AlphaBase
  -- ⊢alpha-trans {ΓL1} {ΓR1} {ΓL2} {ΓR2} (AlphaVarBound x₁ x₂) (AlphaVarBound x₃ x₄) = AlphaVarBound (comp-elem ΓL2 ΓL1 x₁ x₃) (comp-elem ΓR1 ΓR2 x₄ x₂)
  -- ⊢alpha-trans {ΓL1} {ΓR1} {ΓL2} {ΓR2} {τ1 = T x} {τ2 = T y} (AlphaVarBound x₁ x₂) (AlphaVarFree x₃ x₄) = {!   !}
  -- ⊢alpha-trans {ΓL2 = ΓL2} {ΓR2 = ΓR2} (AlphaVarFree x x₁) (AlphaVarBound x₂ x₃) = {!   !}
  -- ⊢alpha-trans {ΓL1} {ΓR1} {ΓL2} {ΓR2} (AlphaVarFree x x₁) (AlphaVarFree x₂ x₃) = AlphaVarFree {!   !} {!   !}
  -- ⊢alpha-trans {ΓL2 = ΓL2} {ΓR2 = ΓR2} AlphaHole AlphaHole = AlphaHole
  -- ⊢alpha-trans (AlphaArr a1 a3) (AlphaArr a2 a4) = AlphaArr (⊢alpha-trans a1 a2) (⊢alpha-trans a3 a4)
  -- ⊢alpha-trans {ΓL1} {ΓR1} {ΓL2} {ΓR2} (AlphaForall {x = x} {y = y} a1) (AlphaForall {x = y} {y = y'} a2) with (⊢alpha-trans a1 a2)
  -- ... | result rewrite (<=<-comm x y y' {!   !} {!   !}) = AlphaForall {! result  !}
  --   -- AlphaForall (prune-pres-alpha2 (alpha-rewrite-gamma (! (comp-lextend-prunel x y y' ΓL1 ΓL2 ΓR1 ΓR2)) {!   !} (⊢alpha-trans (prune-pres-alpha1 a1) (prune-pres-alpha1 a2))))
    
  -- alpha-trans : ∀{τ1 τ2 τ3} → τ1 =α τ2 → τ2 =α τ3 → τ1 =α τ3
  -- alpha-trans = ⊢alpha-trans

  -- needs a stronger inductive hypothesis.
  alpha-closed : ∀{τ τ'} → ∅ ⊢ τ wf → τ =α τ' → ∅ ⊢ τ' wf
  alpha-closed wf AlphaBase = {!   !}
  alpha-closed wf (AlphaVarFree x x₁) = {!   !}
  alpha-closed wf AlphaHole = {!   !}
  alpha-closed wf (AlphaArr alpha alpha₁) = {!   !}
  alpha-closed (WFForall wf) (AlphaForall alpha) = WFForall {!   !}
  -- Alternatively can prove the below and use:
  -- alpha-closed = alpha-wf

  alpha-wf : ∀{Θ τ τ'} → Θ ⊢ τ wf → τ =α τ' → Θ ⊢ τ' wf
  alpha-wf wf AlphaBase = wf
  alpha-wf wf (AlphaVarFree x x₁) = wf
  alpha-wf wf AlphaHole = wf
  alpha-wf (WFArr wf wf₁) (AlphaArr alpha alpha₁) = WFArr (alpha-wf wf alpha) (alpha-wf wf₁ alpha₁)
  alpha-wf (WFForall wf) (AlphaForall alpha) = WFForall (alpha-wf {! wf  !} {!   !})

     -- AlphaForall (prune-pres-alpha2 (alpha-rewrite-gamma (! (comp-lextend-prunel x y y' ΓL1 ΓL2 ΓR1 ΓR2)) (! (comp-lextend-pruner x y y' ΓL1 ΓL2 ΓR1 ΓR2)) (prune-pres-alpha1 (alpha-trans a1 a2)))) -- (alpha-rewrite-gamma (! (comp-lextend x y y' ΓL1 ΓL2)) (! (comp-lextend y' y x ΓR2 ΓR1)) (alpha-trans a1 a2)) -- AlphaForall {!   !}

  -- num-sum : Nat + Nat → Nat 
  -- num-sum (Inl (1+ n)) = 1+ (1+ (num-sum (Inl n)))
  -- num-sum (Inl Z) = Z
  -- num-sum (Inr (1+ n)) = 1+ (1+ (num-sum (Inr n)))
  -- num-sum (Inr Z) = 1+ Z

  -- num-sum-inv : Nat → Nat + Nat 
  -- num-sum-inv Z = Inl Z 
  -- num-sum-inv (1+ Z) = Inr Z 
  -- num-sum-inv (1+ (1+ n)) with num-sum-inv n 
  -- ... | Inl m = Inl (1+ m)
  -- ... | Inr m = Inr (1+ m)

  -- num-sum-correct1 : (n : Nat + Nat) → (num-sum-inv (num-sum n)) == n
  -- num-sum-correct1 (Inl Z) = refl
  -- num-sum-correct1 (Inl (1+ x)) rewrite num-sum-correct1 (Inl x) = refl
  -- num-sum-correct1 (Inr Z) = refl
  -- num-sum-correct1 (Inr (1+ x)) rewrite num-sum-correct1 (Inr x) = refl

  -- num-sum-correct2 : (n : Nat) → (num-sum (num-sum-inv n)) == n
  -- num-sum-correct2 Z = refl
  -- num-sum-correct2 (1+ Z) = refl
  -- num-sum-correct2 (1+ (1+ n)) with num-sum-inv n in eq 
  -- ... | Inl m rewrite (sym eq) rewrite (num-sum-correct2 n) = refl
  -- ... | Inr m rewrite (sym eq) rewrite (num-sum-correct2 n) = refl

  data debruijn-htyp : Set where
    DB-base     : debruijn-htyp
    DB-B     : Nat → debruijn-htyp
    DB-F     : Nat → debruijn-htyp
    DB-⦇-⦈    : debruijn-htyp
    _DB-==>_ : debruijn-htyp → debruijn-htyp → debruijn-htyp
    DB-∀    : debruijn-htyp → debruijn-htyp
  
  debruijn-of-type-ctx : (Nat ctx) → htyp → debruijn-htyp 
  debruijn-of-type-ctx Γ b = DB-base
  debruijn-of-type-ctx Γ (T x) with Γ x 
  ... | Some height = DB-B height
  ... | None = DB-F x
  debruijn-of-type-ctx Γ ⦇-⦈ = DB-⦇-⦈
  debruijn-of-type-ctx Γ (τ ==> τ₁) = (debruijn-of-type-ctx Γ τ) DB-==> (debruijn-of-type-ctx Γ τ₁)
  debruijn-of-type-ctx Γ (·∀ x τ) = DB-∀ (debruijn-of-type-ctx Γ' τ)
    where Γ' = ■(x , Z) ∪ (map (\n → 1+ n) Γ)

  debruijn-of-type : htyp → debruijn-htyp 
  debruijn-of-type = debruijn-of-type-ctx ∅

  data ctx-consist : (Γ1 Γ2 Γ3 Γ4 : Nat ctx) → Set where 
    Empty : ctx-consist ∅ ∅ ∅ ∅ 
    Extend : ∀{Γ1 Γ2 Γ3 Γ4 x y} → ctx-consist Γ1 Γ2 Γ3 Γ4 → ctx-consist (■ (x , y) ∪ Γ1) (■ (y , x) ∪ Γ2) (■ (x , Z) ∪ (map (\n → 1+ n) Γ3)) (■ (y , Z) ∪ (map (\n → 1+ n) Γ4))

  consist-free : ∀{Γ1 Γ2 Γ3 Γ4} → ctx-consist Γ1 Γ2 Γ3 Γ4 → (x : Nat) → (Γ1 x == None) → (Γ2 x == None) → (Γ3 x == None × Γ4 x == None)
  consist-free Empty x _ _ = refl , refl
  consist-free (Extend {x = x} {y = y} consist) input eq1 eq2 with (natEQ x input) 
  consist-free (Extend {x = x} {y = y} consist) input () eq2 | Inl refl
  consist-free (Extend {x = x} {y = y} consist) input () eq2 | Inr neq with (natEQ y input)
  consist-free (Extend {x = x} {y = y} consist) input _ () | Inr neq | Inl refl
  consist-free (Extend {x = x} {y = y} consist) input eq1 eq2 | Inr neq | Inr neq2 with consist-free consist input eq1 eq2 
  ... | (eq3 , eq4) rewrite eq3 rewrite eq4 = refl , refl

  consist-free-inv : ∀{Γ1 Γ2 Γ3 Γ4} → ctx-consist Γ1 Γ2 Γ3 Γ4 → (x y : Nat) → (Γ3 x == None) → (Γ4 y == None) → (Γ1 x == None × Γ2 y == None)
  consist-free-inv Empty x y _ _ = refl , refl
  consist-free-inv (Extend {x = x1} {y = y1} consist) x y eq1 eq2 with (natEQ x1 x) 
  consist-free-inv (Extend {x = x1} {y = y1} consist) x y () eq2 | Inl refl
  consist-free-inv (Extend {x = x1} {y = y1} consist) x y () eq2 | Inr neq with (natEQ y1 y)
  consist-free-inv (Extend {x = x1} {y = y1} consist) x y _ () | Inr neq | Inl refl
  consist-free-inv (Extend {Γ1} {Γ2} {Γ3} {Γ4} {x = x1} {y = y1} consist) x y eq1 eq2 | Inr neq | Inr neq2 with Γ3 x in eq3 | Γ4 y in eq4
  consist-free-inv (Extend {_} {_} {_} {_} {x = x1} {y = y1} consist) x y () eq2 | Inr neq | Inr neq2 | Some h1 | Some h2
  consist-free-inv (Extend {x = x1} {y = y1} consist) x y eq1 eq2 | Inr neq | Inr neq2 | None | None = consist-free-inv consist x y eq3 eq4

  consist-bound : ∀{Γ1 Γ2 Γ3 Γ4} → ctx-consist Γ1 Γ2 Γ3 Γ4 → (x y : Nat) → (Γ1 x == Some y) → (Γ2 y == Some x) → Σ[ h ∈ Nat ] (Γ3 x == Some h × Γ4 y == Some h)
  consist-bound Empty x y () ()
  consist-bound (Extend {x = x1} {y = y1} consist) x y eq1 eq2 with natEQ y1 y | natEQ x1 x 
  ... | Inl refl | Inl refl = Z , refl , refl 
  ... | Inr neq | Inl refl = abort (neq (someinj eq1)) 
  ... | Inl refl | Inr neq = abort (neq (someinj eq2)) 
  ... | Inr neq1 | Inr neq2 with consist-bound consist x y eq1 eq2
  ... | h , eq1 , eq2 rewrite eq1 rewrite eq2 = 1+ h , refl , refl

  consist-height : ∀{Γ1 Γ2 Γ3 Γ4} → ctx-consist Γ1 Γ2 Γ3 Γ4 → (x y h : Nat) → (Γ3 x == Some h) → (Γ4 y == Some h) → (Γ1 x == Some y × Γ2 y == Some x)
  consist-height Empty x y h () ()
  consist-height (Extend {x = x1} {y = y1} consist) x y h eq1 eq2  with (natEQ y1 y) | (natEQ x1 x) 
  consist-height (Extend {x = x1} {y = y1} consist) x y h eq1 eq2 | Inl refl | Inl refl = refl , refl
  consist-height (Extend {Γ1} {Γ2} {Γ3} {Γ4} {x = x1} {y = y1} consist) x y h eq1 eq2 | Inr neq | Inl refl with (Γ4 y)
  consist-height (Extend {x = x1} {y = y1} consist) x y h eq1 eq2 | Inr neq | Inl refl | Some hh rewrite (sym (someinj eq2)) with (someinj eq1)
  ... | () 
  consist-height (Extend {x = x1} {y = y1} consist) x y h eq1 () | Inr neq | Inl refl | None 
  consist-height (Extend {Γ1} {Γ2} {Γ3} {Γ4} {x = x1} {y = y1} consist) x y h eq1 eq2 | Inl refl | Inr neq with (Γ3 x)
  consist-height (Extend {x = x1} {y = y1} consist) x y h eq1 eq2 | Inl refl | Inr neq | Some hh rewrite (sym (someinj eq2)) with (someinj eq1)
  ... | () 
  consist-height (Extend {Γ1} {Γ2} {Γ3} {Γ4} {x = x1} {y = y1} consist) x y h eq1 eq2 | Inr neq1 | Inr neq2 with Γ3 x in eq3 | Γ4 y in eq4 
  consist-height (Extend {x = x1} {y = y1} consist) x y h eq1 eq2 | Inr neq1 | Inr neq2 | Some h1 | Some h2 rewrite (sym (someinj eq1)) rewrite (1+inj h2 h1 (someinj eq2)) = consist-height consist x y h1 eq3 eq4

  equiv-debruijn1 : (τ1 τ2 : htyp) → (Γ1 Γ2 Γ3 Γ4 : Nat ctx) → (ctx-consist Γ1 Γ2 Γ3 Γ4) → (Γ1 , Γ2 ⊢ τ1 =α τ2) → (debruijn-of-type-ctx Γ3 τ1 == debruijn-of-type-ctx Γ4 τ2)
  equiv-debruijn1 .b .b Γ1 Γ2 Γ3 Γ4 consist AlphaBase = refl
  equiv-debruijn1 (T x) (T y) Γ1 Γ2 Γ3 Γ4 consist (AlphaVarFree f1 f2) with (consist-free consist x f1 f2) 
  ... | (f3 , f4) with Γ3 x | Γ4 x 
  ... | None | None = refl
  equiv-debruijn1 (T x) (T y) Γ1 Γ2 Γ3 Γ4 consist (AlphaVarBound b1 b2) with consist-bound consist x y b1 b2
  ... | h , eq1 , eq2 rewrite eq1 rewrite eq2 = refl
  equiv-debruijn1 .⦇-⦈ .⦇-⦈ Γ1 Γ2 Γ3 Γ4 consist AlphaHole = refl
  equiv-debruijn1 (t1 ==> t2) (t3 ==> t4) Γ1 Γ2 Γ3 Γ4 consist (AlphaArr eq eq₁) rewrite 
    equiv-debruijn1 t1 t3 Γ1 Γ2 Γ3 Γ4 consist eq rewrite 
    equiv-debruijn1 t2 t4 Γ1 Γ2 Γ3 Γ4 consist eq₁ = refl
  equiv-debruijn1 (·∀ x τ1) (·∀ y τ2) Γ1 Γ2 Γ3 Γ4 consist (AlphaForall eq) rewrite equiv-debruijn1 τ1 τ2 (■ (x , y) ∪ Γ1) (■ (y , x) ∪ Γ2) (■(x , Z) ∪ (map (\n → 1+ n) Γ3)) (■(y , Z) ∪ (map (\n → 1+ n) Γ4)) (Extend {x = x} {y = y} consist) eq = refl 

  DB-B-inj : ∀ {t1 t2} → (DB-B t1) == (DB-B t2) → t1 == t2
  DB-B-inj {Z} {Z} eq = refl
  DB-B-inj {1+ t1} {1+ .t1} refl = refl

  DB-F-inj : ∀ {t1 t2} → (DB-F t1) == (DB-F t2) → t1 == t2
  DB-F-inj {Z} {Z} eq = refl 
  DB-F-inj {1+ t1} {1+ t2} refl = refl 

  DB-==>-injl : ∀ {t1 t2 t3 t4} → (t1 DB-==> t2) == (t3 DB-==> t4) → t1 == t3
  DB-==>-injl {DB-base} {t2} {DB-base} {t4} eq = refl
  DB-==>-injl {DB-B x} {t2} {DB-B .x} {.t2} refl = refl
  DB-==>-injl {DB-F x} {t2} {DB-F x₁} {t4} refl = refl
  DB-==>-injl {DB-⦇-⦈} {t2} {DB-⦇-⦈} {t4} refl = refl
  DB-==>-injl {t1 DB-==> t3} {t2} {t5 DB-==> t6} {t4} refl = refl
  DB-==>-injl {DB-∀ t1} {t2} {DB-∀ t3} {t4} refl = refl

  DB-==>-injr : ∀ {t1 t2 t3 t4} → (t1 DB-==> t2) == (t3 DB-==> t4) → t2 == t4
  DB-==>-injr {t1} {DB-base} {.t1} {DB-base} refl = refl
  DB-==>-injr {t1} {DB-B x} {.t1} {DB-B .x} refl = refl
  DB-==>-injr {t1} {DB-F x} {.t1} {DB-F x₁} refl = refl
  DB-==>-injr {t1} {DB-⦇-⦈} {.t1} {DB-⦇-⦈} refl = refl
  DB-==>-injr {t1} {t2 DB-==> t3} {.t1} {t5 DB-==> t6} refl = refl
  DB-==>-injr {t1} {DB-∀ t2} {.t1} {DB-∀ t3} refl = refl

  DB-==>-inj : ∀ {t1 t2 t3 t4} → (t1 DB-==> t2) == (t3 DB-==> t4) → t1 == t3 × t2 == t4
  DB-==>-inj {t1} {t2} {t3} {t4} eq = (DB-==>-injl eq , DB-==>-injr eq)

  DB-∀-inj : ∀ {t1 t2} → (DB-∀ t1) == (DB-∀ t2) → t1 == t2
  DB-∀-inj {DB-base} {DB-base} refl = refl
  DB-∀-inj {DB-B x} {DB-B x₁} refl = refl
  DB-∀-inj {DB-F x} {DB-F x₁} refl = refl
  DB-∀-inj {DB-⦇-⦈} {DB-⦇-⦈} refl = refl
  DB-∀-inj {t1 DB-==> t2} {t3 DB-==> t4} refl = refl
  DB-∀-inj {DB-∀ t1} {DB-∀ t2} refl = refl

  equiv-debruijn2 : (τ1 τ2 : htyp) → (Γ1 Γ2 Γ3 Γ4 : Nat ctx) → (ctx-consist Γ1 Γ2 Γ3 Γ4) → (debruijn-of-type-ctx Γ3 τ1 == debruijn-of-type-ctx Γ4 τ2) → (Γ1 , Γ2 ⊢ τ1 =α τ2)
  equiv-debruijn2 b b Γ1 Γ2 Γ3 Γ4 consist eq = AlphaBase
  equiv-debruijn2 (T x) (T y) Γ1 Γ2 Γ3 Γ4 consist eq with Γ3 x in eq1 | Γ4 y in eq2 
  equiv-debruijn2 (T x) (T y) Γ1 Γ2 Γ3 Γ4 consist eq | Some h1 | Some h2 rewrite (DB-B-inj eq) with consist-height consist x y h2 eq1 eq2 
  equiv-debruijn2 (T x) (T y) Γ1 Γ2 Γ3 Γ4 consist eq | Some h1 | Some h2 | (r1 , r2) = AlphaVarBound r1 r2
  equiv-debruijn2 (T x) (T y) Γ1 Γ2 Γ3 Γ4 consist eq | None | None with consist-free-inv consist x y eq1 eq2 
  ... | (eq3 , eq4) rewrite (DB-F-inj eq) = AlphaVarFree eq3 eq4
  equiv-debruijn2 ⦇-⦈ ⦇-⦈ Γ1 Γ2 Γ3 Γ4 consist eq = AlphaHole
  equiv-debruijn2 (τ1 ==> τ2) (τ3 ==> τ4) Γ1 Γ2 Γ3 Γ4 consist eq with DB-==>-inj eq 
  ... | ( eq1 , eq2 ) with equiv-debruijn2 τ1 τ3 Γ1 Γ2 Γ3 Γ4 consist eq1 | equiv-debruijn2 τ2 τ4 Γ1 Γ2 Γ3 Γ4 consist eq2 
  ... | eq1 | eq2 = AlphaArr eq1 eq2
  equiv-debruijn2 (·∀ x τ1) (·∀ y τ2) Γ1 Γ2 Γ3 Γ4 consist eq with DB-∀-inj eq 
  ... | eq2 with equiv-debruijn2 τ1 τ2 (■ (x , y) ∪ Γ1) (■ (y , x) ∪ Γ2) (■(x , Z) ∪ (map (\n → 1+ n) Γ3)) (■(y , Z) ∪ (map (\n → 1+ n) Γ4)) (Extend {x = x} {y = y} consist) eq2 
  ... | re = AlphaForall re
  equiv-debruijn2 (T x) τ2 Γ1 Γ2 Γ3 Γ4 consist eq with Γ3 x 
  equiv-debruijn2 (T x) τ2 Γ1 Γ2 Γ3 Γ4 consist () | Some _
  equiv-debruijn2 (T x) τ2 Γ1 Γ2 Γ3 Γ4 consist () | None 
  equiv-debruijn2 τ1 (T x) Γ1 Γ2 Γ3 Γ4 consist eq with Γ4 x 
  equiv-debruijn2 τ1 (T x) Γ1 Γ2 Γ3 Γ4 consist () | Some _
  equiv-debruijn2 τ1 (T x) Γ1 Γ2 Γ3 Γ4 consist () | None
  
  alpha-transitive : (τ1 τ2 τ3 : htyp) → (τ1 =α τ2) → (τ2 =α τ3) → (τ1 =α τ3)
  alpha-transitive τ1 τ2 τ3 eq1 eq2 with equiv-debruijn1 τ1 τ2 ∅ ∅ ∅ ∅ Empty eq1 | equiv-debruijn1 τ2 τ3 ∅ ∅ ∅ ∅ Empty eq2 
  ... | eq3 | eq4 rewrite (sym eq3) = equiv-debruijn2 τ1 τ3 ∅ ∅ ∅ ∅ Empty eq4
