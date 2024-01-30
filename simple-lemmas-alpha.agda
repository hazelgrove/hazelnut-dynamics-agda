open import Prelude
open import contexts
open import Nat
open import simple-core
open import rewrite-util

module simple-lemmas-alpha where

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

  alpha-refl-ta : ∀{Θ Γ d τ } → Θ , Γ ⊢ d :: τ → Σ[ τ' ∈ htyp ] (τ' =α τ × Θ , Γ ⊢ d :: τ')
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

  -- alpha-wf : ∀{Θ τ τ'} → Θ ⊢ τ wf → τ =α τ' → Θ ⊢ τ' wf
  -- alpha-wf wf AlphaBase = wf
  -- alpha-wf wf (AlphaVarFree x x₁) = wf
  -- alpha-wf wf AlphaHole = wf
  -- alpha-wf (WFArr wf wf₁) (AlphaArr alpha alpha₁) = WFArr (alpha-wf wf alpha) (alpha-wf wf₁ alpha₁)
  -- alpha-wf (WFForall apt wf) (AlphaForall alpha) = WFForall {!   !} (alpha-wf {! wf  !} {!   !})


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
  consist-free (Extend {x = x} {y = y} consist) x () eq2 | Inl refl
  consist-free (Extend {x = x} {y = y} consist) input eq1 eq2 | Inr neq with (natEQ y input) 
  consist-free (Extend {x = x} {y = .input} consist) input eq1 () | Inr neq | Inl refl
  consist-free (Extend {x = x} {y = y} consist) input eq1 eq2 | Inr neq | Inr neq2 with consist-free consist input eq1 eq2 
  ... | (eq3 , eq4) rewrite eq3 rewrite eq4 = refl , refl 

  consist-free-inv : ∀{Γ1 Γ2 Γ3 Γ4} → ctx-consist Γ1 Γ2 Γ3 Γ4 → (x y : Nat) → (Γ3 x == None) → (Γ4 y == None) → (Γ1 x == None × Γ2 y == None)
  consist-free-inv Empty x y _ _ = refl , refl
  consist-free-inv (Extend {x = x1} {y = y1} consist) x y eq1 eq2 with (natEQ x1 x) 
  consist-free-inv (Extend {x = x1} {y = y1} consist) x y () eq2 | Inl refl
  consist-free-inv (Extend {x = x1} {y = y1} consist) x y eq1 eq2 | Inr neq with (natEQ y1 y)
  consist-free-inv (Extend {x = x1} {y = y1} consist) x y eq1 () | Inr neq | Inl refl
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
  equiv-debruijn2 ⦇-⦈ ⦇-⦈ Γ1 Γ2 Γ3 Γ4 consist eq = AlphaHole
  equiv-debruijn2 (τ1 ==> τ2) (τ3 ==> τ4) Γ1 Γ2 Γ3 Γ4 consist eq with DB-==>-inj eq 
  ... | ( eq1 , eq2 ) with equiv-debruijn2 τ1 τ3 Γ1 Γ2 Γ3 Γ4 consist eq1 | equiv-debruijn2 τ2 τ4 Γ1 Γ2 Γ3 Γ4 consist eq2 
  ... | eq1 | eq2 = AlphaArr eq1 eq2
  equiv-debruijn2 (·∀ x τ1) (·∀ y τ2) Γ1 Γ2 Γ3 Γ4 consist eq with DB-∀-inj eq 
  ... | eq2 with equiv-debruijn2 τ1 τ2 (■ (x , y) ∪ Γ1) (■ (y , x) ∪ Γ2) (■(x , Z) ∪ (map (\n → 1+ n) Γ3)) (■(y , Z) ∪ (map (\n → 1+ n) Γ4)) (Extend {x = x} {y = y} consist) eq2 
  ... | re = AlphaForall re
  equiv-debruijn2 (T x) τ2 Γ1 Γ2 Γ3 Γ4 consist eq with Γ3 x in eq1
  equiv-debruijn2 (T x) (T y) Γ1 Γ2 Γ3 Γ4 consist eq | Some h1 with Γ4 y in eq2 
  equiv-debruijn2 (T x) (T y) Γ1 Γ2 Γ3 Γ4 consist eq | Some h1 | Some h2 rewrite (DB-B-inj eq) with consist-height consist x y h2 eq1 eq2
  equiv-debruijn2 (T x) (T y) Γ1 Γ2 Γ3 Γ4 consist eq | Some h1 | Some h2 | (r1 , r2) = AlphaVarBound r1 r2
  equiv-debruijn2 (T x) (T y) Γ1 Γ2 Γ3 Γ4 consist eq | None with Γ4 y in eq2 
  equiv-debruijn2 (T x) (T y) Γ1 Γ2 Γ3 Γ4 consist eq | None | None with consist-free-inv consist x y eq1 eq2 
  ... | (eq3 , eq4) rewrite (DB-F-inj eq) = AlphaVarFree eq3 eq4
  equiv-debruijn2 τ1 (T y) Γ1 Γ2 Γ3 Γ4 consist eq with Γ4 y in eq2
  equiv-debruijn2 (T x) (T y) Γ1 Γ2 Γ3 Γ4 consist eq | Some h2 with Γ3 x in eq1 
  equiv-debruijn2 (T x) (T y) Γ1 Γ2 Γ3 Γ4 consist eq | Some h2 | Some h1 rewrite (DB-B-inj eq) with consist-height consist x y h2 eq1 eq2
  equiv-debruijn2 (T x) (T y) Γ1 Γ2 Γ3 Γ4 consist eq | Some h2 | Some h1 | (r1 , r2) = AlphaVarBound r1 r2
  equiv-debruijn2 (T x) (T y) Γ1 Γ2 Γ3 Γ4 consist eq | None with Γ3 x in eq1 
  equiv-debruijn2 (T x) (T y) Γ1 Γ2 Γ3 Γ4 consist eq | None | None with consist-free-inv consist x y eq1 eq2 
  ... | (eq3 , eq4) rewrite (DB-F-inj eq) = AlphaVarFree eq3 eq4
  
  alpha-transitive : (τ1 τ2 τ3 : htyp) → (τ1 =α τ2) → (τ2 =α τ3) → (τ1 =α τ3)
  alpha-transitive τ1 τ2 τ3 eq1 eq2 with equiv-debruijn1 τ1 τ2 ∅ ∅ ∅ ∅ Empty eq1 | equiv-debruijn1 τ2 τ3 ∅ ∅ ∅ ∅ Empty eq2 
  ... | eq3 | eq4 rewrite (sym eq3) = equiv-debruijn2 τ1 τ3 ∅ ∅ ∅ ∅ Empty eq4

  alpha-trans : ∀{τ1 τ2 τ3} → τ1 =α τ2 → τ2 =α τ3 → τ1 =α τ3
  alpha-trans {τ1} {τ2} {τ3} = alpha-transitive τ1 τ2 τ3


  -- lemma-alpha-forall-helper : ∀{t τ τ' ΓL ΓR} → ΓL , ΓR ⊢ τ =α τ' → ((■ (t , t)) ∪ ΓL) , ((■ (t , t)) ∪ ΓR) ⊢ τ =α τ'
  -- lemma-alpha-forall-helper alpha = {!   !}

  -- lemma-alpha-forall : ∀{t τ τ'} → τ =α τ' → ·∀ t τ =α ·∀ t τ'
  -- lemma-alpha-forall alpha = {!   !}
  