open import Prelude
open import List
open import Nat

module contexts where
  -- variables are named with naturals in ė. therefore we represent
  -- contexts as functions from names for variables (nats) to possible
  -- bindings.
  _ctx : Set → Set
  A ctx = Nat → Maybe A

  -- convenient shorthand for the (unique up to fun. ext.) empty context
  ∅ : {A : Set} → A ctx
  ∅ _ = None

  infixr 100 ■_

  -- the domain of a context is those naturals which cuase it to emit some τ
  dom : {A : Set} → A ctx → Nat → Set
  dom {A} Γ x = Σ[ τ ∈ A ] (Γ x == Some τ)

  -- remove a variable from a context
  _\\_ : {A : Set} → A ctx → Nat → A ctx
  (Γ \\ x) y with natEQ x y
  (Γ \\ x) .x | Inl refl = None
  (Γ \\ x) y  | Inr neq  = Γ y

  -- membership, or presence, in a context
  _∈_ : {A : Set} (p : Nat × A) → (Γ : A ctx) → Set
  (x , y) ∈ Γ = (Γ x) == Some y

  -- this packages up an appeal to context memebership into a form
  -- that lets us retain more information in some settings, and
  -- therefore be able to use things like context unicity
  ctxindirect : {A : Set} (Γ : A ctx) (n : Nat) → Σ[ a ∈ A ] (Γ n == Some a) + Γ n == None
  ctxindirect Γ n with Γ n
  ctxindirect Γ n | Some x = Inl (x , refl)
  ctxindirect Γ n | None = Inr refl

  -- apartness for contexts, so that we can follow barendregt's convention
  _#_ : {A : Set} (n : Nat) → (Γ : A ctx) → Set
  x # Γ = (Γ x) == None

  -- disjoint contexts are those which share no mappings
  _##_ : {A : Set} → A ctx → A ctx → Set
  _##_ {A} Γ Γ'  = ((n : Nat) → dom Γ n → n # Γ') × ((n : Nat) → dom Γ' n → n # Γ)

  -- contexts give at most one binding for each variable
  ctxunicity : {A : Set} → {Γ : A ctx} {n : Nat} {t t' : A} →
               (n , t) ∈ Γ →
               (n , t') ∈ Γ →
               t == t'
  ctxunicity {n = n} p q with natEQ n n
  ctxunicity p q | Inl refl = someinj (! p · q)
  ctxunicity _ _ | Inr x≠x = abort (x≠x refl)

  -- warning: this is union, but it assumes WITHOUT CHECKING that the
  -- domains are disjoint.
  _∪_ : {A : Set} → A ctx → A ctx → A ctx
  (C1 ∪ C2) x with C1 x
  (C1 ∪ C2) x | Some x₁ = Some x₁
  (C1 ∪ C2) x | None = C2 x

  -- the singleton context
  ■_ : {A : Set} → (Nat × A) → A ctx
  (■ (x , a)) y with natEQ x y
  (■ (x , a)) .x | Inl refl = Some a
  ... | Inr _ = None

  -- add a new binding to the context, clobbering anything that might have
  -- been there before.
  _,,_ : {A : Set} → A ctx → (Nat × A) → A ctx
  (Γ ,, (x , t)) = Γ ∪ (■ (x , t))

  infixl 10 _,,_

  -- used below in proof of ∪ commutativity and associativity
  lem-dom-union1 : {A : Set} {C1 C2 : A ctx} {x : Nat} → C1 ## C2 → dom C1 x → (C1 ∪ C2) x == C1 x
  lem-dom-union1 {A} {C1} {C2} {x} (d1 , d2) D with C1 x
  lem-dom-union1 (d1 , d2) D | Some x₁ = refl
  lem-dom-union1 (d1 , d2) D | None = abort (somenotnone (! (π2 D)))

  lem-dom-union2 : {A : Set} {C1 C2 : A ctx} {x : Nat} → C1 ## C2 → dom C1 x → (C2 ∪ C1) x == C1 x
  lem-dom-union2 {A} {C1} {C2} {x} (d1 , d2) D with ctxindirect C2 x
  lem-dom-union2 {A} {C1} {C2} {x} (d1 , d2) D | Inl x₁ = abort (somenotnone (! (π2 x₁) · d1 x D ))
  lem-dom-union2 {A} {C1} {C2} {x} (d1 , d2) D | Inr x₁ with C2 x
  lem-dom-union2 (d1 , d2) D | Inr x₂ | Some x₁ = abort (somenotnone x₂)
  lem-dom-union2 (d1 , d2) D | Inr x₁ | None = refl

  -- if the contexts in question are disjoint, then union is commutative
  ∪comm : {A : Set} → (C1 C2 : A ctx) → C1 ## C2 → (C1 ∪ C2) == (C2 ∪ C1)
  ∪comm C1 C2 (d1 , d2)= funext guts
    where
      lem-apart-union1 : {A : Set} (C1 C2 : A ctx) (x : Nat) → x # C1 → x # C2 → x # (C1 ∪ C2)
      lem-apart-union1 C1 C2 x apt1 apt2 with C1 x
      lem-apart-union1 C1 C2 x apt1 apt2 | Some x₁ = abort (somenotnone apt1)
      lem-apart-union1 C1 C2 x apt1 apt2 | None = apt2

      lem-apart-union2 : {A : Set} (C1 C2 : A ctx) (x : Nat) → x # C1 → x # C2 → x # (C2 ∪ C1)
      lem-apart-union2 C1 C2 x apt1 apt2 with C2 x
      lem-apart-union2 C1 C2 x apt1 apt2 | Some x₁ = abort (somenotnone apt2)
      lem-apart-union2 C1 C2 x apt1 apt2 | None = apt1

      guts : (x : Nat) → (C1 ∪ C2) x == (C2 ∪ C1) x
      guts x with ctxindirect C1 x | ctxindirect C2 x
      guts x | Inl (π1 , π2) | Inl (π3 , π4) = abort (somenotnone (! π4 · d1 x (π1 , π2)))
      guts x | Inl x₁ | Inr x₂ = tr (λ qq → qq == (C2 ∪ C1) x) (! (lem-dom-union1 (d1 , d2) x₁)) (tr (λ qq → C1 x == qq) (! (lem-dom-union2 (d1 , d2) x₁)) refl)
      guts x | Inr x₁ | Inl x₂ = tr (λ qq → (C1 ∪ C2) x == qq) (! (lem-dom-union1 (d2 , d1) x₂)) (tr (λ qq → qq == C2 x) (! (lem-dom-union2 (d2 , d1) x₂)) refl)
      guts x | Inr x₁ | Inr x₂ = tr (λ qq → qq == (C2 ∪ C1) x) (! (lem-apart-union1 C1 C2 x x₁ x₂)) (tr (λ qq → None == qq) (! (lem-apart-union2 C1 C2 x x₁ x₂)) refl)


  -- an element in the left of a union is in the union
  x∈∪l : {A : Set} → (Γ Γ' : A ctx) (n : Nat) (x : A) → (n , x) ∈ Γ → (n , x) ∈ (Γ ∪ Γ')
  x∈∪l Γ Γ' n x xin with Γ n
  x∈∪l Γ Γ' n x₁ xin | Some x = xin
  x∈∪l Γ Γ' n x ()   | None

  -- an element in the right of a union is in the union as long as the
  -- contexts are disjoint; this asymmetry reflects the asymmetry in the
  -- definition of union
  x∈∪r : {A : Set} → (Γ Γ' : A ctx) (n : Nat) (x : A) →
                             (n , x) ∈ Γ' →
                             Γ' ## Γ →
                             (n , x) ∈ (Γ ∪ Γ')
  x∈∪r Γ Γ' n x nx∈ disj = tr (λ qq → (n , x) ∈ qq) (∪comm _ _ disj) (x∈∪l Γ' Γ n x nx∈)

  -- an element is in the context formed with just itself
  x∈■ : {A : Set} (n : Nat) (a : A) → (n , a) ∈ (■ (n , a))
  x∈■ n a with natEQ n n
  x∈■ n a | Inl refl = refl
  x∈■ n a | Inr x = abort (x refl)

  -- if an index is in the domain of a singleton context, it's the only
  -- index in the context
  lem-dom-eq : {A : Set} (y : A) (n m : Nat) →
                                 dom (■ (m , y)) n →
                                 n == m
  lem-dom-eq y n m (π1 , π2) with natEQ m n
  lem-dom-eq y n .n (π1 , π2) | Inl refl = refl
  lem-dom-eq y n m (π1 , π2) | Inr x = abort (somenotnone (! π2))

  -- a singleton context formed with an index apart from a context is
  -- disjoint from that context
  lem-apart-sing-disj : {A : Set} {n : Nat} {a : A} {Γ : A ctx} →
                                     n # Γ →
                                     (■ (n , a)) ## Γ
  lem-apart-sing-disj {A} {n} {a} {Γ} apt = asd1 , asd2
    where
      asd1 : (n₁ : Nat) → dom (■ (n , a)) n₁ → n₁ # Γ
      asd1 m d with lem-dom-eq _ _ _ d
      asd1 .n d | refl = apt

      asd2 : (n₁ : Nat) → dom Γ n₁ → n₁ # (■ (n , a))
      asd2 m (π1 , π2) with natEQ n m
      asd2 .n (π1 , π2) | Inl refl = abort (somenotnone (! π2 · apt ))
      asd2 m (π1 , π2) | Inr x = refl

  -- the only index of a singleton context is in its domain
  lem-domsingle : {A : Set} (p : Nat) (q : A) → dom (■ (p , q)) p
  lem-domsingle p q with natEQ p p
  lem-domsingle p q | Inl refl = q , refl
  lem-domsingle p q | Inr x₁ = abort (x₁ refl)


  -- dual of above
  lem-disj-sing-apart : {A : Set} {n : Nat} {a : A} {Γ : A ctx} →
                                     (■ (n , a)) ## Γ →
                                     n # Γ
  lem-disj-sing-apart {A} {n} {a} {Γ} (d1 , d2) = d1 n (lem-domsingle n a)

  -- the singleton context can only produce one non-none result
  lem-insingeq : {A : Set} {x x' : Nat} {τ τ' : A} →
                              (■ (x , τ)) x' == Some τ' →
                              τ == τ'
  lem-insingeq {A} {x} {x'} {τ} {τ'} eq with lem-dom-eq τ x' x (τ' , eq)
  lem-insingeq {A} {x} {.x} {τ} {τ'} eq | refl with natEQ x x
  lem-insingeq refl | refl | Inl refl = refl
  lem-insingeq eq | refl | Inr x₁ = abort (somenotnone (! eq))

  -- if an index doesn't appear in a context, and the union of that context
  -- with a singleton does produce a result, it must have come from the singleton
  lem-apart-union-eq : {A : Set} {Γ : A ctx} {x x' : Nat} {τ τ' : A} →
                                    x' # Γ →
                                    (Γ ∪ ■ (x , τ)) x' == Some τ' →
                                    τ == τ'
  lem-apart-union-eq {A} {Γ} {x} {x'} {τ} {τ'} apart eq with Γ x'
  lem-apart-union-eq apart eq | Some x = abort (somenotnone apart)
  lem-apart-union-eq apart eq | None = lem-insingeq eq

  -- if an index not in a singleton context produces a result from that
  -- singleton unioned with another context, the result must have come from
  -- the other context
  lem-neq-union-eq : {A : Set} {Γ : A ctx} {x x' : Nat} {τ τ' : A} →
                                    x' ≠ x →
                                    (Γ ∪ ■ (x , τ)) x' == Some τ' →
                                    Γ x' == Some τ'
  lem-neq-union-eq {A} {Γ} {x} {x'} {τ} {τ'} neq eq with Γ x'
  lem-neq-union-eq neq eq | Some x = eq
  lem-neq-union-eq {A} {Γ} {x} {x'} {τ} {τ'} neq eq | None with natEQ x x'
  lem-neq-union-eq neq eq | None | Inl x₁ = abort ((flip neq) x₁)
  lem-neq-union-eq neq eq | None | Inr x₁ = abort (somenotnone (! eq))

  -- extending a context with a new index produces the result paired with
  -- that index.
  ctx-top : {A : Set} → (Γ : A ctx) (n : Nat) (a : A) →
                                       (n # Γ) →
                                       (n , a) ∈ (Γ ,, (n , a))
  ctx-top Γ n a apt = x∈∪r Γ (■ (n , a)) n a (x∈■ n a) (lem-apart-sing-disj apt)

  -- if a union of a singleton and a ctx produces no result, the argument
  -- index must be apart from the ctx and disequal to the index of the
  -- singleton
  lem-union-none : {A : Set} {Γ : A ctx} {a : A} {x x' : Nat}
                      → (Γ ∪ ■ (x , a)) x' == None
                      → (x ≠ x') × (x' # Γ)
  lem-union-none {A} {Γ} {a} {x} {x'} emp with ctxindirect Γ x'
  lem-union-none {A} {Γ} {a} {x} {x'} emp | Inl (π1 , π2) with Γ x'
  lem-union-none emp | Inl (π1 , π2) | Some x = abort (somenotnone emp)
  lem-union-none {A} {Γ} {a} {x} {x'} emp | Inl (π1 , π2) | None with natEQ x x'
  lem-union-none emp | Inl (π1 , π2) | None | Inl x₁ = abort (somenotnone (! π2))
  lem-union-none emp | Inl (π1 , π2) | None | Inr x₁ = x₁ , refl
  lem-union-none {A} {Γ} {a} {x} {x'} emp | Inr y with Γ x'
  lem-union-none emp | Inr y | Some x = abort (somenotnone emp)
  lem-union-none {A} {Γ} {a} {x} {x'} emp | Inr y | None with natEQ x x'
  lem-union-none emp | Inr y | None | Inl refl = abort (somenotnone emp)
  lem-union-none emp | Inr y | None | Inr x₁ = x₁ , refl


  --- lemmas building up to a proof of associativity of ∪
  ctxignore1 : {A : Set} (x : Nat) (C1 C2 : A ctx) → x # C1 → (C1 ∪ C2) x == C2 x
  ctxignore1 x C1 C2 apt with ctxindirect C1 x
  ctxignore1 x C1 C2 apt | Inl x₁ = abort (somenotnone (! (π2 x₁) · apt))
  ctxignore1 x C1 C2 apt | Inr x₁ with C1 x
  ctxignore1 x C1 C2 apt | Inr x₂ | Some x₁ = abort (somenotnone (x₂))
  ctxignore1 x C1 C2 apt | Inr x₁ | None = refl

  ctxignore2 : {A : Set} (x : Nat) (C1 C2 : A ctx) → x # C2 → (C1 ∪ C2) x == C1 x
  ctxignore2 x C1 C2 apt with ctxindirect C2 x
  ctxignore2 x C1 C2 apt | Inl x₁ = abort (somenotnone (! (π2 x₁) · apt))
  ctxignore2 x C1 C2 apt | Inr x₁ with C1 x
  ctxignore2 x C1 C2 apt | Inr x₂ | Some x₁ = refl
  ctxignore2 x C1 C2 apt | Inr x₁ | None = x₁

  ctxcollapse1 : {A : Set} → (C1 C2 C3 : A ctx) (x : Nat) →
               (x # C3) →
               (C2 ∪ C3) x == C2 x →
               (C1 ∪ (C2 ∪ C3)) x == (C1 ∪ C2) x
  ctxcollapse1 C1 C2 C3 x apt eq with C2 x
  ctxcollapse1 C1 C2 C3 x apt eq | Some x₁ with C1 x
  ctxcollapse1 C1 C2 C3 x apt eq | Some x₂ | Some x₁ = refl
  ctxcollapse1 C1 C2 C3 x apt eq | Some x₁ | None with C2 x
  ctxcollapse1 C1 C2 C3 x apt eq | Some x₂ | None | Some x₁ = refl
  ctxcollapse1 C1 C2 C3 x apt eq | Some x₁ | None | None = apt
  ctxcollapse1 C1 C2 C3 x apt eq | None with C1 x
  ctxcollapse1 C1 C2 C3 x apt eq | None | Some x₁ = refl
  ctxcollapse1 C1 C2 C3 x apt eq | None | None with C2 x
  ctxcollapse1 C1 C2 C3 x apt eq | None | None | Some x₁ = refl
  ctxcollapse1 C1 C2 C3 x apt eq | None | None | None = eq

  ctxcollapse2 : {A : Set} → (C1 C2 C3 : A ctx) (x : Nat) →
                 (x # C2) →
                 (C2 ∪ C3) x == C3 x →
                 (C1 ∪ (C2 ∪ C3)) x == (C1 ∪ C3) x
  ctxcollapse2 C1 C2 C3 x apt eq with C1 x
  ctxcollapse2 C1 C2 C3 x apt eq | Some x₁ = refl
  ctxcollapse2 C1 C2 C3 x apt eq | None with C2 x
  ctxcollapse2 C1 C2 C3 x apt eq | None | Some x₁ = eq
  ctxcollapse2 C1 C2 C3 x apt eq | None | None = refl

  ctxcollapse3 : {A : Set} → (C1 C2 C3 : A ctx) (x : Nat) →
                 (x # C2) →
                 ((C1 ∪ C2) ∪ C3) x == (C1 ∪ C3) x
  ctxcollapse3 C1 C2 C3 x apt with C1 x
  ctxcollapse3 C1 C2 C3 x apt | Some x₁ = refl
  ctxcollapse3 C1 C2 C3 x apt | None with C2 x
  ctxcollapse3 C1 C2 C3 x apt | None | Some x₁ = abort (somenotnone apt)
  ctxcollapse3 C1 C2 C3 x apt | None | None = refl

  ∪assoc : {A : Set} (C1 C2 C3 : A ctx) → (C2 ## C3) → (C1 ∪ C2) ∪ C3 == C1 ∪ (C2 ∪ C3)
  ∪assoc C1 C2 C3 (d1 , d2) = funext guts
    where
      case2 : (x : Nat) → x # C3 → dom C2 x → ((C1 ∪ C2) ∪ C3) x == (C1 ∪ (C2 ∪ C3)) x
      case2 x apt dom = (ctxignore2 x (C1 ∪ C2) C3 apt) ·
                        ! (ctxcollapse1 C1 C2 C3 x apt (lem-dom-union1 (d1 , d2) dom))

      case34 : (x : Nat) → x # C2 → ((C1 ∪ C2) ∪ C3) x == (C1 ∪ (C2 ∪ C3)) x
      case34 x apt = ctxcollapse3 C1 C2 C3 x apt ·
                        ! (ctxcollapse2 C1 C2 C3 x apt (ctxignore1 x C2 C3 apt))

      guts : (x : Nat) → ((C1 ∪ C2) ∪ C3) x == (C1 ∪ (C2 ∪ C3)) x
      guts x with ctxindirect C2 x | ctxindirect C3 x
      guts x | Inl (π1 , π2) | Inl (π3 , π4) = abort (somenotnone (! π4 · d1 x (π1 , π2)))
      guts x | Inl x₁ | Inr x₂ = case2 x x₂ x₁
      guts x | Inr x₁ | Inl x₂ = case34 x x₁
      guts x | Inr x₁ | Inr x₂ = case34 x x₁
