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

  -- add a new binding to the context, clobbering anything that might have
  -- been there before.
  _,,_ : {A : Set} → A ctx → (Nat × A) → A ctx
  (Γ ,, (x , t)) y with natEQ x y
  (Γ ,, (x , t)) .x | Inl refl = Some t
  (Γ ,, (x , t)) y  | Inr neq  = Γ y

  infixl 10 _,,_

  -- the singleton context
  ■_ : {A : Set} → (Nat × A) → A ctx
  ■ x = ∅ ,, x

  infixr 100 ■_

  -- membership, or presence, in a context
  _∈_ : {A : Set} (p : Nat × A) → (Γ : A ctx) → Set
  (x , y) ∈ Γ = (Γ x) == Some y

  -- apartness for contexts, so that we can follow barendregt's convention
  _#_ : {A : Set} (n : Nat) → (Γ : A ctx) → Set
  x # Γ = (Γ x) == None

  -- disjointness for contexts
  _##_ : {A : Set} → A ctx → A ctx → Set
  _##_ {A} Γ Γ'  = ((n : Nat) (a : A) → Γ n == Some a → Γ' n == None) ×
                   ((n : Nat) (a : A) → Γ' n == Some a → Γ n == None)

  -- without: remove a variable from a context
  _/_ : {A : Set} → A ctx → Nat → A ctx
  (Γ / x) y with natEQ x y
  (Γ / x) .x | Inl refl = None
  (Γ / x) y  | Inr neq  = Γ y

  -- a variable is apart from any context from which it is removed
  aar : {A : Set} → (Γ : A ctx) (x : Nat) → x # (Γ / x)
  aar Γ x with natEQ x x
  aar Γ x | Inl refl = refl
  aar Γ x | Inr x≠x  = abort (x≠x refl)

  -- contexts give at most one binding for each variable
  ctxunicity : {A : Set} → {Γ : A ctx} {n : Nat} {t t' : A} →
               (n , t) ∈ Γ →
               (n , t') ∈ Γ →
               t == t'
  ctxunicity {n = n} p q with natEQ n n
  ctxunicity p q | Inl refl = someinj (! p · q)
  ctxunicity _ _ | Inr x≠x = abort (x≠x refl)

  -- warning: this is union but it assumes WITHOUT CHECKING that the
  -- domains are disjoint.
  _∪_ : {A : Set} → A ctx → A ctx → A ctx
  (C1 ∪ C2) x with C1 x
  (C1 ∪ C2) x | Some x₁ = Some x₁
  (C1 ∪ C2) x | None = C2 x

  x∈sing : {A : Set} → (Γ : A ctx) (n : Nat) (x : A) → (n , x) ∈ (Γ ,, (n , x))
  x∈sing Γ n x with Γ n
  x∈sing Γ n x  | Some y with natEQ n n
  x∈sing Γ n x₁ | Some y | Inl refl = refl
  x∈sing Γ n x₁ | Some y | Inr x = abort (x refl)
  x∈sing Γ n x  | None with natEQ n n
  x∈sing Γ n x₁ | None | Inl refl = refl
  x∈sing Γ n x₁ | None | Inr x = abort (x refl)

  x∈∪ : {A : Set} → (Γ Γ' : A ctx) (n : Nat) (x : A) → (n , x) ∈ Γ → (n , x) ∈ (Γ ∪ Γ')
  x∈∪ Γ Γ' n x xin with Γ n
  x∈∪ Γ Γ' n x₁ xin | Some x = xin
  x∈∪ Γ Γ' n x ()   | None

  -- todo: i thought these would be the right thing to work out some holes,
  -- but they're not even true
  -- lem-union1 : {A : Set} (C1 C2 : A ctx) (x : Nat) (disjoint : C1 ## C2) → (C1 x) == ((C1 ∪ C2) x)
  -- lem-union2 : {A : Set} (C1 C2 : A ctx) (x : Nat) (disjoint : C1 ## C2) → (C2 x) == ((C1 ∪ C2) x)
