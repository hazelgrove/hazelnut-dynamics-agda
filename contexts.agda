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

  -- membership, or presence, in a context
  _∈_ : {A : Set} (p : Nat × A) → (Γ : A ctx) → Set
  (x , y) ∈ Γ = (Γ x) == Some y

  -- apartness for contexts, so that we can follow barendregt's convention
  _#_ : {A : Set} (n : Nat) → (Γ : A ctx) → Set
  x # Γ = (Γ x) == None

  -- disjointness for contexts
  _##_ : {A : Set} → A ctx → A ctx → Set
  _##_ {A} Γ Γ'  = ((n : Nat) (a : A) → Γ n  == Some a → n # Γ') ×
                   ((n : Nat) (a : A) → Γ' n == Some a → n # Γ )

  -- without: remove a variable from a context
  _//_ : {A : Set} → A ctx → Nat → A ctx
  (Γ // x) y with natEQ x y
  (Γ // x) .x | Inl refl = None
  (Γ // x) y  | Inr neq  = Γ y

  -- a variable is apart from any context from which it is removed
  aar : {A : Set} → (Γ : A ctx) (x : Nat) → x # (Γ // x)
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

  x∈∪l : {A : Set} → (Γ Γ' : A ctx) (n : Nat) (x : A) → (n , x) ∈ Γ → (n , x) ∈ (Γ ∪ Γ')
  x∈∪l Γ Γ' n x xin with Γ n
  x∈∪l Γ Γ' n x₁ xin | Some x = xin
  x∈∪l Γ Γ' n x ()   | None

  lem-stop : {A : Set} (Γ : A ctx) (x : Nat) → (Σ[ a ∈ A ] ((x , a) ∈ Γ)) + (x # Γ)
  lem-stop Γ x with Γ x
  lem-stop Γ x | Some x₁ = Inl (x₁ , refl)
  lem-stop Γ x | None = Inr refl


  -- x∈∪r Γ Γ' n x xin d with lem-stop Γ n
  -- x∈∪r Γ Γ' n x₁ xin d | Inl (a , ain) = {!ain!}
  -- x∈∪r Γ Γ' n x₁ xin d | Inr x = {!!}


  x∈■ : {A : Set} (n : Nat) (a : A) → (n , a) ∈ (■ (n , a))
  x∈■ n a with natEQ n n
  x∈■ n a | Inl refl = refl
  x∈■ n a | Inr x = abort (x refl)


  postulate -- TODO
    ∪comm : {A : Set} → (C1 C2 : A ctx) → (C1 ∪ C2) == (C2 ∪ C1)
    x∈sing : {A : Set} → (Γ : A ctx) (n : Nat) (a : A) → (n , a) ∈ (Γ ,, (n , a))
    x∈∪r : {A : Set} → (Γ Γ' : A ctx) (n : Nat) (x : A) → (n , x) ∈ Γ' → Γ ## Γ' → (n , x) ∈ (Γ ∪ Γ') -- follows from comm?

  -- x∈∪2 Γ Γ' n x₁ xin | None   | _ = abort (somenotnone (! xin))

  -- x∈∪■ : {A : Set} → (Γ : A ctx) (n : Nat) (a : A) → (n , a) ∈ (Γ ∪ (■ (n , a)))
  -- x∈∪■ Γ n a with natEQ n n
  -- x∈∪■ Γ n a | Inl refl = {!!} -- it might be in Γ because i don't know that they're disjoint. this is where that premise gets you
  -- x∈∪■ Γ n a | Inr x = {!!}

  -- x∈sing Γ n a  = {!!} -- x∈∪2 Γ (■ (n , a)) n a (x∈■ n a)
