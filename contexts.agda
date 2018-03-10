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

  -- membership, or presence, in a context
  _∈_ : {A : Set} (p : Nat × A) → (Γ : A ctx) → Set
  (x , y) ∈ Γ = (Γ x) == Some y

  -- apartness for contexts, so that we can follow barendregt's convention
  _#_ : {A : Set} (n : Nat) → (Γ : A ctx) → Set
  x # Γ = (Γ x) == None

  -- disjointness for contexts
  _##_ : {A : Set} → A ctx → A ctx → Set
  _##_ {A} Γ Γ'  = ((n : Nat) → dom Γ n → n # Γ') × ((n : Nat) → dom Γ' n → n # Γ)

  ##-comm : {A : Set} {Δ1 Δ2 : A ctx} → Δ1 ## Δ2 → Δ2 ## Δ1
  ##-comm (π1 , π2) = π2 , π1

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

  x∈∪l : {A : Set} → (Γ Γ' : A ctx) (n : Nat) (x : A) → (n , x) ∈ Γ → (n , x) ∈ (Γ ∪ Γ')
  x∈∪l Γ Γ' n x xin with Γ n
  x∈∪l Γ Γ' n x₁ xin | Some x = xin
  x∈∪l Γ Γ' n x ()   | None

  lem-stop : {A : Set} (Γ : A ctx) (x : Nat) → (Σ[ a ∈ A ] (Γ x == Some a) + (Γ x == None))
  lem-stop Γ x with Γ x
  lem-stop Γ x | Some x₁ = Inl (x₁ , refl)
  lem-stop Γ x | None = Inr refl

  x∈■ : {A : Set} (n : Nat) (a : A) → (n , a) ∈ (■ (n , a))
  x∈■ n a with natEQ n n
  x∈■ n a | Inl refl = refl
  x∈■ n a | Inr x = abort (x refl)

  -- todo: this is almost a proof of ∪comm
  -- ∪comm'guts : {A : Set} → (C1 C2 : A ctx) → (C1 ## C2) → (x : Nat) → ((C1 ∪ C2) x) == ((C2 ∪ C1) x)
  -- ∪comm'guts C1 C2 disj x with lem-stop C1 x | lem-stop C2 x
  -- ∪comm'guts C1 C2 disj x | Inl x₁ | Inl x₂ = abort (somenotnone (! (π2 x₂) · (π1 disj) x x₁))
  -- ∪comm'guts C1 C2 disj x | Inl x₁ | Inr x₂ = {!!}
  -- ∪comm'guts C1 C2 disj x | Inr x₁ | Inl x₂ = {!!}
  -- ∪comm'guts C1 C2 disj x | Inr x₁ | Inr x₂ with x₁ · (! x₂)
  -- ... | qq = {!ap1 (λ ff → C1 ∪ ff == C2 ∪ ff) !}

  -- ∪comm' : {A : Set} → (C1 C2 : A ctx) → (C1 ## C2) → (C1 ∪ C2) == (C2 ∪ C1)
  -- ∪comm' C1 C2 disj = funext (∪comm'guts C1 C2 disj)
