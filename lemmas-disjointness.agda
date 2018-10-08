open import Prelude
open import Nat
open import core
open import contexts

module lemmas-disjointness where
  -- disjointness is commutative
  ##-comm : {A : Set} {Δ1 Δ2 : A ctx} → Δ1 ## Δ2 → Δ2 ## Δ1
  ##-comm (π1 , π2) = π2 , π1

  -- the empty context is disjoint from any context
  empty-disj : {A : Set} (Γ : A ctx) → ∅ ## Γ
  empty-disj Γ = ed1 , ed2
   where
    ed1 : {A : Set} (n : Nat) → dom {A} ∅ n → n # Γ
    ed1 n (π1 , ())

    ed2 : {A : Set} (n : Nat) → dom Γ n →  _#_ {A} n ∅
    ed2 _ _ = refl

  -- two singleton contexts with different indices are disjoint
  disjoint-singles : {A : Set} {x y : A} {u1 u2 : Nat} → u1 ≠ u2 → (■ (u1 , x)) ## (■ (u2 , y))
  disjoint-singles {_} {x} {y} {u1} {u2} neq = ds1 , ds2
    where
      ds1 : (n : Nat) → dom (■ (u1 , x)) n → n # (■ (u2 , y))
      ds1 n d with lem-dom-eq _ _ _ d
      ds1 .u1 d | refl with natEQ u2 u1
      ds1 .u1 d | refl | Inl xx = abort (neq (! xx))
      ds1 .u1 d | refl | Inr x₁ = refl

      ds2 : (n : Nat) → dom (■ (u2 , y)) n → n # (■ (u1 , x))
      ds2 n d with lem-dom-eq _ _ _ d
      ds2 .u2 d | refl with natEQ u1 u2
      ds2 .u2 d | refl | Inl x₁ = abort (neq x₁)
      ds2 .u2 d | refl | Inr x₁ = refl

  -- the only index of a singleton context is in its domain
  lem-domsingle : {A : Set} (p : Nat) (q : A) → dom (■ (p , q)) p
  lem-domsingle p q with natEQ p p
  lem-domsingle p q | Inl refl = q , refl
  lem-domsingle p q | Inr x₁ = abort (x₁ refl)

  -- if singleton contexts are disjoint, their indices must be disequal
  singles-notequal : {A : Set} {x y : A} {u1 u2 : Nat} →
                          (■ (u1 , x)) ## (■ (u2 , y)) →
                          u1 ≠ u2
  singles-notequal {A} {x} {y} {u1} {u2} (d1 , d2) = lem2 u1 u2 y (d1 u1 (lem-domsingle u1 x))
    where
      lem2 : {A : Set} (p r : Nat) (q : A) → p # (■ (r , q)) → p ≠ r
      lem2 p r q apt with natEQ r p
      lem2 p .p q apt | Inl refl = abort (somenotnone apt)
      lem2 p r q apt | Inr x₁ = flip x₁

  -- dual of lem2 above; if two indices are disequal, then either is apart
  -- from the singleton formed with the other
  apart-singleton : {A : Set} → ∀{x y} → {τ : A} →
                          x ≠ y →
                          x # (■ (y , τ))
  apart-singleton {A} {x} {y} {τ} neq with natEQ y x
  apart-singleton neq | Inl x₁ = abort ((flip neq) x₁)
  apart-singleton neq | Inr x₁ = refl

  -- if an index is apart from two contexts, it's apart from their union as
  -- well. used below and in other files, so it's outside the local scope.
  apart-parts : {A : Set} (Γ1 Γ2 : A ctx) (n : Nat) → n # Γ1 → n # Γ2 → n # (Γ1 ∪ Γ2)
  apart-parts Γ1 Γ2 n apt1 apt2 with Γ1 n
  apart-parts _ _ n refl apt2 | .None = apt2

  -- this is just for convenience; it shows up a lot.
  apart-extend1 : {A : Set} → ∀{ x y τ} → (Γ : A ctx)  → x ≠ y → x # Γ → x # (Γ ,, (y , τ))
  apart-extend1 {A} {x} {y} {τ} Γ neq apt = apart-parts Γ (■ (y , τ)) x apt (apart-singleton neq)

  -- if both parts of a union are disjoint with a target, so is the union
  disjoint-parts : {A : Set} {Γ1 Γ2 Γ3 : A ctx} → Γ1 ## Γ3 → Γ2 ## Γ3 → (Γ1 ∪ Γ2) ## Γ3
  disjoint-parts {_} {Γ1} {Γ2} {Γ3} D13 D23 = d31 , d32
    where
      dom-split : {A : Set} → (Γ1 Γ2 : A ctx) (n : Nat) → dom (Γ1 ∪ Γ2) n → dom Γ1 n + dom Γ2 n
      dom-split Γ4 Γ5 n (π1 , π2) with Γ4 n
      dom-split Γ4 Γ5 n (π1 , π2) | Some x = Inl (x , refl)
      dom-split Γ4 Γ5 n (π1 , π2) | None = Inr (π1 , π2)

      d31 : (n : Nat) → dom (Γ1 ∪ Γ2) n → n # Γ3
      d31 n D with dom-split Γ1 Γ2 n D
      d31 n D | Inl x = π1 D13 n x
      d31 n D | Inr x = π1 D23 n x

      d32 : (n : Nat) → dom Γ3 n → n # (Γ1 ∪ Γ2)
      d32 n D = apart-parts Γ1 Γ2 n (π2 D13 n D) (π2 D23 n D)

  -- if a union is disjoint with a target, so is the left unand
  disjoint-union1 : {A : Set} {Γ1 Γ2 Δ : A ctx} → (Γ1 ∪ Γ2) ## Δ → Γ1 ## Δ
  disjoint-union1 {Γ1 = Γ1} {Γ2 = Γ2} {Δ = Δ} (ud1 , ud2) = du11 , du12
    where
      dom-union1 : {A : Set} (Γ1 Γ2 : A ctx) (n : Nat) → dom Γ1 n → dom (Γ1 ∪ Γ2) n
      dom-union1 Γ1 Γ2 n (π1 , π2) with Γ1 n
      dom-union1 Γ1 Γ2 n (π1 , π2) | Some x = x , refl
      dom-union1 Γ1 Γ2 n (π1 , ()) | None

      apart-union1 : {A : Set} (Γ1 Γ2 : A ctx) (n : Nat) → n # (Γ1 ∪ Γ2) → n # Γ1
      apart-union1 Γ1 Γ2 n aprt with Γ1 n
      apart-union1 Γ1 Γ2 n () | Some x
      apart-union1 Γ1 Γ2 n aprt | None = refl

      du11 : (n : Nat) → dom Γ1 n → n # Δ
      du11 n dom = ud1 n (dom-union1 Γ1 Γ2 n dom)

      du12 : (n : Nat) → dom Δ n → n # Γ1
      du12 n dom = apart-union1 Γ1 Γ2 n (ud2 n dom)

  -- if a union is disjoint with a target, so is the right unand
  disjoint-union2 : {A : Set} {Γ1 Γ2 Δ : A ctx} → (Γ1 ∪ Γ2) ## Δ → Γ2 ## Δ
  disjoint-union2 {Γ1 = Γ1} {Γ2 = Γ2} {Δ = Δ} (ud1 , ud2) = du21 , du22
    where
      dom-union2 : {A : Set} (Γ1 Γ2 : A ctx) (n : Nat) → dom Γ2 n → dom (Γ1 ∪ Γ2) n
      dom-union2 Γ1 Γ2 n (π1 , π2) with Γ1 n
      dom-union2 Γ3 Γ4 n (π1 , π2) | Some x = x , refl
      dom-union2 Γ3 Γ4 n (π1 , π2) | None = π1 , π2

      apart-union2 : {A : Set} (Γ1 Γ2 : A ctx) (n : Nat) → n # (Γ1 ∪ Γ2) → n # Γ2
      apart-union2 Γ1 Γ2 n aprt with Γ1 n
      apart-union2 Γ3 Γ4 n () | Some x
      apart-union2 Γ3 Γ4 n aprt | None = aprt

      du21 : (n : Nat) → dom Γ2 n → n # Δ
      du21 n dom = ud1 n (dom-union2 Γ1  Γ2 n dom)

      du22 : (n : Nat) → dom Δ n → n # Γ2
      du22 n dom = apart-union2 Γ1 Γ2 n (ud2 n dom)
