open import Prelude
open import Nat
open import core
open import contexts

module structural-assumptions where

-- this module contains the signatures of theorems that we intend to
-- prove in the finished artefact. they are all either canonical
-- structural properties of the hypothetical judgements or common
-- properties of contexts. we strongly believe that they are true,
-- especially since they're all standard, but have not yet proven them
-- for our specific choices of implementations.

-- the only assumptions not in this file are 1) for function
-- extensionality in Prelude.agda; funext is known to be independent
-- of Agda, and we have no intension of removing it, and 2) the
-- signature of the disjointness judgements in core.agda used below to
-- break a circular module dependency, and 3) the signature of
-- applying a substitition to a hole in core.agda

postulate
  ∪comm : {A : Set} → (C1 C2 : A ctx) → C1 ## C2 → (C1 ∪ C2) == (C2 ∪ C1)
postulate
  gcomp-extend : ∀{Γ τ x} → Γ gcomplete → τ tcomplete → (Γ ,, (x , τ)) gcomplete
postulate
  subst-weaken : ∀{Δ Γ Γ' Δ' σ} → Δ ## Δ' → Δ , Γ ⊢ σ :s: Γ' → (Δ ∪ Δ') , Γ ⊢ σ :s: Γ'
postulate
  lem-subst : ∀{Δ Γ x τ1 d1 τ d2 } → Δ , Γ ,, (x , τ1) ⊢ d1 :: τ → Δ , Γ ⊢ d2 :: τ1 → Δ , Γ ⊢ [ d2 / x ] d1 :: τ


-- todo: this belongs in contexts once the above are proven and the
-- cyclic dependency gets broken
x∈∪r : {A : Set} → (Γ Γ' : A ctx) (n : Nat) (x : A) → (n , x) ∈ Γ' → Γ' ## Γ → (n , x) ∈ (Γ ∪ Γ')
x∈∪r Γ Γ' n x nx∈ disj = tr (λ qq → (n , x) ∈ qq) (∪comm _ _ disj) (x∈∪l Γ' Γ n x nx∈)

-- see below; this is copied code
lem-deleteme : {A : Set} (y : A) (n m : Nat) → dom (■ (m , y)) n → n == m
lem-deleteme y n m (π1 , π2) with natEQ m n
lem-deleteme y n .n (π1 , π2) | Inl refl = refl
lem-deleteme y n m (π1 , π2) | Inr x = abort (somenotnone (! π2))

-- todo: this lemma belongs in lemmas-disjointness, which already
-- contains lem-deleteme under disjoint-singles; remove one and
-- promote the other once you break the cyclic dependency
lem-apart-sing-disj : {A : Set} {n : Nat} {a : A} {Γ : A ctx} → n # Γ → (■ (n , a)) ## Γ
lem-apart-sing-disj {A} {n} {a} {Γ} apt = asd1 , asd2
  where
    asd1 : (n₁ : Nat) → dom (■ (n , a)) n₁ → n₁ # Γ
    asd1 m d with lem-deleteme _ _ _ d
    asd1 .n d | refl = apt

    asd2 : (n₁ : Nat) → dom Γ n₁ → n₁ # (■ (n , a))
    asd2 m (π1 , π2) with natEQ n m
    asd2 .n (π1 , π2) | Inl refl = abort (somenotnone (! π2 · apt ))
    asd2 m (π1 , π2) | Inr x = refl

-- proably belongs in contexts
ctx-top : {A : Set} → (Γ : A ctx) (n : Nat) (a : A) → (n # Γ) → (n , a) ∈ (Γ ,, (n , a))
ctx-top Γ n a apt = x∈∪r Γ (■ (n , a)) n a (x∈■ n a) (lem-apart-sing-disj apt)
