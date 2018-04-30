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
-- postulate
--   gcomp-extend : ∀{Γ τ x} → Γ gcomplete → τ tcomplete → (Γ ,, (x , τ)) gcomplete
postulate
  subst-weaken : ∀{Δ Γ Γ' Δ' σ} → Δ ## Δ' → Δ , Γ ⊢ σ :s: Γ' → (Δ ∪ Δ') , Γ ⊢ σ :s: Γ'
postulate
  lem-subst : ∀{Δ Γ x τ1 d1 τ d2 } → Δ , Γ ,, (x , τ1) ⊢ d1 :: τ → Δ , Γ ⊢ d2 :: τ1 → Δ , Γ ⊢ [ d2 / x ] d1 :: τ
  -- can also get an apartness premise here, i think; see callsite in preserve-trans in preservation

----- former assumptions that have now been proven, at least up to the
----- assumptions above, but not placed in their rightful files
----- because of cyclic dependency junk


-- todo: this belongs in contexts once the above are proven and the
-- cyclic dependency gets broken
x∈∪r : {A : Set} → (Γ Γ' : A ctx) (n : Nat) (x : A) → (n , x) ∈ Γ' → Γ' ## Γ → (n , x) ∈ (Γ ∪ Γ')
x∈∪r Γ Γ' n x nx∈ disj = tr (λ qq → (n , x) ∈ qq) (∪comm _ _ disj) (x∈∪l Γ' Γ n x nx∈)

-- todo : see below; this is copied code
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

-- todo: belongs in contexts
ctx-top : {A : Set} → (Γ : A ctx) (n : Nat) (a : A) → (n # Γ) → (n , a) ∈ (Γ ,, (n , a))
ctx-top Γ n a apt = x∈∪r Γ (■ (n , a)) n a (x∈■ n a) (lem-apart-sing-disj apt)

-- todo: belongs in contexts
lem-insingeq : {A : Set} {x x' : Nat} {τ τ' : A} → (■ (x , τ)) x' == Some τ' → τ == τ'
lem-insingeq {A} {x} {x'} {τ} {τ'} eq with lem-deleteme τ x' x (τ' , eq)
lem-insingeq {A} {x} {.x} {τ} {τ'} eq | refl with natEQ x x
lem-insingeq refl | refl | Inl refl = refl
lem-insingeq eq | refl | Inr x₁ = abort (somenotnone (! eq))

lem-apart-union-eq : {A : Set} {Γ : A ctx} {x x' : Nat} {τ τ' : A} → x' # Γ → (Γ ∪ ■ (x , τ)) x' == Some τ' → τ == τ'
lem-apart-union-eq {A} {Γ} {x} {x'} {τ} {τ'} apart eq with Γ x'
lem-apart-union-eq apart eq | Some x = abort (somenotnone apart)
lem-apart-union-eq apart eq | None = lem-insingeq eq

lem-neq-union-eq : {A : Set} {Γ : A ctx} {x x' : Nat} {τ τ' : A} → x' ≠ x → (Γ ∪ ■ (x , τ)) x' == Some τ' → Γ x' == Some τ'
lem-neq-union-eq {A} {Γ} {x} {x'} {τ} {τ'} neq eq with Γ x'
lem-neq-union-eq neq eq | Some x = eq
lem-neq-union-eq {A} {Γ} {x} {x'} {τ} {τ'} neq eq | None with natEQ x x'
lem-neq-union-eq neq eq | None | Inl x₁ = abort ((flip neq) x₁)
lem-neq-union-eq neq eq | None | Inr x₁ = abort (somenotnone (! eq))

-- we need this apartness premise because it's false otherwise, given
-- the particular implementation of ,, which is backed by ∪, which
-- queries one side first.
gcomp-extend : ∀{Γ τ x} → Γ gcomplete → τ tcomplete → x # Γ → (Γ ,, (x , τ)) gcomplete
gcomp-extend {Γ} {τ} {x} gc tc apart x_query τ_query x₁ with natEQ x x_query
gcomp-extend {Γ} {τ} {x} gc tc apart .x τ_query x₂ | Inl refl = tr (λ qq → qq tcomplete) (lem-apart-union-eq {Γ = Γ} apart x₂) tc
gcomp-extend {Γ} {τ} {x} gc tc apart x_query τ_query x₂ | Inr x₁ = gc x_query τ_query (lem-neq-union-eq {Γ = Γ} (flip x₁) x₂ )

-- gcomp-extend {Γ} {τ} {x} gc tc aprt x₁ τ₁ x₂ with Γ x
-- gcomp-extend gc tc aprt x₂ τ₁ x₃ | Some x₁ = abort (somenotnone aprt)
-- gcomp-extend {Γ} {τ} {x} gc tc aprt x₁ τ₁ x₂ | None with ctxindirect' Γ x₁
-- gcomp-extend {Γ} {τ} {x} gc tc aprt x₁ τ₁ x₃ | None | Inl (a , eq , inj) with lem-apart-union-eq {Γ = Γ} {!!}  x₃
-- gcomp-extend gc tc aprt x₁ τ₁ x₃ | None | Inl (a , eq , inj) | refl = tc
-- gcomp-extend gc tc aprt x₁ τ₁ x₃ | None | Inr x = {!!}

-- gcomp-extend {Γ} {τ} {x} gc apt tc x' τ' mem with Γ x
-- gcomp-extend gc apt tc x' τ' mem | Some x₁ = abort (somenotnone tc)
-- gcomp-extend {Γ} gc apt refl x' τ' mem | None with ctxindirect Γ x'
-- gcomp-extend {Γ} {x = y} gc tc refl x' τ' mem | None | Inl (a , x) = tr (λ qq → qq tcomplete) (ctxunicity x {!!}) (gc x' a x)
-- gcomp-extend {Γ} gc tc refl x' τ' mem | None | Inr neq with Γ x'
-- gcomp-extend gc tc refl x' τ' mem | None | Inr neq | Some x = abort (somenotnone neq)
-- gcomp-extend gc tc refl x' τ' mem | None | Inr refl | None with lem-insingeq mem
-- gcomp-extend gc tc refl x' τ' mem | None | Inr refl | None | refl = tc

-- (Γ ∪ ■ (x , τ) x₁ | Γ x₁) == Some τ₁
