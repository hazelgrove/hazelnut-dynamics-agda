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
  subst-weaken : ∀{Δ Γ Γ' Δ' σ} → Δ ## Δ' → Δ , Γ ⊢ σ :s: Γ' → (Δ ∪ Δ') , Γ ⊢ σ :s: Γ'
postulate
  lem-subst : ∀{Δ Γ x τ1 d1 τ d2 } → Δ , Γ ,, (x , τ1) ⊢ d1 :: τ → Δ , Γ ⊢ d2 :: τ1 → Δ , Γ ⊢ [ d2 / x ] d1 :: τ
  -- can also get an apartness premise here, i think; see callsite in preserve-trans in preservation. probably need it.
