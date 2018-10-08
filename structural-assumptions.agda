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

-- the only assumptions not in this file are 1) for function extensionality
-- in Prelude.agda; funext is known to be independent of Agda, and we have
-- no intension of removing it, and 2) the structural properties in
-- structural.agda, and 3) the signature of applying a substitition to a
-- hole in core.agda

  -- partial proof in lemmas-subst-ta
  postulate
    lem-subst : ∀{Δ Γ x τ1 d1 τ d2 } → x # Γ → Δ , Γ ,, (x , τ1) ⊢ d1 :: τ → Δ , Γ ⊢ d2 :: τ1 → Δ , Γ ⊢ [ d2 / x ] d1 :: τ

  -- todo: there's a freshness concern here; i'm not sure if just
  -- being apart from Γ is good enough. in POPL work it wasn't, we
  -- wanted really aggressive freshness because of barendrecht's. we
  -- might be able to generate that freshness from the first two
  -- premises.
  postulate
    weaken-ana-expand : ∀{ Γ e τ e' τ' Δ x τ* } → x # Γ
                                                → Γ ⊢ e ⇐ τ ~> e' :: τ' ⊣ Δ
                                                → (Γ ,, (x , τ*)) ⊢ e ⇐ τ ~> e' :: τ' ⊣ Δ
