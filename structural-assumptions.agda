open import Prelude
open import Nat
open import core
open import contexts

module structural-assumptions where

-- this module contains postualtes that we intend to remove in the finished
-- artefact. they are all either canonical structural properties of the
-- hypothetical judgements or common properties of contexts. we strongly
-- believe that they are true, especially since they're all standard, but
-- have not yet proven them for our specific choices of implementations.

-- the only postualte not in this file is for function extensionality in
-- Prelude.agda. funext is known to be independent of Agda, and we have no
-- intension of removing it.


postulate -- TODO
  ∪comm : {A : Set} → (C1 C2 : A ctx) → C1 ## C2 → (C1 ∪ C2) == (C2 ∪ C1)
  x∈sing : {A : Set} → (Γ : A ctx) (n : Nat) (a : A) → (n , a) ∈ (Γ ,, (n , a))
  x∈∪r : {A : Set} → (Γ Γ' : A ctx) (n : Nat) (x : A) → (n , x) ∈ Γ' → Γ ## Γ' → (n , x) ∈ (Γ ∪ Γ') -- follows from comm?
