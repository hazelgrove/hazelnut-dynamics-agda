open import Prelude
open import Nat
open import core


module binders-disjoint-checks where
  -- these are fairly mechanical lemmas that show that the
  -- judgementally-defined binders-disjoint is really a type-directed
  -- function
  mutual
    lem-bdσ-lam : ∀{σ x τ d} → binders-disjoint-σ σ (·λ_[_]_ x τ d) → binders-disjoint-σ σ d
    lem-bdσ-lam BDσId = BDσId
    lem-bdσ-lam (BDσSubst x₁ bd) = BDσSubst (lem-bd-lam x₁) (lem-bdσ-lam bd)

    lem-bd-lam :  ∀{ d1 x τ1 d} → binders-disjoint d1 (·λ_[_]_ x  τ1 d) → binders-disjoint d1 d
    lem-bd-lam BDConst = BDConst
    lem-bd-lam BDVar = BDVar
    lem-bd-lam (BDLam bd (UBLam2 x₂ x₃)) = BDLam (lem-bd-lam bd) x₃
    lem-bd-lam (BDHole x₁) = BDHole (lem-bdσ-lam x₁)
    lem-bd-lam (BDNEHole x₁ bd) = BDNEHole (lem-bdσ-lam x₁) (lem-bd-lam bd)
    lem-bd-lam (BDAp bd bd₁) = BDAp (lem-bd-lam bd) (lem-bd-lam bd₁)
    lem-bd-lam (BDCast bd) = BDCast (lem-bd-lam bd)
    lem-bd-lam (BDFailedCast bd) = BDFailedCast (lem-bd-lam bd)

  mutual
    lem-bdσ-hole : ∀{d u σ σ'} → binders-disjoint-σ σ ⦇⌜ d ⌟⦈⟨ u , σ' ⟩ → binders-disjoint-σ σ d
    lem-bdσ-hole BDσId = BDσId
    lem-bdσ-hole (BDσSubst x bd) = BDσSubst (lem-bd-hole x) (lem-bdσ-hole bd)

    lem-bd-hole : ∀{d1 d u σ} → binders-disjoint d1 ⦇⌜ d ⌟⦈⟨ u , σ ⟩ → binders-disjoint d1 d
    lem-bd-hole BDConst = BDConst
    lem-bd-hole BDVar = BDVar
    lem-bd-hole (BDLam bd (UBNEHole x₁ x₂)) = BDLam (lem-bd-hole bd) x₂
    lem-bd-hole (BDHole x) = BDHole (lem-bdσ-hole x)
    lem-bd-hole (BDNEHole x bd) = BDNEHole (lem-bdσ-hole x) (lem-bd-hole bd)
    lem-bd-hole (BDAp bd bd₁) = BDAp (lem-bd-hole bd) (lem-bd-hole bd₁)
    lem-bd-hole (BDCast bd) = BDCast (lem-bd-hole bd)
    lem-bd-hole (BDFailedCast bd) = BDFailedCast (lem-bd-hole bd)

  mutual
    lem-bdσ-cast : ∀{σ d τ1 τ2} → binders-disjoint-σ σ (d ⟨ τ1 ⇒ τ2 ⟩) → binders-disjoint-σ σ d
    lem-bdσ-cast BDσId = BDσId
    lem-bdσ-cast (BDσSubst x bd) = BDσSubst (lem-bd-cast x) (lem-bdσ-cast bd)

    lem-bd-cast : ∀{d1 d τ1 τ2} → binders-disjoint d1 (d ⟨ τ1 ⇒ τ2 ⟩) → binders-disjoint d1 d
    lem-bd-cast BDConst = BDConst
    lem-bd-cast BDVar = BDVar
    lem-bd-cast (BDLam bd (UBCast x₁)) = BDLam (lem-bd-cast bd) x₁
    lem-bd-cast (BDHole x) = BDHole (lem-bdσ-cast x)
    lem-bd-cast (BDNEHole x bd) = BDNEHole (lem-bdσ-cast x) (lem-bd-cast bd)
    lem-bd-cast (BDAp bd bd₁) = BDAp (lem-bd-cast bd) (lem-bd-cast bd₁)
    lem-bd-cast (BDCast bd) = BDCast (lem-bd-cast bd)
    lem-bd-cast (BDFailedCast bd) = BDFailedCast (lem-bd-cast bd)

  mutual
    lem-bdσ-failedcast : ∀{σ d τ1 τ2} → binders-disjoint-σ σ (d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩) → binders-disjoint-σ σ d
    lem-bdσ-failedcast BDσId = BDσId
    lem-bdσ-failedcast (BDσSubst x bd) = BDσSubst (lem-bd-failedcast x) (lem-bdσ-failedcast bd)

    lem-bd-failedcast : ∀{d1 d τ1 τ2} → binders-disjoint d1 (d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩) → binders-disjoint d1 d
    lem-bd-failedcast BDConst = BDConst
    lem-bd-failedcast BDVar = BDVar
    lem-bd-failedcast (BDLam bd (UBFailedCast x₁)) = BDLam (lem-bd-failedcast bd) x₁
    lem-bd-failedcast (BDHole x) = BDHole (lem-bdσ-failedcast x)
    lem-bd-failedcast (BDNEHole x bd) = BDNEHole (lem-bdσ-failedcast x) (lem-bd-failedcast bd)
    lem-bd-failedcast (BDAp bd bd₁) = BDAp (lem-bd-failedcast bd) (lem-bd-failedcast bd₁)
    lem-bd-failedcast (BDCast bd) = BDCast (lem-bd-failedcast bd)
    lem-bd-failedcast (BDFailedCast bd) = BDFailedCast (lem-bd-failedcast bd)

  mutual
    lem-bdσ-into-cast : ∀{σ d τ1 τ2} → binders-disjoint-σ σ d → binders-disjoint-σ σ (d ⟨ τ1 ⇒ τ2 ⟩)
    lem-bdσ-into-cast BDσId = BDσId
    lem-bdσ-into-cast (BDσSubst x bd) = BDσSubst (lem-bd-into-cast x) (lem-bdσ-into-cast bd)

    lem-bd-into-cast : ∀{d1 d2 τ1 τ2} → binders-disjoint d1 d2 → binders-disjoint d1 (d2 ⟨ τ1 ⇒ τ2 ⟩)
    lem-bd-into-cast BDConst = BDConst
    lem-bd-into-cast BDVar = BDVar
    lem-bd-into-cast (BDLam bd x₁) = BDLam (lem-bd-into-cast bd) (UBCast x₁)
    lem-bd-into-cast (BDHole x) = BDHole (lem-bdσ-into-cast x)
    lem-bd-into-cast (BDNEHole x bd) = BDNEHole (lem-bdσ-into-cast x) (lem-bd-into-cast bd)
    lem-bd-into-cast (BDAp bd bd₁) = BDAp (lem-bd-into-cast bd) (lem-bd-into-cast bd₁)
    lem-bd-into-cast (BDCast bd) = BDCast (lem-bd-into-cast bd)
    lem-bd-into-cast (BDFailedCast bd) = BDFailedCast (lem-bd-into-cast bd)
