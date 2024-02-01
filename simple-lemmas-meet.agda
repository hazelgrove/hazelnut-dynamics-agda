open import Nat
open import Prelude
open import contexts
open import simple-core

data consist-meet-lb : (Γ12 Γ21 Γ31 Γ13 Γ32 Γ23 : Nat ctx) → Set where 
  CMLEmpty : consist-meet-lb ∅ ∅ ∅ ∅ ∅ ∅ 
  CMLExtend : ∀{Γ12 Γ21 Γ31 Γ13 Γ32 Γ23 x y} → (consist-meet-lb Γ12 Γ21 Γ31 Γ13 Γ32 Γ23) → consist-meet-lb ((■ (x , y)) ∪ Γ12) ((■ (y , x)) ∪ Γ21) ((■ (pair (x , y) , x)) ∪ Γ31) ((■ (x , pair (x , y))) ∪ Γ13) ((■ (pair (x , y) , y)) ∪ Γ32) ((■ (y , pair (x , y))) ∪ Γ23)
  CMLExtendL : ∀{Γ12 Γ21 Γ31 Γ13 Γ32 Γ23 x} → (consist-meet-lb Γ12 Γ21 Γ31 Γ13 Γ32 Γ23) → consist-meet-lb ((■ (x , x)) ∪ Γ12) Γ21 ((■ (pair (x , x) , x)) ∪ Γ31) ((■ (x , pair (x , x))) ∪ Γ13) Γ32 Γ23
  CMLExtendR : ∀{Γ12 Γ21 Γ31 Γ13 Γ32 Γ23 x} → (consist-meet-lb Γ12 Γ21 Γ31 Γ13 Γ32 Γ23) → consist-meet-lb Γ12 ((■ (x , x)) ∪ Γ21) Γ31 Γ13 ((■ (pair (x , x) , x)) ∪ Γ32) ((■ (x , pair (x , x))) ∪ Γ23)

consist-meet-helper1 : 
  ∀{Γ12 Γ21 Γ31 Γ13 Γ32 Γ23 x y} → 
  (consist-meet-lb Γ12 Γ21 Γ31 Γ13 Γ32 Γ23) → 
  (x , y) ∈ Γ12 → 
  ((pair (x , y) , x) ∈ Γ31) × ((x , pair (x , y)) ∈ Γ13)
consist-meet-helper1 {Γ12 = Γ12} {x = x} {y = y} (CMLExtend {x = x'} {y = y'} consist) in12 with natEQ x' x 
consist-meet-helper1 (CMLExtend {x = x'} {y = y'} consist) refl | Inl refl rewrite (natEQrefl {pair (x' , y')}) = refl , refl 
consist-meet-helper1 {x = x} {y = y} (CMLExtend {x = x'} {y = y'} consist) in12 | Inr neq with natEQneq h1
  where 
    h1 : (pair (x' , y')) == (pair (x , y)) → ⊥ 
    h1 eq = neq (π1 (pair-inj eq)) 
... | neq rewrite neq = consist-meet-helper1 consist in12
consist-meet-helper1 {x = x} (CMLExtendL {x = x'} consist) in12 with natEQ x' x 
consist-meet-helper1 (CMLExtendL {x = x'} consist) refl | Inl refl rewrite (natEQrefl {pair (x' , x')}) = refl , refl  
consist-meet-helper1 {x = x} {y = y} (CMLExtendL {x = x'} consist) in12 | Inr neq with natEQneq h1
  where 
    h1 : (pair (x' , x')) == (pair (x , y)) → ⊥ 
    h1 eq = neq (π1 (pair-inj eq)) 
... | neq rewrite neq = consist-meet-helper1 consist in12
consist-meet-helper1 (CMLExtendR {x = x'} consist) in12 = consist-meet-helper1 consist in12

consist-meet-helper2 : 
  ∀{Γ12 Γ21 Γ31 Γ13 Γ32 Γ23 x y} → 
  (consist-meet-lb Γ12 Γ21 Γ31 Γ13 Γ32 Γ23) → 
  (y , x) ∈ Γ21 → 
  ((pair (x , y) , y) ∈ Γ32) × ((y , pair (x , y)) ∈ Γ23)
consist-meet-helper2 {Γ12 = Γ12} {x = x} {y = y} (CMLExtend {x = x'} {y = y'} consist) in21 with natEQ y' y 
consist-meet-helper2 (CMLExtend {x = x'} {y = y'} consist) refl | Inl refl rewrite (natEQrefl {pair (x' , y')}) = refl , refl 
consist-meet-helper2 {x = x} {y = y} (CMLExtend {x = x'} {y = y'} consist) in21 | Inr neq with natEQneq h1
  where 
    h1 : (pair (x' , y')) == (pair (x , y)) → ⊥ 
    h1 eq = neq (π2 (pair-inj eq)) 
... | neq rewrite neq = consist-meet-helper2 consist in21 
consist-meet-helper2 {y = y} (CMLExtendR {x = x'} consist) in21 with natEQ x' y 
consist-meet-helper2 (CMLExtendR {x = x'} consist) refl | Inl refl rewrite (natEQrefl {pair (x' , x')}) = refl , refl  
consist-meet-helper2 {x = x} {y = y} (CMLExtendR {x = x'} consist) in21 | Inr neq with natEQneq h1
  where 
    h1 : (pair (x' , x')) == (pair (x , y)) → ⊥ 
    h1 eq = neq (π2 (pair-inj eq)) 
... | neq rewrite neq = consist-meet-helper2 consist in21
consist-meet-helper2 (CMLExtendL {x = x'} consist) in21 = consist-meet-helper2 consist in21



meet-lb : ∀{Γ12 Γ21 Γ31 Γ13 Γ32 Γ23 τ1 τ2 τ3} → (consist-meet-lb Γ12 Γ21 Γ31 Γ13 Γ32 Γ23) → Γ12 , Γ21 ⊢ τ1 ⊓ τ2 == τ3 → ((Γ31 , Γ13 ⊢ τ3 ⊑t τ1) × (Γ32 , Γ23 ⊢ τ3 ⊑t τ2))
meet-lb consist JoinBase = PTBase , PTBase 
meet-lb consist (JoinVar in21 in12) with consist-meet-helper1 consist in21 | consist-meet-helper2 consist in12
... | in1 , in2 | in3 , in4 = PTTVarBound in1 in2 , PTTVarBound in3 in4
meet-lb consist (JoinArr meet1 meet2) = PTArr (π1 (meet-lb consist meet1)) (π1 (meet-lb consist meet2)) , PTArr (π2 (meet-lb consist meet1)) (π2 (meet-lb consist meet2))
meet-lb consist (JoinForall meet) = PTForall (π1 (meet-lb (CMLExtend consist) meet)) , PTForall (π2 (meet-lb (CMLExtend consist) meet))
meet-lb consist JoinHoleHole = PTHole , PTHole
meet-lb consist JoinHoleBase = PTHole , PTBase
meet-lb consist (JoinHoleVar in21) with consist-meet-helper2 consist in21 
... | in1 , in2 = PTHole , PTTVarBound in1 in2
meet-lb consist (JoinHoleArr meet1 meet2) = PTHole , (PTArr (π2 (meet-lb consist meet1)) (π2 (meet-lb consist meet2)))
meet-lb consist (JoinHoleForall meet) = PTHole , PTForall (π2 (meet-lb (CMLExtendR consist) meet))
meet-lb consist JoinBaseHole = PTBase , PTHole
meet-lb consist (JoinVarHole in12) with consist-meet-helper1 consist in12
... | in1 , in2 = PTTVarBound in1 in2 , PTHole
meet-lb consist (JoinArrHole meet1 meet2) = (PTArr (π1 (meet-lb consist meet1)) (π1 (meet-lb consist meet2))) , PTHole
meet-lb consist (JoinForallHole meet) = PTForall ((π1 (meet-lb (CMLExtendL consist) meet))) , PTHole 