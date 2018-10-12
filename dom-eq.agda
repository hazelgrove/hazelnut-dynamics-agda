open import Prelude
open import Nat
open import core
open import contexts
open import lemmas-disjointness


module dom-eq where
  -- main definition: two contexts are domain-equal when they produce (Some
  -- x) on the same indices. note that the context need not map indices to
  -- even the same type of contents; this is just a property about the
  -- domains. the proofs that follow establish that this property is
  -- respected in the appropriate ways by the context maniupulation
  -- operators we use in the other judgements.
  dom-eq : {A B : Set} → A ctx → B ctx → Set
  dom-eq {A} {B} C1 C2 = ((n : Nat) → Σ[ x ∈ A ]( C1 n == Some x) → (Σ[ y ∈ B ](C2 n == Some y)))×
                         ((n : Nat) → Σ[ y ∈ B ]( C2 n == Some y) → (Σ[ x ∈ A ](C1 n == Some x)))

  -- the empty context has the same domain as itself
  dom-∅ : {A B : Set} → dom-eq (λ _ → None {A}) (λ _ → None {B})
  dom-∅ {A} {B} = (λ n x → abort (somenotnone (! (π2 x)))) , (λ n x → abort (somenotnone (! (π2 x))))

  -- the singleton contexts formed with any contents but the same index has
  -- the same domain
  dom-single : {A B : Set} (x : Nat) {a : A} {b : B} → dom-eq (■ (x , a)) (■ (x , b))
  dom-single {A} {B} x {α} {β} = (λ n x₁ → β , (ap1 (λ qq → (■ (qq , β)) n) (! (lem-dom-eq x₁)) · x∈■ _ _)) ,
                             (λ n x₁ → α , (ap1 (λ qq → (■ (qq , α)) n) (! (lem-dom-eq x₁)) · x∈■ _ _))

  -- if two disjoint contexts each share a domain with two others, those
  -- are also disjoint.
  dom-eq-disj : {A B : Set} {Δ1 Δ2 : A ctx} {H1 H2 : B ctx} →
              H1 ## H2 →
              dom-eq Δ1 H1 →
              dom-eq Δ2 H2 →
              Δ1 ## Δ2
  dom-eq-disj {A} {B} {Δ1} {Δ2} {H1} {H2} (d1 , d2) (de1 , de2) (de3 , de4) = guts1 , guts2
    where
      guts1 : (n : Nat) → dom Δ1 n → n # Δ2
      guts1 n dom1 with ctxindirect H2 n
      guts1 n dom1 | Inl x = abort (somenotnone (! (π2 x) · d1 n (de1 n dom1)))
      guts1 n dom1 | Inr x with ctxindirect Δ2 n
      guts1 n dom1 | Inr x₁ | Inl x = abort (somenotnone (! (π2 (de3 n x)) · x₁))
      guts1 n dom1 | Inr x₁ | Inr x = x

      guts2 : (n : Nat) → dom Δ2 n → n # Δ1
      guts2 n dom2 with ctxindirect H1 n
      guts2 n dom2 | Inl x = abort (somenotnone (! (π2 x) · d2 n (de3 n dom2)))
      guts2 n dom2 | Inr x with ctxindirect Δ1 n
      guts2 n dom2 | Inr x₁ | Inl x = abort (somenotnone (! (π2 (de1 n x)) · x₁))
      guts2 n dom2 | Inr x₁ | Inr x = x

  -- if two sets share a domain with disjoint sets, then their union shares
  -- a domain with the union
  dom-union : {A B : Set} {Δ1 Δ2 : A ctx} {H1 H2 : B ctx} →
                                     H1 ## H2 →
                                     dom-eq Δ1 H1 →
                                     dom-eq Δ2 H2 →
                                     dom-eq (Δ1 ∪ Δ2) (H1 ∪ H2)
  dom-union {A} {B} {Δ1} {Δ2} {H1} {H2} disj (p1 , p2) (p3 , p4) = guts1 , guts2
    where
      guts1 : (n : Nat) →
                 Σ[ x ∈ A ] ((Δ1 ∪ Δ2) n == Some x) →
                 Σ[ y ∈ B ] ((H1 ∪ H2) n == Some y)
      guts1 n (x , eq) with ctxindirect Δ1 n
      guts1 n (x₁ , eq) | Inl x with p1 n x
      ... | q1 , q2 = q1 , x∈∪l H1 H2 n q1 q2
      guts1 n (x₁ , eq) | Inr x with p3 n (_ , lem-dom-union-apt1 {Δ1 = Δ1} {Δ2 = Δ2} x eq)
      ... | q1 , q2 =  q1 , x∈∪r H1 H2 n q1 q2 (##-comm disj)

      guts2 : (n : Nat) →
                 Σ[ y ∈ B ] ((H1 ∪ H2) n == Some y) →
                 Σ[ x ∈ A ] ((Δ1 ∪ Δ2) n == Some x)
      guts2 n (x , eq) with ctxindirect H1 n
      guts2 n (x₁ , eq) | Inl x with p2 n x
      ... | q1 , q2 = q1 , x∈∪l Δ1 Δ2 n q1 q2
      guts2 n (x₁ , eq) | Inr x with p4 n (_ , lem-dom-union-apt2 {Δ1 = H2} {Δ2 = H1} x (tr (λ qq → qq n == Some x₁) (∪comm H1 H2 disj) eq))
      ... | q1 , q2 = q1 , x∈∪r Δ1 Δ2 n q1 q2 (##-comm (dom-eq-disj disj (p1 , p2) (p3 , p4)))
