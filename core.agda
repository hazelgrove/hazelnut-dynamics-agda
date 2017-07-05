open import Nat
open import Prelude
open import contexts

module core where
  -- types
  data htyp : Set where
    b     : htyp
    ⦇⦈    : htyp
    _==>_ : htyp → htyp → htyp

  -- arrow type constructors bind very tightly
  infixr 25  _==>_

  -- expressions
  data hexp : Set where
    c       : hexp
    _·:_    : hexp → htyp → hexp
    X       : Nat → hexp
    ·λ      : Nat → hexp → hexp
    ·λ_[_]_ : Nat → htyp → hexp → hexp
    ⦇⦈[_]   : Nat → hexp
    ⦇_⦈[_]  : hexp → Nat → hexp
    _∘_     : hexp → hexp → hexp

  -- used to mark which dhexp holes have been evaluated
  data mark : Set where
    ✓ : mark
    ✗ : mark

  mutual
    subst : Set -- todo: no idea if this is right; mutual thing is weird
    subst = dhexp ctx

    -- expressions without ascriptions but with casts
    data dhexp : Set where
      c        : dhexp
      X        : Nat → dhexp
      ·λ_[_]_  : Nat → htyp → dhexp → dhexp
      ⦇⦈⟨_⟩    : (Nat × subst × mark) → dhexp
      ⦇_⦈⟨_⟩   : dhexp → (Nat × subst × mark) → dhexp
      _∘_      : dhexp → dhexp → dhexp
      <_>_     : htyp → dhexp → dhexp

  -- type consistency
  data _~_ : (t1 t2 : htyp) → Set where
    TCRefl  : {τ : htyp} → τ ~ τ
    TCHole1 : {τ : htyp} → τ ~ ⦇⦈
    TCHole2 : {τ : htyp} → ⦇⦈ ~ τ
    TCArr   : {τ1 τ2 τ1' τ2' : htyp} →
               τ1 ~ τ1' →
               τ2 ~ τ2' →
               τ1 ==> τ2 ~ τ1' ==> τ2'

  -- type inconsistency
  data _~̸_ : (τ1 τ2 : htyp) → Set where
    ICBaseArr1 : {τ1 τ2 : htyp} → b ~̸ τ1 ==> τ2
    ICBaseArr2 : {τ1 τ2 : htyp} → τ1 ==> τ2 ~̸ b
    ICArr1 : {τ1 τ2 τ3 τ4 : htyp} →
               τ1 ~̸ τ3 →
               τ1 ==> τ2 ~̸ τ3 ==> τ4
    ICArr2 : {τ1 τ2 τ3 τ4 : htyp} →
               τ2 ~̸ τ4 →
               τ1 ==> τ2 ~̸ τ3 ==> τ4

  --- matching for arrows, sums, and products
  data _▸arr_ : htyp → htyp → Set where
    MAHole : ⦇⦈ ▸arr ⦇⦈ ==> ⦇⦈
    MAArr  : {τ1 τ2 : htyp} → τ1 ==> τ2 ▸arr τ1 ==> τ2

  -- aliases for type and hole contexts
  tctx : Set
  tctx = htyp ctx

  hctx : Set
  hctx = (htyp ctx × htyp) ctx

  -- todo: this probably belongs in contexts, but need to abstract it.
  id : tctx → subst
  id ctx x with ctx x
  id ctx x | Some τ = Some (X x)
  id ctx x | None = None

  -- this is just fancy notation to match the paper
  _::[_]_ : Nat → tctx → htyp → (Nat × tctx × htyp)
  u ::[ Γ ] τ = u , Γ , τ

  -- bidirectional type checking judgements for hexp
  mutual
    -- synthesis
    data _⊢_=>_ : (Γ : tctx) (e : hexp) (τ : htyp) → Set where
      SConst  : {Γ : tctx} → Γ ⊢ c => b
      SAsc    : {Γ : tctx} {e : hexp} {τ : htyp} →
                 Γ ⊢ e <= τ →
                 Γ ⊢ (e ·: τ) => τ
      SVar    : {Γ : tctx} {τ : htyp} {n : Nat} →
                 (n , τ) ∈ Γ →
                 Γ ⊢ X n => τ
      SAp     : {Γ : tctx} {e1 e2 : hexp} {τ τ1 τ2 : htyp} →
                 Γ ⊢ e1 => τ1 →
                 τ1 ▸arr τ2 ==> τ →
                 Γ ⊢ e2 <= τ2 →
                 Γ ⊢ (e1 ∘ e2) => τ
      SEHole  : {Γ : tctx} {u : Nat} → Γ ⊢ ⦇⦈[ u ] => ⦇⦈     -- todo: uniqueness of n?
      SNEHole : {Γ : tctx} {e : hexp} {τ : htyp} {u : Nat} → -- todo: uniqueness of n?
                 Γ ⊢ e => τ →
                 Γ ⊢ ⦇ e ⦈[ u ] => ⦇⦈
      SLam    : {Γ : tctx} {e : hexp} {τ1 τ2 : htyp} {x : Nat} →
                 x # Γ →
                 (Γ ,, (x , τ1)) ⊢ e => τ2 →
                 Γ ⊢ ·λ x [ τ1 ] e => τ1 ==> τ2

    -- analysis
    data _⊢_<=_ : (Γ : htyp ctx) (e : hexp) (τ : htyp) → Set where
      ASubsume : {Γ : tctx} {e : hexp} {τ τ' : htyp} →
                 Γ ⊢ e => τ' →
                 τ ~ τ' →
                 Γ ⊢ e <= τ
      ALam : {Γ : tctx} {e : hexp} {τ τ1 τ2 : htyp} {x : Nat} →
                 x # Γ →
                 τ ▸arr τ1 ==> τ2 →
                 (Γ ,, (x , τ1)) ⊢ e <= τ2 →
                 Γ ⊢ (·λ x e) <= τ

  -- todo: do we care about completeness of hexp or e-umlauts?
  -- those types without holes anywhere
  tcomplete : htyp → Set
  tcomplete b         = ⊤
  tcomplete ⦇⦈        = ⊥
  tcomplete (τ1 ==> τ2) = tcomplete τ1 × tcomplete τ2

  -- those expressions without holes anywhere
  ecomplete : hexp → Set
  ecomplete c = ⊤
  ecomplete (e1 ·: τ)  = ecomplete e1 × tcomplete τ
  ecomplete (X _)      = ⊤
  ecomplete (·λ _ e1)  = ecomplete e1
  ecomplete ⦇⦈[ u ]       = ⊥
  ecomplete ⦇ e1 ⦈[ u ]   = ⊥
  ecomplete (e1 ∘ e2)  = ecomplete e1 × ecomplete e2
  ecomplete (·λ x [ τ ] e) = tcomplete τ × ecomplete e

  -- expansion
  mutual
    data _⊢_⇒_~>_⊣_ : (Γ : tctx) (e : hexp) (τ : htyp) (d : dhexp) (Δ : hctx) → Set where
      ESConst : ∀{Γ} → Γ ⊢ c ⇒ b ~> c ⊣ ∅
      ESVar   : ∀{Γ x τ} → (x , τ) ∈ Γ →
                         Γ ⊢ X x ⇒ τ ~> X x ⊣ ∅
      ESLam   : ∀{Γ x τ1 τ2 e d Δ } →
                     (x # Γ) → -- todo: i added this
                     (Γ ,, (x , τ1)) ⊢ e ⇒ τ2 ~> d ⊣ Δ →
                      Γ ⊢ ·λ x [ τ1 ] e ⇒ (τ1 ==> τ2) ~> ·λ x [ τ1 ] d ⊣ Δ
      ESAp1   : ∀{Γ e1 e2 d2 d1 Δ1 τ1 τ2 Δ2} →
                Δ1 ## Δ2 →
                Γ ⊢ e1 => ⦇⦈ →
                Γ ⊢ e1 ⇐ (τ2 ==> ⦇⦈) ~> d1 :: τ1 ⊣ Δ1 →
                Γ ⊢ e2 ⇐ ⦇⦈ ~> d2 :: τ2 ⊣ Δ2 →
                Γ ⊢ e1 ∘ e2 ⇒ ⦇⦈ ~> (< τ2 ==> ⦇⦈ > d1) ∘ d2 ⊣ (Δ1 ∪ Δ2)
      ESAp2 : ∀{Γ e1 τ2 τ d1 d2 Δ1 Δ2 τ2' e2} →
              Δ1 ## Δ2 →
              Γ ⊢ e1 ⇒ (τ2 ==> τ) ~> d1 ⊣ Δ1 →
              Γ ⊢ e2 ⇐ τ2 ~> d2 :: τ2' ⊣ Δ2 →
              (τ2 == τ2' → ⊥) →
              Γ ⊢ e1 ∘ e2 ⇒ τ ~> d1 ∘ (< τ2 > d2) ⊣ (Δ1 ∪ Δ2)
      ESAp3 : ∀{Γ e1 τ d1 Δ1 e2 τ2 d2 Δ2 } →
              Δ1 ## Δ2 →
              Γ ⊢ e1 ⇒ (τ2 ==> τ) ~> d1 ⊣ Δ1 →
              Γ ⊢ e2 ⇐ τ2 ~> d2 :: τ2 ⊣ Δ2 →
              Γ ⊢ e1 ∘ e2 ⇒ τ ~> d1 ∘ d2 ⊣ (Δ1 ∪ Δ2)
      ESEHole : ∀{ Γ u } →
                Γ ⊢ ⦇⦈[ u ] ⇒ ⦇⦈ ~> ⦇⦈⟨ u , id Γ , ✗ ⟩ ⊣  ■ (u ::[ Γ ] ⦇⦈)
      ESNEHole : ∀{ Γ e τ d u Δ } →
                 Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                 Γ ⊢ ⦇ e ⦈[ u ] ⇒ ⦇⦈ ~> ⦇ d ⦈⟨ u , id Γ , ✗ ⟩ ⊣ (Δ ,, u ::[ Γ ] ⦇⦈)
      ESAsc1 : ∀ {Γ e τ d τ' Δ} →
                 Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                 (τ == τ' → ⊥) →
                 Γ ⊢ (e ·: τ) ⇒ τ ~> (< τ > d) ⊣ Δ
      ESAsc2 : ∀{Γ e τ d τ' Δ } →
               Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
               Γ ⊢ (e ·: τ) ⇒ τ ~> d ⊣ Δ

    data _⊢_⇐_~>_::_⊣_ : (Γ : tctx) (e : hexp) (τ : htyp) (d : dhexp) (τ' : htyp) (Δ : hctx) → Set where
      EALam : ∀{Γ x τ1 τ2 e d τ2' Δ } →
              (x # Γ) →
              (Γ ,, (x , τ1)) ⊢ e ⇐ τ2 ~> d :: τ2' ⊣ Δ →
              Γ ⊢ ·λ x e ⇐ τ1 ==> τ2 ~> ·λ x [ τ1 ] d :: τ1 ==> τ2' ⊣ Δ
      EALamHole : ∀{Γ x e τ d Δ } →
              (x # Γ) →
              (Γ ,, (x , ⦇⦈)) ⊢ e ⇐ ⦇⦈ ~> d :: τ ⊣ Δ  →
              Γ ⊢ ·λ x e ⇐ ⦇⦈ ~> ·λ x [ ⦇⦈ ] d :: ⦇⦈ ==> τ ⊣ Δ
      EASubsume : ∀{e Γ τ' d Δ τ} →
                  ((u : Nat) → (e == ⦇⦈[ u ] → ⊥)) →
                  ((e' : hexp) (u : Nat) → (e == ⦇ e' ⦈[ u ] → ⊥)) →
                  Γ ⊢ e ⇒ τ' ~> d ⊣ Δ →
                  τ ~ τ' →
                  Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ
      EAEHole : ∀{ Γ u τ  } →
                Γ ⊢ ⦇⦈[ u ] ⇐ τ ~> ⦇⦈⟨ u , id Γ , ✗ ⟩ :: τ ⊣ ■ (u ::[ Γ ] τ)
      EANEHole : ∀{ Γ e u τ d τ' Δ  } →
                 Γ ⊢ e ⇒ τ' ~> d ⊣ Δ →
                 Γ ⊢ ⦇ e ⦈[ u ] ⇐ τ ~> ⦇ d ⦈⟨ u , id Γ , ✗ ⟩ :: τ ⊣ (Δ ,, u ::[ Γ ] τ)

  mutual
    -- substitition type assignment
    _,_⊢_:s:_ : hctx → tctx → subst → tctx → Set
    Δ , Γ ⊢ σ :s: Γ' =
        (x : Nat) (d : dhexp) →
          (x , d) ∈ σ →
          Σ[ τ ∈ htyp ] (Γ' x == Some τ × Δ , Γ ⊢ d :: τ)

    -- type assignment
    data _,_⊢_::_ : (Δ : hctx) (Γ : tctx) (d : dhexp) (τ : htyp) → Set where
      TAConst : ∀{Δ Γ} → Δ , Γ ⊢ c :: b
      TAVar : ∀{Δ Γ x τ} → (x , τ) ∈ Γ → Δ , Γ ⊢ X x :: τ
      TALam : ∀{ Δ Γ x τ1 d τ2} →
              Δ , (Γ ,, (x , τ1)) ⊢ d :: τ2 →
              Δ , Γ ⊢ ·λ x [ τ1 ] d :: (τ1 ==> τ2)
      TAAp : ∀{ Δ Γ d1 d2 τ1 τ2 τ} →
             Δ , Γ ⊢ d1 :: τ1 →
             τ1 ▸arr (τ2 ==> τ) →
             Δ , Γ ⊢ d2 :: τ2 →
             Δ , Γ ⊢ d1 ∘ d2 :: τ
      TAEHole : ∀{ Δ Γ σ u Γ' τ m} →
                Δ , Γ ⊢ σ :s: Γ' →
                (Δ ,, u ::[ Γ' ] τ) , Γ ⊢ ⦇⦈⟨ u , σ , m ⟩ :: τ
      TANEHole : ∀ { Δ Γ d τ' Γ' u σ τ m} →
                 Δ , Γ ⊢ d :: τ' →
                 Δ , Γ ⊢ σ :s: Γ' →
                 (Δ ,, u ::[ Γ' ] τ) , Γ ⊢ ⦇ d ⦈⟨ u , σ , m ⟩ :: τ
      TACast : ∀{ Δ Γ d τ τ'} →
             Δ , Γ ⊢ d :: τ' →
             τ ~ τ' →
             Δ , Γ ⊢ < τ > d :: τ

  postulate -- todo: write this later
    [_]_ : subst → dhexp → dhexp

  -- value
  data _val : (d : dhexp) → Set where
    VConst : c val
    VLam   : ∀{x τ d} → (·λ x [ τ ] d) val

  mutual
    -- indeterminate
    data _indet : (d : dhexp) → Set where
      IEHole : ∀{u σ} → ⦇⦈⟨ u , σ ⟩ indet
      INEHole : ∀{d u σ} → d final → ⦇ d ⦈⟨ u , σ ⟩ indet
      IAp : ∀{d1 d2} → d1 indet → d2 final → (d1 ∘ d2) indet
      ICast : ∀{d τ} → d indet → (< τ > d) indet

    -- final
    data _final : (d : dhexp) → Set where
      FVal : ∀{d} → d val → d final
      FIndet : ∀{d} → d indet → d final

------------- these two judgements are still being figured out; form
------------- changing, etc. double check everything here once it settles
------------- before doing anything with it
  -- error
  data _err[_] : (d : dhexp) → (Δ : hctx) → Set where
    -- ERNEHole
    -- ERCastError
    -- ERLam
    -- ERAp1
    -- ERAp2
    -- ERCast

  -- small step semantics
  data _↦_ : (d d' : dhexp)  → Set where
    STHole : ∀{ d d' u σ } →
             d ↦ d' →
             ⦇ d ⦈⟨ u , σ ⟩ ↦  ⦇ d' ⦈⟨ u , σ ⟩
    -- STCast
    STAp1 : ∀{ d1 d2 d1' } →
            d1 ↦ d1' →
            (d1 ∘ d2) ↦ (d1' ∘ d2)
    STAp2 : ∀{ d1 d2 d2' } →
            d1 final →
            d2 ↦ d2' →
            (d1 ∘ d2) ↦ (d1 ∘ d2')
    -- STApβ : ∀{ d1 d2 τ x } →
    --         d2 final →
    --         ((·λ x [ τ ] d1) ∘ d2) ↦ ([ ⟦ x , {!!} ⟧ ] d2)
