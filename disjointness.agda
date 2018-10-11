open import Prelude
open import Nat
open import core
open import contexts
open import lemmas-disjointness
open import exchange
open import lemmas-freshness
open import weakening

module disjointness where
  mutual
    expand-new-disjoint-synth : ∀ { e u τ d Δ Γ Γ' τ'} →
                          hole-name-new e u →
                          Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                          Δ ## (■ (u , Γ' , τ'))
    expand-new-disjoint-synth HNConst ESConst = empty-disj (■ (_ , _ , _))
    expand-new-disjoint-synth (HNAsc hn) (ESAsc x) = expand-new-disjoint-ana hn x
    expand-new-disjoint-synth HNVar (ESVar x₁) = empty-disj (■ (_ , _ , _))
    expand-new-disjoint-synth (HNLam1 hn) ()
    expand-new-disjoint-synth (HNLam2 hn) (ESLam x₁ exp) = expand-new-disjoint-synth hn exp
    expand-new-disjoint-synth (HNHole x) ESEHole = disjoint-singles x
    expand-new-disjoint-synth (HNNEHole x hn) (ESNEHole x₁ exp) = disjoint-parts (expand-new-disjoint-synth hn exp) (disjoint-singles x)
    expand-new-disjoint-synth (HNAp hn hn₁) (ESAp x x₁ x₂ x₃ x₄ x₅) =
                                            disjoint-parts (expand-new-disjoint-ana hn x₄)
                                                  (expand-new-disjoint-ana hn₁ x₅)

    expand-new-disjoint-ana : ∀ { e u τ d Δ Γ Γ' τ' τ2} →
                              hole-name-new e u →
                              Γ ⊢ e ⇐ τ ~> d :: τ2 ⊣ Δ →
                              Δ ## (■ (u , Γ' , τ'))
    expand-new-disjoint-ana hn (EASubsume x x₁ x₂ x₃) = expand-new-disjoint-synth hn x₂
    expand-new-disjoint-ana (HNLam1 hn) (EALam x₁ x₂ ex) = expand-new-disjoint-ana hn ex
    expand-new-disjoint-ana (HNHole x) EAEHole = disjoint-singles x
    expand-new-disjoint-ana (HNNEHole x hn) (EANEHole x₁ x₂) = disjoint-parts (expand-new-disjoint-synth hn x₂) (disjoint-singles x)

  mutual
    expand-disjoint-new-synth : ∀{ e τ d Δ u Γ Γ' τ'} →
                                Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                                Δ ## (■ (u , Γ' , τ')) →
                                hole-name-new e u
    expand-disjoint-new-synth ESConst disj = HNConst
    expand-disjoint-new-synth (ESVar x₁) disj = HNVar
    expand-disjoint-new-synth (ESLam x₁ ex) disj = HNLam2 (expand-disjoint-new-synth ex disj)
    expand-disjoint-new-synth (ESAp {Δ1 = Δ1} x x₁ x₂ x₃ x₄ x₅) disj
      with expand-disjoint-new-ana x₄ (disjoint-union1 disj) | expand-disjoint-new-ana x₅ (disjoint-union2 {Γ1 = Δ1} disj)
    ... | ih1 | ih2 = HNAp ih1 ih2
    expand-disjoint-new-synth {Γ = Γ} ESEHole disj = HNHole (singles-notequal disj)
    expand-disjoint-new-synth (ESNEHole {Δ = Δ} x ex) disj = HNNEHole (singles-notequal (disjoint-union2 {Γ1 = Δ} disj))
                                                                      (expand-disjoint-new-synth ex (disjoint-union1 disj))
    expand-disjoint-new-synth (ESAsc x) disj = HNAsc (expand-disjoint-new-ana x disj)

    expand-disjoint-new-ana : ∀{ e τ d Δ u Γ Γ' τ2 τ'} →
                                Γ ⊢ e ⇐ τ ~> d :: τ2 ⊣ Δ →
                                Δ ## (■ (u , Γ' , τ')) →
                                hole-name-new e u
    expand-disjoint-new-ana (EALam x₁ x₂ ex) disj = HNLam1 (expand-disjoint-new-ana ex disj)
    expand-disjoint-new-ana (EASubsume x x₁ x₂ x₃) disj = expand-disjoint-new-synth x₂ disj
    expand-disjoint-new-ana EAEHole disj = HNHole (singles-notequal disj)
    expand-disjoint-new-ana (EANEHole {Δ = Δ} x x₁) disj = HNNEHole (singles-notequal (disjoint-union2 {Γ1 = Δ} disj))
                                                                    (expand-disjoint-new-synth x₁ (disjoint-union1 disj))

  -- collect up the hole names of a term as the indices of a trivial contex
  data holes : (e : hexp) (H : ⊤ ctx) → Set where
    HConst : holes c ∅
    HAsc   : ∀{e τ H} → holes e H → holes (e ·: τ) H
    HVar   : ∀{x} → holes (X x) ∅
    HLam1  : ∀{x e H} → holes e H → holes (·λ x e) H
    HLam2  : ∀{x e τ H} → holes e H → holes (·λ x [ τ ] e) H
    HEHole : ∀{u} → holes (⦇⦈[ u ]) (■ (u , <>))
    HNEHole : ∀{e u H} → holes e H → holes (⦇ e ⦈[ u ]) (H ,, (u , <>))
    HAp : ∀{e1 e2 H1 H2} → holes e1 H1 → holes e2 H2 → holes (e1 ∘ e2) (H1 ∪ H2)

  -- the above judgement has mode (∀,∃). this doesn't prove uniqueness; any
  -- contex that extends the one computed here will be indistinguishable
  -- but we'll treat this one as canonical
  find-holes : (e : hexp) → Σ[ H ∈ ⊤ ctx ](holes e H)
  find-holes c = ∅ , HConst
  find-holes (e ·: x) with find-holes e
  ... | (h , d)= h , (HAsc d)
  find-holes (X x) = ∅ , HVar
  find-holes (·λ x e) with find-holes e
  ... | (h , d) = h , HLam1 d
  find-holes (·λ x [ x₁ ] e) with find-holes e
  ... | (h , d) = h , HLam2 d
  find-holes ⦇⦈[ x ] = (■ (x , <>)) , HEHole
  find-holes ⦇ e ⦈[ x ] with find-holes e
  ... | (h , d) = h ,, (x , <>) , HNEHole d
  find-holes (e1 ∘ e2) with find-holes e1 | find-holes e2
  ... | (h1 , d1) | (h2 , d2)  = (h1 ∪ h2 ) , (HAp d1 d2)

  -- two contexts that may contain different mappings have the same domain
  dom-eq : {A B : Set} → A ctx → B ctx → Set
  dom-eq {A} {B} C1 C2 = ((n : Nat) → Σ[ x ∈ A ]( C1 n == Some x) → (Σ[ y ∈ B ](C2 n == Some y)))×
                         ((n : Nat) → Σ[ y ∈ B ]( C2 n == Some y) → (Σ[ x ∈ A ](C1 n == Some x)))

  -- the empty context has the same domain as itself
  dom-∅ : {A B : Set} → dom-eq (λ _ → None {A}) (λ _ → None {B})
  dom-∅ {A} {B} = (λ n x → abort (somenotnone (! (π2 x)))) , (λ n x → abort (somenotnone (! (π2 x))))

  -- todo: this seems like i would have proven it already? otw move to lemmas
  singleton-eq : {A : Set} {a : A} → ∀{x n y} → (■ (x , a)) n == Some y → x == n
  singleton-eq {A} {a} {x} {n} {y} eq with natEQ x n
  singleton-eq eq | Inl x₁ = x₁
  singleton-eq eq | Inr x₁ = abort (somenotnone (! eq))

  -- todo: this seems like i would have proven it already? otw move to lemmas
  singleton-lookup-refl : {A : Set} {n : Nat} {β : A} → (■ (n , β)) n == Some β
  singleton-lookup-refl {n = n} with natEQ n n
  singleton-lookup-refl | Inl refl = λ {β} → refl
  singleton-lookup-refl | Inr x = abort (x refl)

  -- the singleton contexts formed with any contents but the same index has
  -- the same domain
  dom-single : {A B : Set} (x : Nat) (a : A) (b : B) → dom-eq (■ (x , a)) (■ (x , b))
  dom-single {A} {B} x α β = (λ n x₁ → β , (ap1 (λ qq → (■ (qq , β)) n) (singleton-eq (π2 x₁)) · singleton-lookup-refl)) ,
                             (λ n x₁ → α , (ap1 (λ qq → (■ (qq , α)) n) (singleton-eq (π2 x₁)) · singleton-lookup-refl))

  -- todo: this seems like i would have proven it already? otw move to lemmas
  lem-dom-union-apt1 : {A : Set} {Δ1 Δ2 : A ctx} {x : Nat} {y : A} → x # Δ1 → ((Δ1 ∪ Δ2) x == Some y) → (Δ2 x == Some y)
  lem-dom-union-apt1 {A} {Δ1} {Δ2} {x} {y} apt xin with Δ1 x
  lem-dom-union-apt1 apt xin | Some x₁ = abort (somenotnone apt)
  lem-dom-union-apt1 apt xin | None = xin

  -- todo: this seems like i would have proven it already? otw move to lemmas
  lem-dom-union-apt2 : {A : Set} {Δ1 Δ2 : A ctx} {x : Nat} {y : A} → x # Δ2 → ((Δ1 ∪ Δ2) x == Some y) → (Δ1 x == Some y)
  lem-dom-union-apt2 {A} {Δ1} {Δ2} {x} {y} apt xin with Δ1 x
  lem-dom-union-apt2 apt xin | Some x₁ = xin
  lem-dom-union-apt2 apt xin | None = abort (somenotnone (! xin · apt))

  -- if two disjoint sets each share a domain with two other sets, those
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

  -- if a hole name is new then it's apart from the collection of hole
  -- names
  lem-apart-new : ∀{e H u} → holes e H → hole-name-new e u → u # H
  lem-apart-new HConst HNConst = refl
  lem-apart-new (HAsc h) (HNAsc hn) = lem-apart-new h hn
  lem-apart-new HVar HNVar = refl
  lem-apart-new (HLam1 h) (HNLam1 hn) = lem-apart-new h hn
  lem-apart-new (HLam2 h) (HNLam2 hn) = lem-apart-new h hn
  lem-apart-new HEHole (HNHole x) = apart-singleton (flip x)
  lem-apart-new (HNEHole {u = u'} {H = H} h) (HNNEHole  {u = u}  x hn) = apart-parts H (■ (u' , <>)) u (lem-apart-new h hn) (apart-singleton (flip x))
  lem-apart-new (HAp {H1 = H1} {H2 = H2} h h₁) (HNAp hn hn₁) = apart-parts H1 H2 _ (lem-apart-new h hn) (lem-apart-new h₁ hn₁)

  -- todo: this seems like i would have proven it already? otw move to lemmas
  lem-dom-apt : {A : Set} {G : A ctx} {x y : Nat} → x # G → dom G y → x ≠ y
  lem-dom-apt {x = x} {y = y} apt dom with natEQ x y
  lem-dom-apt apt dom | Inl refl = abort (somenotnone (! (π2 dom) · apt))
  lem-dom-apt apt dom | Inr x₁ = x₁

  -- if the holes of two expressions are disjoint, so are their collections
  -- of hole names
  holes-disjoint-disjoint : ∀{ e1 e2 H1 H2} →
                    holes e1 H1 →
                    holes e2 H2 →
                    holes-disjoint e1 e2 →
                    H1 ## H2
  holes-disjoint-disjoint HConst he2 HDConst = empty-disj _
  holes-disjoint-disjoint (HAsc he1) he2 (HDAsc hd) = holes-disjoint-disjoint he1 he2 hd
  holes-disjoint-disjoint HVar he2 HDVar = empty-disj _
  holes-disjoint-disjoint (HLam1 he1) he2 (HDLam1 hd) = holes-disjoint-disjoint he1 he2 hd
  holes-disjoint-disjoint (HLam2 he1) he2 (HDLam2 hd) = holes-disjoint-disjoint he1 he2 hd
  holes-disjoint-disjoint HEHole he2 (HDHole x) = lem-apart-sing-disj (lem-apart-new he2 x)
  holes-disjoint-disjoint (HNEHole he1) he2 (HDNEHole x hd) = disjoint-parts (holes-disjoint-disjoint he1 he2 hd) (lem-apart-sing-disj (lem-apart-new he2 x))
  holes-disjoint-disjoint (HAp he1 he2) he3 (HDAp hd hd₁) = disjoint-parts (holes-disjoint-disjoint he1 he3 hd) (holes-disjoint-disjoint he2 he3 hd₁)

  -- the holes of an expression have the same domain as Δ; that is, we
  -- don't add any extra junk as we expand
  mutual
    holes-delta-ana : ∀{Γ H e τ d τ' Δ} →
                    holes e H →
                    Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                    dom-eq Δ H
    holes-delta-ana (HLam1 h) (EALam x₁ x₂ exp) = holes-delta-ana h exp
    holes-delta-ana h (EASubsume x x₁ x₂ x₃) = holes-delta-synth h x₂
    holes-delta-ana (HEHole {u = u}) EAEHole = dom-single u _ _
    holes-delta-ana (HNEHole {u = u} h) (EANEHole x x₁) with (holes-delta-synth h x₁)
    ... | ih = dom-union {!!} ih (dom-single u _ _ )

    holes-delta-synth : ∀{Γ H e τ d Δ} →
                    holes e H →
                    Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                    dom-eq Δ H
    holes-delta-synth HConst ESConst = dom-∅
    holes-delta-synth (HAsc h) (ESAsc x) = holes-delta-ana h x
    holes-delta-synth HVar (ESVar x₁) = dom-∅
    holes-delta-synth (HLam2 h) (ESLam x₁ exp) = holes-delta-synth h exp
    holes-delta-synth (HEHole {u = u}) ESEHole = dom-single u _ _
    holes-delta-synth (HNEHole {u = u} h) (ESNEHole x exp) = dom-union {!!} (holes-delta-synth h exp) (dom-single u _ _)
    holes-delta-synth (HAp h h₁) (ESAp x x₁ x₂ x₃ x₄ x₅) = dom-union (holes-disjoint-disjoint h h₁ x) (holes-delta-ana h x₄) (holes-delta-ana h₁ x₅)

  -- if you expand two hole-disjoint expressions analytically, the Δs
  -- produces are disjoint. note that this is likely true for synthetic
  -- expansions in much the same way, but we only prove "half" of the usual
  -- pair here. the proof technique is *not* structurally inductive on the
  -- expansion judgement, because of the missing weakness property, so this
  -- proof is somewhat unusual compared to the rest in this development.
  expand-ana-disjoint : ∀{ e1 e2 τ1 τ2 e1' e2' τ1' τ2' Γ Δ1 Δ2 } →
          holes-disjoint e1 e2 →
          Γ ⊢ e1 ⇐ τ1 ~> e1' :: τ1' ⊣ Δ1 →
          Γ ⊢ e2 ⇐ τ2 ~> e2' :: τ2' ⊣ Δ2 →
          Δ1 ## Δ2
  expand-ana-disjoint {e1} {e2} hd ana1 ana2
    with find-holes e1 | find-holes e2
  ... | (_ , he1) | (_ , he2) = dom-eq-disj (holes-disjoint-disjoint he1 he2 hd)
                                            (holes-delta-ana he1 ana1)
                                            (holes-delta-ana he2 ana2)


  -- these lemmas are all structurally recursive and quite
  -- mechanical. morally, they establish the properties about reduction
  -- that would be obvious / baked into Agda if holes-disjoint was defined
  -- as a function rather than a judgement (datatype), or if we had defined
  -- all the O(n^2) cases rather than relying on a little indirection to
  -- only have O(n) cases. that work has to go somewhwere, and we prefer
  -- that it goes here.
  ds-lem-asc : ∀{e1 e2 τ} → holes-disjoint e2 e1 → holes-disjoint e2 (e1 ·: τ)
  ds-lem-asc HDConst = HDConst
  ds-lem-asc (HDAsc hd) = HDAsc (ds-lem-asc hd)
  ds-lem-asc HDVar = HDVar
  ds-lem-asc (HDLam1 hd) = HDLam1 (ds-lem-asc hd)
  ds-lem-asc (HDLam2 hd) = HDLam2 (ds-lem-asc hd)
  ds-lem-asc (HDHole x) = HDHole (HNAsc x)
  ds-lem-asc (HDNEHole x hd) = HDNEHole (HNAsc x) (ds-lem-asc hd)
  ds-lem-asc (HDAp hd hd₁) = HDAp (ds-lem-asc hd) (ds-lem-asc hd₁)

  ds-lem-lam1 : ∀{e1 e2 x} → holes-disjoint e2 e1 → holes-disjoint e2 (·λ x e1)
  ds-lem-lam1 HDConst = HDConst
  ds-lem-lam1 (HDAsc hd) = HDAsc (ds-lem-lam1 hd)
  ds-lem-lam1 HDVar = HDVar
  ds-lem-lam1 (HDLam1 hd) = HDLam1 (ds-lem-lam1 hd)
  ds-lem-lam1 (HDLam2 hd) = HDLam2 (ds-lem-lam1 hd)
  ds-lem-lam1 (HDHole x₁) = HDHole (HNLam1 x₁)
  ds-lem-lam1 (HDNEHole x₁ hd) = HDNEHole (HNLam1 x₁) (ds-lem-lam1 hd)
  ds-lem-lam1 (HDAp hd hd₁) = HDAp (ds-lem-lam1 hd) (ds-lem-lam1 hd₁)

  ds-lem-lam2 : ∀{e1 e2 x τ} → holes-disjoint e2 e1 → holes-disjoint e2 (·λ x [ τ ] e1)
  ds-lem-lam2 HDConst = HDConst
  ds-lem-lam2 (HDAsc hd) = HDAsc (ds-lem-lam2 hd)
  ds-lem-lam2 HDVar = HDVar
  ds-lem-lam2 (HDLam1 hd) = HDLam1 (ds-lem-lam2 hd)
  ds-lem-lam2 (HDLam2 hd) = HDLam2 (ds-lem-lam2 hd)
  ds-lem-lam2 (HDHole x₁) = HDHole (HNLam2 x₁)
  ds-lem-lam2 (HDNEHole x₁ hd) = HDNEHole (HNLam2 x₁) (ds-lem-lam2 hd)
  ds-lem-lam2 (HDAp hd hd₁) = HDAp (ds-lem-lam2 hd) (ds-lem-lam2 hd₁)

  ds-lem-nehole : ∀{e e1 u} → holes-disjoint e e1 → hole-name-new e u → holes-disjoint e ⦇ e1 ⦈[ u ]
  ds-lem-nehole HDConst ν = HDConst
  ds-lem-nehole (HDAsc hd) (HNAsc ν) = HDAsc (ds-lem-nehole hd ν)
  ds-lem-nehole HDVar ν = HDVar
  ds-lem-nehole (HDLam1 hd) (HNLam1 ν) = HDLam1 (ds-lem-nehole hd ν)
  ds-lem-nehole (HDLam2 hd) (HNLam2 ν) = HDLam2 (ds-lem-nehole hd ν)
  ds-lem-nehole (HDHole x) (HNHole x₁) = HDHole (HNNEHole (flip x₁) x)
  ds-lem-nehole (HDNEHole x hd) (HNNEHole x₁ ν) = HDNEHole (HNNEHole (flip x₁) x) (ds-lem-nehole hd ν)
  ds-lem-nehole (HDAp hd hd₁) (HNAp ν ν₁) = HDAp (ds-lem-nehole hd ν) (ds-lem-nehole hd₁ ν₁)

  ds-lem-ap : ∀{e1 e2 e3} → holes-disjoint e3 e1 → holes-disjoint e3 e2 → holes-disjoint e3 (e1 ∘ e2)
  ds-lem-ap HDConst hd2 = HDConst
  ds-lem-ap (HDAsc hd1) (HDAsc hd2) = HDAsc (ds-lem-ap hd1 hd2)
  ds-lem-ap HDVar hd2 = HDVar
  ds-lem-ap (HDLam1 hd1) (HDLam1 hd2) = HDLam1 (ds-lem-ap hd1 hd2)
  ds-lem-ap (HDLam2 hd1) (HDLam2 hd2) = HDLam2 (ds-lem-ap hd1 hd2)
  ds-lem-ap (HDHole x) (HDHole x₁) = HDHole (HNAp x x₁)
  ds-lem-ap (HDNEHole x hd1) (HDNEHole x₁ hd2) = HDNEHole (HNAp x x₁) (ds-lem-ap hd1 hd2)
  ds-lem-ap (HDAp hd1 hd2) (HDAp hd3 hd4) = HDAp (ds-lem-ap hd1 hd3) (ds-lem-ap hd2 hd4)

  -- holes-disjoint is symmetric
  disjoint-sym : (e1 e2 : hexp) → holes-disjoint e1 e2 → holes-disjoint e2 e1
  disjoint-sym .c c HDConst = HDConst
  disjoint-sym .c (e2 ·: x) HDConst = HDAsc (disjoint-sym _ _ HDConst)
  disjoint-sym .c (X x) HDConst = HDVar
  disjoint-sym .c (·λ x e2) HDConst = HDLam1 (disjoint-sym c e2 HDConst)
  disjoint-sym .c (·λ x [ x₁ ] e2) HDConst = HDLam2 (disjoint-sym c e2 HDConst)
  disjoint-sym .c ⦇⦈[ x ] HDConst = HDHole HNConst
  disjoint-sym .c ⦇ e2 ⦈[ x ] HDConst = HDNEHole HNConst (disjoint-sym c e2 HDConst)
  disjoint-sym .c (e2 ∘ e3) HDConst = HDAp (disjoint-sym c e2 HDConst) (disjoint-sym c e3 HDConst)

  disjoint-sym _ c (HDAsc hd) = HDConst
  disjoint-sym _ (e2 ·: x) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ·: x) (HDAsc hd) | HDAsc ih = HDAsc (ds-lem-asc ih)
  disjoint-sym _ (X x) (HDAsc hd) = HDVar
  disjoint-sym _ (·λ x e2) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x e2) (HDAsc hd) | HDLam1 ih = HDLam1 (ds-lem-asc ih)
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDAsc hd) | HDLam2 ih = HDLam2 (ds-lem-asc ih)
  disjoint-sym _ ⦇⦈[ x ] (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⦈[ x ] (HDAsc hd) | HDHole x₁ = HDHole (HNAsc x₁)
  disjoint-sym _ ⦇ e2 ⦈[ x ] (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇ e2 ⦈[ x ] (HDAsc hd) | HDNEHole x₁ ih = HDNEHole (HNAsc x₁) (ds-lem-asc ih)
  disjoint-sym _ (e2 ∘ e3) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ∘ e3) (HDAsc hd) | HDAp ih ih₁ = HDAp (ds-lem-asc ih) (ds-lem-asc ih₁)

  disjoint-sym _ c HDVar = HDConst
  disjoint-sym _ (e2 ·: x₁) HDVar = HDAsc (disjoint-sym _ e2 HDVar)
  disjoint-sym _ (X x₁) HDVar = HDVar
  disjoint-sym _ (·λ x₁ e2) HDVar = HDLam1 (disjoint-sym _ e2 HDVar)
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) HDVar = HDLam2 (disjoint-sym _ e2 HDVar)
  disjoint-sym _ ⦇⦈[ x₁ ] HDVar = HDHole HNVar
  disjoint-sym _ ⦇ e2 ⦈[ x₁ ] HDVar = HDNEHole HNVar (disjoint-sym _ e2 HDVar)
  disjoint-sym _ (e2 ∘ e3) HDVar = HDAp (disjoint-sym _ e2 HDVar) (disjoint-sym _ e3 HDVar)

  disjoint-sym _ c (HDLam1 hd) = HDConst
  disjoint-sym _ (e2 ·: x₁) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ·: x₁) (HDLam1 hd) | HDAsc ih = HDAsc (ds-lem-lam1 ih)
  disjoint-sym _ (X x₁) (HDLam1 hd) = HDVar
  disjoint-sym _ (·λ x₁ e2) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x₁ e2) (HDLam1 hd) | HDLam1 ih = HDLam1 (ds-lem-lam1 ih)
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) (HDLam1 hd) | HDLam2 ih = HDLam2 (ds-lem-lam1 ih)
  disjoint-sym _ ⦇⦈[ x₁ ] (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⦈[ x₁ ] (HDLam1 hd) | HDHole x = HDHole (HNLam1 x)
  disjoint-sym _ ⦇ e2 ⦈[ x₁ ] (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇ e2 ⦈[ x₁ ] (HDLam1 hd) | HDNEHole x ih = HDNEHole (HNLam1 x) (ds-lem-lam1 ih)
  disjoint-sym _ (e2 ∘ e3) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ∘ e3) (HDLam1 hd) | HDAp ih ih₁ = HDAp (ds-lem-lam1 ih) (ds-lem-lam1 ih₁)

  disjoint-sym _ c (HDLam2 hd) = HDConst
  disjoint-sym _ (e2 ·: x₁) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ·: x₁) (HDLam2 hd) | HDAsc ih = HDAsc (ds-lem-lam2 ih)
  disjoint-sym _ (X x₁) (HDLam2 hd) = HDVar
  disjoint-sym _ (·λ x₁ e2) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x₁ e2) (HDLam2 hd) | HDLam1 ih = HDLam1 (ds-lem-lam2 ih)
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) (HDLam2 hd) | HDLam2 ih = HDLam2 (ds-lem-lam2 ih)
  disjoint-sym _ ⦇⦈[ x₁ ] (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⦈[ x₁ ] (HDLam2 hd) | HDHole x = HDHole (HNLam2 x)
  disjoint-sym _ ⦇ e2 ⦈[ x₁ ] (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇ e2 ⦈[ x₁ ] (HDLam2 hd) | HDNEHole x ih = HDNEHole (HNLam2 x) (ds-lem-lam2 ih)
  disjoint-sym _ (e2 ∘ e3) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ∘ e3) (HDLam2 hd) | HDAp ih ih₁ = HDAp (ds-lem-lam2 ih) (ds-lem-lam2 ih₁)

  disjoint-sym _ c (HDHole x) = HDConst
  disjoint-sym _ (e2 ·: x) (HDHole (HNAsc x₁)) = HDAsc (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x₁))
  disjoint-sym _ (X x) (HDHole x₁) = HDVar
  disjoint-sym _ (·λ x e2) (HDHole (HNLam1 x₁)) = HDLam1 (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x₁))
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDHole (HNLam2 x₂)) = HDLam2 (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x₂))
  disjoint-sym _ ⦇⦈[ x ] (HDHole (HNHole x₁)) =  HDHole (HNHole (flip x₁))
  disjoint-sym _ ⦇ e2 ⦈[ u' ] (HDHole (HNNEHole x x₁)) = HDNEHole (HNHole (flip x)) (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x₁))
  disjoint-sym _ (e2 ∘ e3) (HDHole (HNAp x x₁)) = HDAp (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x))
                                                    (disjoint-sym ⦇⦈[ _ ] e3 (HDHole x₁))

  disjoint-sym _ c (HDNEHole x hd) = HDConst
  disjoint-sym _ (e2 ·: x) (HDNEHole x₁ hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e ·: x) (HDNEHole (HNAsc x₁) hd) | HDAsc ih = HDAsc (ds-lem-nehole ih x₁)
  disjoint-sym _ (X x) (HDNEHole x₁ hd) = HDVar
  disjoint-sym _ (·λ x e2) (HDNEHole x₁ hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x e2) (HDNEHole (HNLam1 x₁) hd) | HDLam1 ih = HDLam1 (ds-lem-nehole ih x₁)
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDNEHole x₂ hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDNEHole (HNLam2 x₂) hd) | HDLam2 ih = HDLam2 (ds-lem-nehole ih x₂)
  disjoint-sym _ ⦇⦈[ x ] (HDNEHole x₁ hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⦈[ x ] (HDNEHole (HNHole x₂) hd) | HDHole x₁ = HDHole (HNNEHole (flip x₂) x₁)
  disjoint-sym _ ⦇ e2 ⦈[ x ] (HDNEHole x₁ hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇ e2 ⦈[ x ] (HDNEHole (HNNEHole x₂ x₃) hd) | HDNEHole x₁ ih = HDNEHole (HNNEHole (flip x₂) x₁) (ds-lem-nehole ih x₃)
  disjoint-sym _ (e2 ∘ e3) (HDNEHole x hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e1 ∘ e3) (HDNEHole (HNAp x x₁) hd) | HDAp ih ih₁ = HDAp (ds-lem-nehole ih x) (ds-lem-nehole ih₁ x₁)

  disjoint-sym _ c (HDAp hd hd₁) = HDConst
  disjoint-sym _ (e3 ·: x) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (e3 ·: x) (HDAp hd hd₁) | HDAsc ih | HDAsc ih1 = HDAsc (ds-lem-ap ih ih1)
  disjoint-sym _ (X x) (HDAp hd hd₁) = HDVar
  disjoint-sym _ (·λ x e3) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (·λ x e3) (HDAp hd hd₁) | HDLam1 ih | HDLam1 ih1 = HDLam1 (ds-lem-ap ih ih1)
  disjoint-sym _ (·λ x [ x₁ ] e3) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (·λ x [ x₁ ] e3) (HDAp hd hd₁) | HDLam2 ih | HDLam2 ih1 = HDLam2 (ds-lem-ap ih ih1)
  disjoint-sym _ ⦇⦈[ x ] (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ ⦇⦈[ x ] (HDAp hd hd₁) | HDHole x₁ | HDHole x₂ = HDHole (HNAp x₁ x₂)
  disjoint-sym _ ⦇ e3 ⦈[ x ] (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ ⦇ e3 ⦈[ x ] (HDAp hd hd₁) | HDNEHole x₁ ih | HDNEHole x₂ ih1 = HDNEHole (HNAp x₁ x₂) (ds-lem-ap ih ih1)
  disjoint-sym _ (e3 ∘ e4) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (e3 ∘ e4) (HDAp hd hd₁) | HDAp ih ih₁ | HDAp ih1 ih2 = HDAp (ds-lem-ap ih ih1) (ds-lem-ap ih₁ ih2)


  -- note that this is false, so holes-disjoint isn't transitive
  -- disjoint-new : ∀{e1 e2 u} → holes-disjoint e1 e2 → hole-name-new e1 u → hole-name-new e2 u

  -- it's also not reflexive, because ⦇⦈[ u ] isn't hole-disjoint with
  -- itself since refl : u == u; it's also not anti-reflexive, because the
  -- expression c *is* hole-disjoint with itself (albeit vacuously)
