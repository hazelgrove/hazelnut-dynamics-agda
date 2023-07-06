open import Prelude
open import Nat
open import core
open import contexts
open import lemmas-disjointness
open import dom-eq

module disjointness where
  -- if a hole name is new in a term, then the resultant context is
  -- disjoint from any singleton context with that hole name
  mutual
    elab-new-disjoint-synth : ∀ { e u τ d Δ Θ Γ Γ' τ'} →
                          hole-name-new e u →
                          Γ , Θ ⊢ e ⇒ τ ~> d ⊣ Δ →
                          Δ ## (■ (u , Γ' , τ'))
    elab-new-disjoint-synth HNConst ESConst = empty-disj (■ (_ , _ , _))
    elab-new-disjoint-synth (HNAsc hn) (ESAsc x) = elab-new-disjoint-ana hn x
    elab-new-disjoint-synth HNVar (ESVar x₁) = empty-disj (■ (_ , _ , _))
    elab-new-disjoint-synth (HNLam1 hn) ()
    elab-new-disjoint-synth (HNLam2 hn) (ESLam x₁ exp) = elab-new-disjoint-synth hn exp
    elab-new-disjoint-synth (HNTLam hn) (ESTLam e) = elab-new-disjoint-synth hn e
    elab-new-disjoint-synth (HNTAp hn) (ESTAp x₁ x₂ x₃) = elab-new-disjoint-ana hn x₃ 
    elab-new-disjoint-synth (HNHole x) ESEHole = disjoint-singles x
    elab-new-disjoint-synth (HNNEHole x hn) (ESNEHole x₁ exp) = disjoint-parts (elab-new-disjoint-synth hn exp) (disjoint-singles x)
    elab-new-disjoint-synth (HNAp hn hn₁) (ESAp x x₁ x₂ x₃ x₄ x₅) =
                                            disjoint-parts (elab-new-disjoint-ana hn x₄)
                                                  (elab-new-disjoint-ana hn₁ x₅)

    elab-new-disjoint-ana : ∀ { e u τ d Δ Θ Γ Γ' τ' τ2} →
                              hole-name-new e u →
                              Γ , Θ ⊢ e ⇐ τ ~> d :: τ2 ⊣ Δ →
                              Δ ## (■ (u , Γ' , τ'))
    elab-new-disjoint-ana hn (EASubsume x x₁ x₂ x₃) = elab-new-disjoint-synth hn x₂
    elab-new-disjoint-ana (HNLam1 hn) (EALam x₁ x₂ ex) = elab-new-disjoint-ana hn ex
    elab-new-disjoint-ana (HNTLam hn) (EATLam x₁ x₂) = elab-new-disjoint-ana hn x₂
    elab-new-disjoint-ana (HNHole x) EAEHole = disjoint-singles x
    elab-new-disjoint-ana (HNNEHole x hn) (EANEHole x₁ x₂) = disjoint-parts (elab-new-disjoint-synth hn x₂) (disjoint-singles x)

  -- dual of the above: if elaborating a term produces a context that's
  -- disjoint with a singleton context, it must be that the index is a new
  -- hole name in the original term
  mutual
    elab-disjoint-new-synth : ∀{ e τ d Δ Θ u Γ Γ' τ'} →
                                Γ , Θ ⊢ e ⇒ τ ~> d ⊣ Δ →
                                Δ ## (■ (u , Γ' , τ')) →
                                hole-name-new e u
    elab-disjoint-new-synth ESConst disj = HNConst
    elab-disjoint-new-synth (ESVar x₁) disj = HNVar
    elab-disjoint-new-synth (ESLam x₁ ex) disj = HNLam2 (elab-disjoint-new-synth ex disj)
    elab-disjoint-new-synth (ESTLam x₁) x = HNTLam (elab-disjoint-new-synth x₁ x)
    elab-disjoint-new-synth (ESAp {Δ1 = Δ1} x x₁ x₂ x₃ x₄ x₅) disj
      with elab-disjoint-new-ana x₄ (disjoint-union1 disj) | elab-disjoint-new-ana x₅ (disjoint-union2 {Γ1 = Δ1} disj)
    ... | ih1 | ih2 = HNAp ih1 ih2
    elab-disjoint-new-synth (ESTAp x₁ x₂ x₃) x = HNTAp (elab-disjoint-new-ana x₃ x)
    elab-disjoint-new-synth {Γ = Γ} ESEHole disj = HNHole (singles-notequal disj)
    elab-disjoint-new-synth (ESNEHole {Δ = Δ} x ex) disj = HNNEHole (singles-notequal (disjoint-union2 {Γ1 = Δ} disj))
                                                                      (elab-disjoint-new-synth ex (disjoint-union1 disj))
    elab-disjoint-new-synth (ESAsc x) disj = HNAsc (elab-disjoint-new-ana x disj)

    elab-disjoint-new-ana : ∀{ e τ d Δ Θ u Γ Γ' τ2 τ'} →
                                Γ , Θ ⊢ e ⇐ τ ~> d :: τ2 ⊣ Δ →
                                Δ ## (■ (u , Γ' , τ')) →
                                hole-name-new e u
    elab-disjoint-new-ana (EALam x₁ x₂ ex) disj = HNLam1 (elab-disjoint-new-ana ex disj)
    elab-disjoint-new-ana (EATLam x₁ x₂) x = HNTLam (elab-disjoint-new-ana x₂ x)
    elab-disjoint-new-ana (EASubsume x x₁ x₂ x₃) disj = elab-disjoint-new-synth x₂ disj
    elab-disjoint-new-ana EAEHole disj = HNHole (singles-notequal disj)
    elab-disjoint-new-ana (EANEHole {Δ = Δ} x x₁) disj = HNNEHole (singles-notequal (disjoint-union2 {Γ1 = Δ} disj))
                                                                    (elab-disjoint-new-synth x₁ (disjoint-union1 disj))

  -- collect up the hole names of a term as the indices of a trivial context
  data holes : (e : hexp) (H : ⊤ ctx) → Set where
    HConst : holes c ∅
    HAsc   : ∀{e τ H} → holes e H → holes (e ·: τ) H
    HVar   : ∀{x} → holes (X x) ∅
    HLam1  : ∀{x e H} → holes e H → holes (·λ x e) H
    HLam2  : ∀{x e τ H} → holes e H → holes (·λ x [ τ ] e) H
    HTLam  : ∀{e H} → holes e H → holes (·Λ e) H
    HEHole : ∀{u} → holes (⦇-⦈[ u ]) (■ (u , <>))
    HNEHole : ∀{e u H} → holes e H → holes (⦇⌜ e ⌟⦈[ u ]) (H ,, (u , <>))
    HAp : ∀{e1 e2 H1 H2} → holes e1 H1 → holes e2 H2 → holes (e1 ∘ e2) (H1 ∪ H2)
    HTAp : ∀{e τ H} → holes e H → holes (e < τ >) H

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
  find-holes (·Λ e) with find-holes e 
  ... | (h , d) = h , HTLam d
  find-holes ⦇-⦈[ x ] = (■ (x , <>)) , HEHole
  find-holes ⦇⌜ e ⌟⦈[ x ] with find-holes e
  ... | (h , d) = h ,, (x , <>) , HNEHole d
  find-holes (e1 ∘ e2) with find-holes e1 | find-holes e2
  ... | (h1 , d1) | (h2 , d2)  = (h1 ∪ h2 ) , (HAp d1 d2)
  find-holes (e < τ >) with find-holes e 
  ... | (h , d) = h , HTAp d


  -- if a hole name is new then it's apart from the collection of hole
  -- names
  lem-apart-new : ∀{e H u} → holes e H → hole-name-new e u → u # H
  lem-apart-new HConst HNConst = refl
  lem-apart-new (HAsc h) (HNAsc hn) = lem-apart-new h hn
  lem-apart-new HVar HNVar = refl
  lem-apart-new (HLam1 h) (HNLam1 hn) = lem-apart-new h hn
  lem-apart-new (HLam2 h) (HNLam2 hn) = lem-apart-new h hn
  lem-apart-new (HTLam h) (HNTLam hn) = lem-apart-new h hn
  lem-apart-new HEHole (HNHole x) = apart-singleton (flip x)
  lem-apart-new (HNEHole {u = u'} {H = H} h) (HNNEHole  {u = u}  x hn) = apart-parts H (■ (u' , <>)) u (lem-apart-new h hn) (apart-singleton (flip x))
  lem-apart-new (HAp {H1 = H1} {H2 = H2} h h₁) (HNAp hn hn₁) = apart-parts H1 H2 _ (lem-apart-new h hn) (lem-apart-new h₁ hn₁)
  lem-apart-new (HTAp h) (HNTAp hn) = lem-apart-new h hn

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

  -- the holes of an expression have the same domain as the context
  -- produced during expansion; that is, we don't add anything we don't
  -- find in the term during expansion.
  mutual
    holes-delta-ana : ∀{Γ Θ H e τ d τ' Δ} →
                    holes e H →
                    Γ , Θ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                    dom-eq Δ H
    holes-delta-ana (HLam1 h) (EALam x₁ x₂ exp) = holes-delta-ana h exp
    holes-delta-ana h (EASubsume x x₁ x₂ x₃) = holes-delta-synth h x₂
    holes-delta-ana (HEHole {u = u}) EAEHole = dom-single u
    holes-delta-ana (HNEHole {u = u} h) (EANEHole x x₁) =
                                  dom-union (##-comm (lem-apart-sing-disj (lem-apart-new h (elab-disjoint-new-synth x₁ x))))
                                            (holes-delta-synth h x₁)
                                            (dom-single u)

    holes-delta-synth : ∀{Γ Θ H e τ d Δ} →
                    holes e H →
                    Γ , Θ ⊢ e ⇒ τ ~> d ⊣ Δ →
                    dom-eq Δ H
    holes-delta-synth HConst ESConst = dom-∅
    holes-delta-synth (HAsc h) (ESAsc x) = holes-delta-ana h x
    holes-delta-synth HVar (ESVar x₁) = dom-∅
    holes-delta-synth (HLam2 h) (ESLam x₁ exp) = holes-delta-synth h exp
    holes-delta-synth (HEHole {u = u}) ESEHole = dom-single u
    holes-delta-synth (HNEHole {u = u} h) (ESNEHole x exp) = dom-union ((##-comm (lem-apart-sing-disj (lem-apart-new h (elab-disjoint-new-synth exp x)))))
                                                                       (holes-delta-synth h exp)
                                                                       (dom-single u)
    holes-delta-synth (HAp h h₁) (ESAp x x₁ x₂ x₃ x₄ x₅) = dom-union (holes-disjoint-disjoint h h₁ x) (holes-delta-ana h x₄) (holes-delta-ana h₁ x₅)

  -- this is the main result of this file:
  --
  -- if you elaborate two hole-disjoint expressions analytically, the Δs
  -- produced are disjoint.
  --
  -- note that this is likely true for synthetic expansions in much the
  -- same way, but we only prove half of the usual pair here because that's
  -- all we need to establish expansion generality and elaborability. the
  -- proof technique here is explcitly *not* structurally inductive on the
  -- expansion judgement, because that approach relies on weakening of
  -- expansion, which is false because of the substitution contexts. giving
  -- expansion weakning would take away unicity, so we avoid the whole
  -- question.
  elab-ana-disjoint : ∀{ e1 e2 τ1 τ2 e1' e2' τ1' τ2' Γ Θ Δ1 Δ2 } →
          holes-disjoint e1 e2 →
          Γ , Θ ⊢ e1 ⇐ τ1 ~> e1' :: τ1' ⊣ Δ1 →
          Γ , Θ ⊢ e2 ⇐ τ2 ~> e2' :: τ2' ⊣ Δ2 →
          Δ1 ## Δ2
  elab-ana-disjoint {e1} {e2} hd ana1 ana2
    with find-holes e1 | find-holes e2
  ... | (_ , he1) | (_ , he2) = dom-eq-disj (holes-disjoint-disjoint he1 he2 hd)
                                            (holes-delta-ana he1 ana1)
                                            (holes-delta-ana he2 ana2)
