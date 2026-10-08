import GradualProb.GPLC.FormulaTypes
import GradualProb.GPLC.Terms

/-!
# The type system of GPLC and the static gradual guarantee

The lifting of annotations to formula types, the type system of GPLC
(Figure 6), term precision (Figure 9) and the static gradual guarantee. Terms
carry source gradual types as annotations; the types the system infers are
formula types, and the type operators are those of `GPLC/FormulaTypes`.

## Main results

* `goodTy_liftF`, `goodD_liftFD`: Lemma 21 (lifting well-formedness), with
  `plausible_fin` for the plausibility premise.
* `good_val`, `good_tm`: Lemma 4 (type well-formedness), also Lemma 22.
* `det_val`, `det_tm`: Lemma 23 (determinism of typing).
* `static_gradual_guarantee`: Theorem 2 (static gradual guarantee), for closed
  terms; `static_gradual_guarantee_val`, `static_gradual_guarantee_tm` for open
  values and terms.

## Reading guide

The static gradual guarantee is proved with a size bound
(`static_gradual_guarantee_val_bounded`, `static_gradual_guarantee_tm_bounded`)
and then wrapped.
-/

namespace GradualProb.GPLC

open scoped BigOperators

/-! ## The lifting of annotations

The lifting `⌈·⌉` of source gradual types to formula types (Section 4.1). The
closing formula of `⌈{{σᵢ^ρᵢ}}⌉`, which conjoins `ωᵢ = r` for a known
probability, `ωᵢ ∈ [0,1]` for `?`, and `Σᵢ ωᵢ = 1`, is represented by its set
of solutions: `(∀ i, pᵢ ∈ γ_p(ρᵢ)) ∧ Σᵢ pᵢ = 1`. The recursion goes through the
entry list via `List.get`, so the definition is by well-founded recursion and
its equations are not definitional: unfold with `simp only [liftFTy]` or
`simp only [liftFDist]`. -/

mutual
/-- The lifting `⌈·⌉` of a source gradual simple type. -/
def liftFTy : Ty → FTy
  | .real => .real
  | .bool => .bool
  | .unk  => .unk
  | .arrow s d => .arrow (liftFTy s) (liftFDist d)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega
/-- The lifting `⌈·⌉` of a source gradual distribution type. -/
def liftFDist : DTy → FDist
  | .dist es => .mk es.length (fun i => liftFTy (es.get i).1)
      (fun p => (∀ i, GammaP (es.get i).2 (p i)) ∧ (∑ i, p i) = 1)
termination_by d => sizeOf d
decreasing_by
  simp_wf
  have h1 : sizeOf es[(i : ℕ)] < sizeOf es :=
    List.sizeOf_lt_of_mem (es.getElem_mem i.isLt)
  have h2 : sizeOf (es[(i : ℕ)].1, es[(i : ℕ)].2) =
      1 + sizeOf es[(i : ℕ)].1 + sizeOf es[(i : ℕ)].2 := rfl
  rw [Prod.mk.eta] at h2
  omega
end

/-- `⌈τ⌉`, the lifting of a source gradual simple type to a formula type. It
shares the brackets with Mathlib's `Int.ceil`; the type of the argument picks
the reading. -/
scoped notation:max (name := liftFTyStx) "⌈" τ "⌉" => liftFTy τ
/-- `⌈T⌉`, the lifting of a source gradual distribution type. -/
scoped notation:max (name := liftFDistStx) "⌈" T "⌉" => liftFDist T

/-! ## Lemma 21 (lifting well-formedness) -/

/-- Convexity of `γ_p`. -/
theorem gammaP_convex : ∀ {g : GProb} {a b : ℝ}, GammaP g a → GammaP g b →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → GammaP g (t * a + (1 - t) * b)
  | .q r, _, _, ⟨ha, h0, h1⟩, ⟨hb, _, _⟩, t, _, _ => by
      subst ha; subst hb
      exact ⟨by ring, h0, h1⟩
  | .unk, _, _, ⟨ha0, ha1⟩, ⟨hb0, hb1⟩, t, ht0, ht1 =>
      ⟨by nlinarith, by nlinarith⟩

/-- Plausibility, converted to a `Fin`-indexed assignment. -/
theorem plausible_fin {es : List (Ty × GProb)} (h : Plausible es) :
    ∃ p : Fin es.length → ℝ, (∀ i, GammaP (es.get i).2 (p i)) ∧ (∑ i, p i) = 1 := by
  obtain ⟨ps, hf, hsum⟩ := h
  rw [List.forall₂_iff_get] at hf
  obtain ⟨hlen, hpt⟩ := hf
  have hlen' : es.length = ps.length := by simpa using hlen
  refine ⟨fun i => ps.get (Fin.cast hlen' i), ?_, ?_⟩
  · intro i
    have := hpt i.val (by simpa using i.isLt) (hlen' ▸ i.isLt)
    simpa [List.get_eq_getElem] using this
  · rw [← hsum]
    conv_rhs => rw [← List.ofFn_get ps]
    rw [List.sum_ofFn]
    exact Fin.sum_congr' ps.get hlen'

mutual
/-- Lemma 21 (lifting well-formedness), simple types: if `⊢ σ` then `⊢ ⌈σ⌉`. -/
theorem goodTy_liftF : ∀ {τ : Ty}, WfTy τ → GoodTy ⌈τ⌉
  | _, .real => by simp only [liftFTy]; exact .real
  | _, .bool => by simp only [liftFTy]; exact .bool
  | _, .unk  => by simp only [liftFTy]; exact .unk
  | _, .arrow hs hd => by
      simp only [liftFTy]
      exact .arrow (goodTy_liftF hs) (goodD_liftFD hd)
/-- Lemma 21 (lifting well-formedness), distribution types: if `⊢ T` then
`⊢ ⌈T⌉`. Satisfiability is plausibility (`plausible_fin`); convexity is
`gammaP_convex` at each entry. -/
theorem goodD_liftFD : ∀ {T : DTy}, WfDTy T → GoodD ⌈T⌉
  | _, .dist he hp => by
      simp only [liftFDist]
      refine GoodD.mk ⟨?_, ?_, ?_, ?_⟩ ?_
      · exact plausible_fin hp
      · rintro p ⟨hg, _⟩ i
        exact (gammaP_mem_unit (hg i)).1
      · rintro p ⟨_, hm⟩
        exact hm
      · rintro p q ⟨hgp, hmp⟩ ⟨hgq, hmq⟩ t ht0 ht1
        refine ⟨fun i => gammaP_convex (hgp i) (hgq i) t ht0 ht1, ?_⟩
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hmp, hmq]
        ring
      · exact fun i => goodTy_liftF (he _ (List.get_mem _ i))
end

/-! ## The type system -/

/- The type system of GPLC (Figure 6). Contexts are lists of formula simple
types, and variables are de Bruijn indices that look up a position in the list.
A probabilistic choice has two rules, `choice` for a known probability (whose
`[0,1]` bound is a premise) and `choiceU` for `?`; the conditional types at the
convex hull `chooseSemU` of its branches, and the `let` is exhaustive, typing
the body at every bound term entry. -/
mutual
/-- Typing judgment for values, `Γ ⊢ v : σ` (Figure 6). -/
inductive HasTyV : List FTy → Val → FTy → Prop where
  | var  : ∀ {Γ x σ}, Γ[x]? = some σ → HasTyV Γ (.var x) σ
  | real : ∀ {Γ r}, HasTyV Γ (.real r) .real
  | bool : ∀ {Γ b}, HasTyV Γ (.bool b) .bool
  | lam  : ∀ {Γ τ m D}, HasTyT (liftFTy τ :: Γ) m D → WfTy τ →
             HasTyV Γ (.lam τ m) (.arrow (liftFTy τ) D)
/-- Typing judgment for terms, `Γ ⊢ m : D` (Figure 6). -/
inductive HasTyT : List FTy → Tm → FDist → Prop where
  | val    : ∀ {Γ v σ}, HasTyV Γ v σ → HasTyT Γ (.val v) (pointF σ)
  | app    : ∀ {Γ v w σ σ' s D}, HasTyV Γ v σ → HasTyV Γ w σ' →
               DomCod σ s D → ConsTy σ' s → HasTyT Γ (.app v w) D
  | letin  : ∀ {Γ m n D} {F : Fin D.n → FDist},
               HasTyT Γ m D →
               (∀ i, HasTyT (D.ty i :: Γ) n (F i)) →
               HasTyT Γ (.letin m n) (letSem D F)
  | choice : ∀ {Γ m n D1 D2} {a : ℝ}, 0 ≤ a → a ≤ 1 →
               HasTyT Γ m D1 → HasTyT Γ n D2 →
               HasTyT Γ (.choice (.q a) m n) (chooseSem a D1 D2)
  | choiceU : ∀ {Γ m n D1 D2}, HasTyT Γ m D1 → HasTyT Γ n D2 →
               HasTyT Γ (.choice .unk m n) (chooseSemU D1 D2)
  | ascT   : ∀ {Γ m D T}, HasTyT Γ m D → ConsD D (liftFDist T) → WfDTy T →
               HasTyT Γ (.ascT m T) (liftFDist T)
  | ascV   : ∀ {Γ v σ τ}, HasTyV Γ v σ → ConsTy σ (liftFTy τ) → WfTy τ →
               HasTyT Γ (.ascV v τ) (pointF (liftFTy τ))
  | ite    : ∀ {Γ v m n σ D1 D2}, HasTyV Γ v σ → ConsTy σ .bool →
               HasTyT Γ m D1 → HasTyT Γ n D2 → ConsD D1 D2 →
               HasTyT Γ (.ite v m n) (chooseSemU D1 D2)
  | add    : ∀ {Γ v w σ1 σ2}, HasTyV Γ v σ1 → ConsTy σ1 .real →
               HasTyV Γ w σ2 → ConsTy σ2 .real →
               HasTyT Γ (.add v w) (pointF .real)
end

/-- `Γ ⊢ v : σ`, the typing of values of GPLC (Figure 6). The three languages
write their judgments with `⊢`: SPLC's carries the subscript `ₛ` (`⊢ₛ`), and
GPLC's and TPLC's share the symbol, the language of the term picking the
reading. -/
scoped notation:50 (name := hasTyVStx) Γ:51 " ⊢ " v:51 " : " σ:51 => HasTyV Γ v σ
/-- `Γ ⊢ m : D`, the typing of terms of GPLC (Figure 6). -/
scoped notation:50 (name := hasTyTStx) Γ:51 " ⊢ " m:51 " : " D:51 => HasTyT Γ m D
/-- `⊢ v : σ`, the typing of closed values of GPLC. -/
scoped notation:50 (name := hasTyVClosedStx) "⊢ " v:51 " : " σ:51 => HasTyV [] v σ
/-- `⊢ m : D`, the typing of closed terms of GPLC. -/
scoped notation:50 (name := hasTyTClosedStx) "⊢ " m:51 " : " D:51 => HasTyT [] m D

/-! ## Determinism

Typing assigns at most one type. The `let` case of the static gradual
guarantee needs it to identify the branch types given by the induction
hypothesis with the ones in the derivation it builds. -/

/-- `dom`/`cod` is a partial function. -/
theorem domcod_det : ∀ {σ s s' : FTy} {d d' : FDist},
    DomCod σ s d → DomCod σ s' d' → s = s' ∧ d = d'
  | _, _, _, _, _, .arrow, .arrow => ⟨rfl, rfl⟩
  | _, _, _, _, _, .unk, .unk => ⟨rfl, rfl⟩

mutual
/-- Lemma 23 (determinism of typing), values: if `Γ ⊢ v : σ₁` and
`Γ ⊢ v : σ₂`, then `σ₁ = σ₂`. -/
theorem det_val : ∀ {Γ} {v : Val} {σ1 σ2}, Γ ⊢ v : σ1 → Γ ⊢ v : σ2 → σ1 = σ2
  | _, _, _, _, .var hx, h2 => by
      cases h2 with
      | var hx' => exact Option.some.inj (hx.symm.trans hx')
  | _, _, _, _, .real, h2 => by cases h2 with | real => rfl
  | _, _, _, _, .bool, h2 => by cases h2 with | bool => rfl
  | _, _, _, _, .lam hm _, h2 => by
      cases h2 with
      | lam hm' _ => rw [det_tm hm hm']
/-- Lemma 23 (determinism of typing), terms: if `Γ ⊢ m : D₁` and
`Γ ⊢ m : D₂`, then `D₁ = D₂`. -/
theorem det_tm : ∀ {Γ} {m : Tm} {D1 D2}, Γ ⊢ m : D1 → Γ ⊢ m : D2 → D1 = D2
  | _, _, _, _, .val hv, h2 => by
      cases h2 with
      | val hv' => rw [det_val hv hv']
  | _, _, _, _, .app hv _ hdc _, h2 => by
      cases h2 with
      | app hv' _ hdc' _ =>
        have hσ := det_val hv hv'
        subst hσ
        exact (domcod_det hdc hdc').2
  | _, _, _, _, @HasTyT.letin _ _ nb Dsc F hm hF, h2 => by
      cases h2 with
      | @letin _ _ _ Dsc2 F2 hm2 hF2 =>
        have hD := det_tm hm hm2
        subst hD
        congr 1
        funext j
        exact det_tm (hF j) (hF2 j)
  | _, _, _, _, .choice _ _ hm hn, h2 => by
      cases h2 with
      | choice _ _ hm' hn' => rw [det_tm hm hm', det_tm hn hn']
  | _, _, _, _, .choiceU hm hn, h2 => by
      cases h2 with
      | choiceU hm' hn' => rw [det_tm hm hm', det_tm hn hn']
  | _, _, _, _, .ascT _ _ _, h2 => by
      cases h2 with
      | ascT _ _ _ => rfl
  | _, _, _, _, .ascV _ _ _, h2 => by
      cases h2 with
      | ascV _ _ _ => rfl
  | _, _, _, _, .ite _ _ hm hn _, h2 => by
      cases h2 with
      | ite _ _ hm' hn' _ => rw [det_tm hm hm', det_tm hn hn']
  | _, _, _, _, .add _ _ _ _, h2 => by
      cases h2 with
      | add _ _ _ _ => rfl
end

/-! ## Lemma 4 (type well-formedness) -/

/-- Definition 5 (type and environment well-formedness), environments: every
type in the context is well-formed. -/
def CtxGood (Γ : List FTy) : Prop := ∀ σ ∈ Γ, GoodTy σ

/-- Extending a well-formed context with a well-formed type yields a well-formed
context. -/
theorem ctxGood_cons {σ : FTy} {Γ : List FTy} (hσ : GoodTy σ)
    (hΓ : CtxGood Γ) : CtxGood (σ :: Γ) := by
  intro σ' hσ'
  rcases List.mem_cons.1 hσ' with rfl | hm
  · exact hσ
  · exact hΓ σ' hm

/-- Every type looked up in a well-formed context is well-formed. -/
theorem ctxGood_get {Γ : List FTy} {x : ℕ} {σ : FTy}
    (hΓ : CtxGood Γ) (hx : Γ[x]? = some σ) : GoodTy σ :=
  hΓ σ (List.mem_of_getElem? hx)

mutual
/-- Lemma 4 (type well-formedness), item 1, values, also Lemma 22 (well-formed types):
under a well-formed context, a well-typed value has a well-formed type. The
annotations need no hypothesis here, since the rules for `lam` and the
ascriptions carry their well-formedness as premises. -/
theorem good_val : ∀ {Γ} {v : Val} {σ}, Γ ⊢ v : σ → CtxGood Γ → GoodTy σ
  | _, _, _, .var hx, hΓ => ctxGood_get hΓ hx
  | _, _, _, .real, _ => .real
  | _, _, _, .bool, _ => .bool
  | _, _, _, .lam hm hτ, hΓ =>
      .arrow (goodTy_liftF hτ)
        (good_tm hm (ctxGood_cons (goodTy_liftF hτ) hΓ))
/-- Lemma 4 (type well-formedness), item 2, terms, also Lemma 22 (well-formed types):
under a well-formed context, a well-typed term has a well-formed type. The
operators preserve well-formedness (`goodD_choose`, `goodD_chooseU`,
`goodD_let`) and the lifting of a well-formed annotation is well-formed
(`goodD_liftFD`). -/
theorem good_tm : ∀ {Γ} {m : Tm} {D}, Γ ⊢ m : D → CtxGood Γ → GoodD D
  | _, _, _, .val hv, hΓ => goodD_point (good_val hv hΓ)
  | _, _, _, .app hv _ hdc _, hΓ => by
      cases hdc with
      | arrow =>
        cases good_val hv hΓ with
        | arrow _ hD => exact hD
      | unk => exact goodD_topF
  | _, _, _, @HasTyT.letin _ _ _ D F hm hF, hΓ => by
      refine goodD_let (good_tm hm hΓ) (fun i => ?_)
      exact good_tm (hF i) (ctxGood_cons ((good_tm hm hΓ).tys i) hΓ)
  | _, _, _, .choice ha0 ha1 hm hn, hΓ =>
      goodD_choose ha0 ha1 (good_tm hm hΓ) (good_tm hn hΓ)
  | _, _, _, .choiceU hm hn, hΓ =>
      goodD_chooseU (good_tm hm hΓ) (good_tm hn hΓ)
  | _, _, _, .ascT _ _ hT, _ => goodD_liftFD hT
  | _, _, _, .ascV _ _ hτ, _ => goodD_point (goodTy_liftF hτ)
  | _, _, _, .ite _ _ hm hn _, hΓ =>
      goodD_chooseU (good_tm hm hΓ) (good_tm hn hΓ)
  | _, _, _, .add _ _ _ _, _ => goodD_point .real
end

/-! ## Context precision -/

/-- Pointwise context precision on formula contexts. -/
def PrecCtx (Γ Γ' : List FTy) : Prop := List.Forall₂ PrecTy Γ Γ'

/-- `Γ ⊑ Γ'`, context precision. -/
scoped infix:50 (name := precCtxStx) " ⊑ " => PrecCtx

/-- `Γ ⊑ Γ'` and `σ ⊑ σ'` give `σ :: Γ ⊑ σ' :: Γ'`. -/
theorem precCtx_cons {σ σ' : FTy} {Γ Γ' : List FTy} (h : PrecTy σ σ')
    (hΓ : PrecCtx Γ Γ') : PrecCtx (σ :: Γ) (σ' :: Γ') :=
  List.Forall₂.cons h hΓ

/-- Positional lookup transports along context precision. -/
theorem precCtx_getElem : ∀ {Γ Γ' : List FTy}, PrecCtx Γ Γ' → ∀ {x : ℕ} {σ : FTy},
    Γ[x]? = some σ → ∃ σ', Γ'[x]? = some σ' ∧ PrecTy σ σ'
  | _, _, .nil, x, σ, hx => by simp at hx
  | _, _, .cons hab htail, x, σ, hx => by
      cases x with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨_, by simp, hab⟩
      | succ n =>
        simp only [List.getElem?_cons_succ] at hx
        obtain ⟨σ', h1, h2⟩ := precCtx_getElem htail hx
        exact ⟨σ', by simpa using h1, h2⟩


/-! ## Term precision -/

/- Term precision (Figure 9): a structural congruence on terms that compares
the annotations of `lam`, `ascT` and `ascV` by the precision of their liftings,
`⌈τ⌉ ⊑ ⌈τ'⌉`, and the probabilities of a choice by `PrecP`. -/
mutual
/-- Term precision on values. -/
inductive PrecV : Val → Val → Prop where
  | var  : ∀ {x}, PrecV (.var x) (.var x)
  | real : ∀ {r}, PrecV (.real r) (.real r)
  | bool : ∀ {b}, PrecV (.bool b) (.bool b)
  | lam  : ∀ {τ1 τ2 m n}, PrecTy (liftFTy τ1) (liftFTy τ2) → PrecT m n →
      PrecV (.lam τ1 m) (.lam τ2 n)
/-- Term precision on terms. -/
inductive PrecT : Tm → Tm → Prop where
  | val    : ∀ {v w}, PrecV v w → PrecT (.val v) (.val w)
  | app    : ∀ {v1 v2 w1 w2}, PrecV v1 v2 → PrecV w1 w2 → PrecT (.app v1 w1) (.app v2 w2)
  | letin  : ∀ {m1 m2 n1 n2}, PrecT m1 m2 → PrecT n1 n2 →
      PrecT (.letin m1 n1) (.letin m2 n2)
  | choice : ∀ {p1 p2 m1 m2 n1 n2}, PrecP p1 p2 → PrecT m1 m2 → PrecT n1 n2 →
      PrecT (.choice p1 m1 n1) (.choice p2 m2 n2)
  | ascT   : ∀ {m n T1 T2}, PrecT m n → PrecD (liftFDist T1) (liftFDist T2) →
      PrecT (.ascT m T1) (.ascT n T2)
  | ascV   : ∀ {v w τ1 τ2}, PrecV v w → PrecTy (liftFTy τ1) (liftFTy τ2) →
      PrecT (.ascV v τ1) (.ascV w τ2)
  | ite    : ∀ {v w m1 m2 n1 n2}, PrecV v w → PrecT m1 m2 → PrecT n1 n2 →
      PrecT (.ite v m1 n1) (.ite w m2 n2)
  | add    : ∀ {v1 v2 w1 w2}, PrecV v1 v2 → PrecV w1 w2 → PrecT (.add v1 w1) (.add v2 w2)
end

/-- `v ⊑ w`, term precision on values of GPLC (Figure 9). -/
scoped infix:50 (name := precVStx) " ⊑ " => PrecV
/-- `m ⊑ n`, term precision on terms of GPLC (Figure 9). -/
scoped infix:50 (name := precTStx) " ⊑ " => PrecT

/-! ## Theorem 2 (static gradual guarantee)

The induction is bounded by a natural number `k` that bounds the size of the
right term. Recursion on `sizeOf n` directly fails: casing the precision
hypothesis refines `n` in the goal but not in the termination measure, whereas
the bound `k` is an independent argument. -/
mutual
/-- Theorem 2 (static gradual guarantee), item 1, for open values, with a size bound
`k` on the right value. -/
theorem static_gradual_guarantee_val_bounded : ∀ (k : ℕ) {Γ Γ' : List FTy} {v w : Val} {σ : FTy},
    HasTyV Γ v σ → PrecCtx Γ Γ' → PrecV v w →
    CtxGood Γ → CtxGood Γ' → WfAnnV w → sizeOf w ≤ k →
    ∃ σ', HasTyV Γ' w σ' ∧ PrecTy σ σ' := by
  intro k Γ Γ' v w σ h hΓ hvw hg hg' hann hk
  cases hvw with
  | var =>
      cases h with
      | var hx =>
        obtain ⟨σ', h1, h2⟩ := precCtx_getElem hΓ hx
        exact ⟨σ', .var h1, h2⟩
  | real => cases h with | real => exact ⟨.real, .real, .real⟩
  | bool => cases h with | bool => exact ⟨.bool, .bool, .bool⟩
  | lam hττ' hmn =>
      cases h with
      | lam hm hτ =>
        cases hann with
        | lam hτ' hannm =>
          obtain ⟨D', hty', hDD'⟩ := static_gradual_guarantee_tm_bounded _ hm
            (precCtx_cons (hττ') hΓ) hmn
            (ctxGood_cons (goodTy_liftF hτ) hg)
            (ctxGood_cons (goodTy_liftF hτ') hg') hannm (le_refl _)
          exact ⟨_, .lam hty' hτ', .arrow (hττ') hDD'⟩
termination_by k => k
decreasing_by
  all_goals simp only [Val.lam.sizeOf_spec] at hk
  all_goals omega
/-- Theorem 2 (static gradual guarantee), item 2, for open terms, with a size bound
`k` on the right term: typing is monotone with respect to the precision
of terms and contexts. In the `let` case, every entry of the less precise
bound term type is covered by a more precise one (right coverage of `PrecD`), at
which the body types; the induction hypothesis types the body at the less
precise entry, determinism (`det_tm`) identifies the branch types, and
`prec_let` concludes. -/
theorem static_gradual_guarantee_tm_bounded : ∀ (k : ℕ) {Γ Γ' : List FTy} {m n : Tm} {D : FDist},
    HasTyT Γ m D → PrecCtx Γ Γ' → PrecT m n →
    CtxGood Γ → CtxGood Γ' → WfAnnT n → sizeOf n ≤ k →
    ∃ D', HasTyT Γ' n D' ∧ PrecD D D' := by
  intro k Γ Γ' m n D h hΓ hmn hg hg' hann hk
  cases h with
  | val hv =>
      cases hmn with
      | val hvw =>
        cases hann with
        | val hannv =>
          obtain ⟨σ', hty', hσσ'⟩ := static_gradual_guarantee_val_bounded _ hv hΓ hvw hg hg' hannv (le_refl _)
          exact ⟨_, .val hty', prec_point hσσ'⟩
  | app hv hw hdc hcons =>
      cases hmn with
      | app hvv' hww' =>
        cases hann with
        | app hannv hannw =>
          obtain ⟨σv', htyv', hσv⟩ := static_gradual_guarantee_val_bounded _ hv hΓ hvv' hg hg' hannv (le_refl _)
          obtain ⟨σw', htyw', hσw⟩ := static_gradual_guarantee_val_bounded _ hw hΓ hww' hg hg' hannw (le_refl _)
          obtain ⟨s', d', hdc', hss', hdd'⟩ :=
            domcod_mono hσv hdc (good_val hv hg)
          exact ⟨d', .app htyv' htyw' hdc' (cons_prec_ty hcons hσw hss'), hdd'⟩
  | @letin _ _ _ D F hm hF =>
      cases hmn with
      | @letin _ _ _ n' hmm' hnn' =>
        cases hann with
        | letin hannm hannn =>
          classical
          obtain ⟨D', hm', hDD'⟩ := static_gradual_guarantee_tm_bounded _ hm hΓ hmm' hg hg' hannm (le_refl _)
          have hgD : GoodD D := good_tm hm hg
          have hgD' : GoodD D' := good_tm hm' hg'
          have hctxj : ∀ j, CtxGood (D'.ty j :: Γ') := fun j =>
            ctxGood_cons (hgD'.tys j) hg'
          -- every less precise entry is covered by a more precise one (right
          -- coverage), where the body types; the induction hypothesis lifts it
          have hcanon : ∀ j : Fin D'.n, ∃ G, HasTyT (D'.ty j :: Γ') n' G := by
            intro j
            obtain ⟨i, hij⟩ := hDD'.covR j
            obtain ⟨G, hG, _⟩ := static_gradual_guarantee_tm_bounded _ (hF i) (precCtx_cons hij hΓ) hnn'
              (ctxGood_cons (hgD.tys i) hg) (hctxj j) hannn (le_refl _)
            exact ⟨G, hG⟩
          choose F' hF' using hcanon
          refine ⟨letSem D' F', HasTyT.letin hm' hF', ?_⟩
          refine prec_let hDD' ?_ (fun j => (good_tm (hF' j) (hctxj j)).good)
          intro i j hij
          obtain ⟨T'', hT'', hFT⟩ := static_gradual_guarantee_tm_bounded _ (hF i) (precCtx_cons hij hΓ) hnn'
            (ctxGood_cons (hgD.tys i) hg) (hctxj j) hannn (le_refl _)
          rw [← det_tm hT'' (hF' j)]
          exact hFT
  | choice ha0 ha1 hm hn =>
      cases hmn with
      | choice hpp' hmm' hnn' =>
        cases hann with
        | choice hannm hannn =>
          obtain ⟨D1', hty1', h1⟩ := static_gradual_guarantee_tm_bounded _ hm hΓ hmm' hg hg' hannm (le_refl _)
          obtain ⟨D2', hty2', h2⟩ := static_gradual_guarantee_tm_bounded _ hn hΓ hnn' hg hg' hannn (le_refl _)
          cases hpp' with
          | refl =>
            exact ⟨_, .choice ha0 ha1 hty1' hty2', prec_choose ha0 ha1 h1 h2⟩
          | unk =>
            exact ⟨_, .choiceU hty1' hty2', prec_choose_unk ha0 ha1 h1 h2⟩
  | choiceU hm hn =>
      cases hmn with
      | choice hpp' hmm' hnn' =>
        cases hann with
        | choice hannm hannn =>
          obtain ⟨D1', hty1', h1⟩ := static_gradual_guarantee_tm_bounded _ hm hΓ hmm' hg hg' hannm (le_refl _)
          obtain ⟨D2', hty2', h2⟩ := static_gradual_guarantee_tm_bounded _ hn hΓ hnn' hg hg' hannn (le_refl _)
          cases hpp' with
          | refl => exact ⟨_, .choiceU hty1' hty2', prec_chooseU h1 h2⟩
          | unk => exact ⟨_, .choiceU hty1' hty2', prec_chooseU h1 h2⟩
  | ascT hm hcons hT =>
      cases hmn with
      | ascT hmm' hTT' =>
        cases hann with
        | ascT hannm hT' =>
          obtain ⟨D'', hty'', hprec⟩ := static_gradual_guarantee_tm_bounded _ hm hΓ hmm' hg hg' hannm (le_refl _)
          exact ⟨_, .ascT hty''
            (cons_prec_d hcons hprec (hTT')) hT',
            hTT'⟩
  | ascV hv hcons hτ =>
      cases hmn with
      | ascV hvw hττ' =>
        cases hann with
        | ascV hannv hτ' =>
          obtain ⟨σ', hty', hσσ'⟩ := static_gradual_guarantee_val_bounded _ hv hΓ hvw hg hg' hannv (le_refl _)
          exact ⟨_, .ascV hty'
            (cons_prec_ty hcons hσσ' (hττ')) hτ',
            prec_point (hττ')⟩
  | ite hv hcb hm hn hc =>
      cases hmn with
      | ite hvv' hmm' hnn' =>
        cases hann with
        | ite hannv hannm hannn =>
          obtain ⟨σ', htyv', hσσ'⟩ := static_gradual_guarantee_val_bounded _ hv hΓ hvv' hg hg' hannv (le_refl _)
          obtain ⟨D1', hty1', h1⟩ := static_gradual_guarantee_tm_bounded _ hm hΓ hmm' hg hg' hannm (le_refl _)
          obtain ⟨D2', hty2', h2⟩ := static_gradual_guarantee_tm_bounded _ hn hΓ hnn' hg hg' hannn (le_refl _)
          exact ⟨_, .ite htyv' (cons_prec_ty hcb hσσ' .bool)
            hty1' hty2' (cons_prec_d hc h1 h2), prec_chooseU h1 h2⟩
  | add hv hc1 hw hc2 =>
      cases hmn with
      | add hvv' hww' =>
        cases hann with
        | add hannv hannw =>
          obtain ⟨σ1', hty1', hσ1⟩ := static_gradual_guarantee_val_bounded _ hv hΓ hvv' hg hg' hannv (le_refl _)
          obtain ⟨σ2', hty2', hσ2⟩ := static_gradual_guarantee_val_bounded _ hw hΓ hww' hg hg' hannw (le_refl _)
          exact ⟨_, .add hty1' (cons_prec_ty hc1 hσ1 .real)
            hty2' (cons_prec_ty hc2 hσ2 .real), prec_point .real⟩
termination_by k => k
decreasing_by
  all_goals
    simp only [Tm.val.sizeOf_spec, Tm.app.sizeOf_spec, Tm.letin.sizeOf_spec,
      Tm.choice.sizeOf_spec, Tm.ascT.sizeOf_spec, Tm.ascV.sizeOf_spec,
      Tm.ite.sizeOf_spec, Tm.add.sizeOf_spec, Val.lam.sizeOf_spec] at hk
  all_goals omega
end

/-- Theorem 2 (static gradual guarantee), item 1, open values: under
well-formed contexts `Γ ⊑ Γ'` and well-formed annotations of `w`, if `v : σ`
and `v ⊑ w` then `w : σ'` with `σ ⊑ σ'`. -/
theorem static_gradual_guarantee_val {Γ Γ' : List FTy} {v w : Val} {σ : FTy}
    (h : Γ ⊢ v : σ) (hΓ : Γ ⊑ Γ') (hvw : v ⊑ w)
    (hg : CtxGood Γ) (hg' : CtxGood Γ') (hann : WfAnnV w) :
    ∃ σ', Γ' ⊢ w : σ' ∧ σ ⊑ σ' :=
  static_gradual_guarantee_val_bounded (sizeOf w) h hΓ hvw hg hg' hann (le_refl _)

/-- Theorem 2 (static gradual guarantee), item 2, open terms: under
well-formed contexts `Γ ⊑ Γ'` and well-formed annotations of `n`, if `m : D`
and `m ⊑ n` then `n : D'` with `D ⊑ D'`. -/
theorem static_gradual_guarantee_tm {Γ Γ' : List FTy} {m n : Tm} {D : FDist}
    (h : Γ ⊢ m : D) (hΓ : Γ ⊑ Γ') (hmn : m ⊑ n)
    (hg : CtxGood Γ) (hg' : CtxGood Γ') (hann : WfAnnT n) :
    ∃ D', Γ' ⊢ n : D' ∧ D ⊑ D' :=
  static_gradual_guarantee_tm_bounded (sizeOf n) h hΓ hmn hg hg' hann (le_refl _)

/-- Theorem 2 (static gradual guarantee), item 2, closed terms: if
`⊢ m : D`, `m ⊑ n`, and the annotations of `n` are well-formed, then `⊢ n : D'`
for some `D'` with `D ⊑ D'`. -/
theorem static_gradual_guarantee {m n : Tm} {D : FDist} (hty : ⊢ m : D)
    (hprec : m ⊑ n) (hann : WfAnnT n) :
    ∃ D', ⊢ n : D' ∧ D ⊑ D' :=
  static_gradual_guarantee_tm hty List.Forall₂.nil hprec
    (by intro σ h; simp at h) (by intro σ h; simp at h) hann

end GradualProb.GPLC
