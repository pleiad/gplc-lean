import GradualProb.SPLC.Semantics

/-!
# Type safety of SPLC

This module proves Theorem 1 (type safety for SPLC): a closed well-typed program
reduces to a distribution value whose type, by rule (V), is equal to the
program's type.  The proof follows the appendix: Lemma 18 (substitution modulo
equality), Lemma 19 (preservation) and Lemma 20 (termination, by Tait's method).
The terms are those of SPLC, so every statement assumes `IsStaticTm`.

## Main results

* `subst_val`, `subst_tm`: Lemma 18 (substitution modulo equality).
* `preservation`: Lemma 19 (preservation).
* `termination`: Lemma 20 (termination), from `fundamental_val`,
  `fundamental_tm` over the reducibility predicate `RedV`.
* `type_safety`: Theorem 1 (type safety for SPLC).
* `semantic_soundness`: Theorem 1 read in terms of probabilities, a corollary of
  preservation:
  the probability the result gives to each class of equal simple types is the
  one the program's type gives it.

## Reading guide

First the typing of distribution values (rule (V)) and its interaction with
scaling and sums; then weakening, Lemma 18 and the typing of closing
substitutions; then the `let` case of preservation (`letRes_assembly`) and
Lemma 19; last the reducibility predicate, the fundamental lemma and the three
results.
-/

namespace GradualProb.SPLC

open scoped BigOperators
open Classical
open GradualProb.CouplingLemma

/-! ## Typing of distribution values (rule (V)) -/

/-- `DistValHasTy V τs`: every outcome of `V` is a closed value of the simple
type `τs i` (the premises of rule (V)). -/
def DistValHasTy (V : DistVal) (τs : Fin V.n → Ty) : Prop :=
  ∀ i, HasTyV [] (V.val i) (τs i)

/-- The distribution type that rule (V) assigns to a distribution value whose
outcomes have types `τs`: `{{τsᵢ ^ pᵢ}}`, with the value's own probabilities. -/
def DistVal.tyD (V : DistVal) (τs : Fin V.n → Ty) : DTy :=
  .dist (List.ofFn fun i => (τs i, GProb.q (V.mass i)))

/-- An equality `EqD (V.tyD τs) (.dist es)`, unfolded with the lifting and the
coverage clauses indexed by the outcomes of `V` (`eqD_ofFn_iff`). -/
theorem eqD_tyD_inv {V : DistVal} {τs : Fin V.n → Ty} {es : List (Ty × GProb)}
    (h : EqD (V.tyD τs) (.dist es)) :
    Lift (fun i j => EqTy (τs i) (es.get j).1) V.mass (fun j => pval (es.get j).2) ∧
      (∀ i, ∃ j, EqTy (τs i) (es.get j).1) ∧
      (∀ j, ∃ i, EqTy (τs i) (es.get j).1) := by
  rw [← List.ofFn_get es] at h
  exact eqD_ofFn_iff.1 h

/-- Rule (V) on a Dirac distribution `{{v^1}}` gives the Dirac type `{τ^1}`. -/
@[simp] theorem tyD_point (v : Val) (τ : Ty) :
    (DistVal.point v).tyD (fun _ => τ) = .dist [(τ, .q 1)] := by
  simp [DistVal.tyD, DistVal.point, List.ofFn_succ]

/-- Rule (V) commutes with scaling: the type of `a · V` is `a` times the type of `V`. -/
theorem tyD_scale (a : ℝ) (V : DistVal) (τs : Fin V.n → Ty) :
    (V.scale a).tyD τs = scaleD a (V.tyD τs) := by
  simp only [DistVal.tyD, DistVal.scale, scaleD, List.map_ofFn]
  congr 1

/-- Rule (V) commutes with sums: the type of `V1 + V2` is the sum of their types. -/
theorem tyD_append (V1 V2 : DistVal) (τs1 : Fin V1.n → Ty) (τs2 : Fin V2.n → Ty) :
    (V1.append V2).tyD (Fin.append τs1 τs2) = addD (V1.tyD τs1) (V2.tyD τs2) := by
  simp only [DistVal.tyD, DistVal.append, addD]
  rw [← List.ofFn_fin_append]
  congr 2
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [Fin.append_left]
  · simp [Fin.append_right]

/-! ## Typed distribution values -/

/-- A distribution value together with a simple type for each outcome, so that
scaling and sums act on values and types at once. -/
structure TypedDistVal where
  V : DistVal
  ty : Fin V.n → Ty

namespace TypedDistVal

/-- The distribution type of a typed distribution value (rule (V)). -/
def tyD (X : TypedDistVal) : DTy := X.V.tyD X.ty

/-- Pointwise predicate over the outcomes and their types. -/
def All (P : Val → Ty → Prop) (X : TypedDistVal) : Prop := ∀ i, P (X.V.val i) (X.ty i)

/-- Scaling of a typed distribution value. -/
def scaleT (a : ℝ) (X : TypedDistVal) : TypedDistVal := ⟨X.V.scale a, X.ty⟩
/-- Sum of two typed distribution values. -/
def appendT (X Y : TypedDistVal) : TypedDistVal := ⟨X.V.append Y.V, Fin.append X.ty Y.ty⟩
/-- Weighted sum of a list of typed distribution values. -/
def wsumListT : List (ℝ × TypedDistVal) → TypedDistVal
  | [] => ⟨⟨0, Fin.elim0, Fin.elim0⟩, Fin.elim0⟩
  | (a, X) :: rest => appendT (scaleT a X) (wsumListT rest)
/-- Weighted sum of a finite family of typed distribution values. -/
def wsumT {K : ℕ} (cells : Fin K → ℝ × TypedDistVal) : TypedDistVal := wsumListT (List.ofFn cells)

/-- The type of a scaled typed distribution value is the scaled type. -/
theorem tyD_scaleT (a : ℝ) (X : TypedDistVal) : (scaleT a X).tyD = scaleD a X.tyD :=
  tyD_scale a X.V X.ty

/-- The type of a sum of typed distribution values is the sum of their types. -/
theorem tyD_appendT (X Y : TypedDistVal) : (appendT X Y).tyD = addD X.tyD Y.tyD :=
  tyD_append X.V Y.V X.ty Y.ty

/-- The empty weighted sum has the empty distribution type. -/
theorem tyD_nil : (wsumListT []).tyD = .dist [] := by
  simp [wsumListT, tyD, DistVal.tyD]

/-- The type of a weighted sum of typed distribution values is the weighted sum
of their types. -/
theorem tyD_wsumListT : ∀ (L : List (ℝ × TypedDistVal)),
    (wsumListT L).tyD = sumScaledList (L.map fun c => (c.1, c.2.tyD))
  | [] => tyD_nil
  | (a, X) :: rest => by
      show (appendT (scaleT a X) (wsumListT rest)).tyD
        = addD (scaleD a X.tyD) (sumScaledList (rest.map fun c => (c.1, c.2.tyD)))
      rw [tyD_appendT, tyD_scaleT, tyD_wsumListT rest]

/-- The type of a weighted sum of a finite family of typed distribution values is
the weighted sum of their types. -/
theorem tyD_wsumT {K : ℕ} (cells : Fin K → ℝ × TypedDistVal) :
    (wsumT cells).tyD = sumScaledList (List.ofFn fun j => ((cells j).1, (cells j).2.tyD)) := by
  unfold wsumT
  rw [tyD_wsumListT, List.map_ofFn]
  rfl

/-- The underlying distribution value of a weighted sum of typed distribution
values is the weighted sum of the underlying values. -/
theorem V_wsumListT : ∀ (L : List (ℝ × TypedDistVal)),
    (wsumListT L).V = DistVal.wsumList (L.map fun c => (c.1, c.2.V))
  | [] => rfl
  | (a, X) :: rest => by
      show ((scaleT a X).V.append (wsumListT rest).V) = _
      rw [V_wsumListT rest]
      rfl

/-- The underlying distribution value of `wsumT` is the weighted sum of the
underlying values. -/
theorem V_wsumT {K : ℕ} (cells : Fin K → ℝ × TypedDistVal) :
    (wsumT cells).V = DistVal.wsum (fun j => ((cells j).1, (cells j).2.V)) := by
  unfold wsumT DistVal.wsum
  rw [V_wsumListT, List.map_ofFn]
  rfl

/-- A pointwise predicate holds after scaling. -/
theorem all_scaleT {P : Val → Ty → Prop} {a : ℝ} {X : TypedDistVal} (h : All P X) :
    All P (scaleT a X) := h

/-- A pointwise predicate that holds on two typed distribution values holds on
their sum. -/
theorem all_appendT {P : Val → Ty → Prop} {X Y : TypedDistVal} (hX : All P X) (hY : All P Y) :
    All P (appendT X Y) := by
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa [appendT, DistVal.append, Fin.append_left] using hX i
  · simpa [appendT, DistVal.append, Fin.append_right] using hY i

/-- A pointwise predicate that holds on every summand holds on the weighted sum
of a list. -/
theorem all_wsumListT {P : Val → Ty → Prop} : ∀ (L : List (ℝ × TypedDistVal)),
    (∀ c ∈ L, All P c.2) → All P (wsumListT L)
  | [], _ => fun i => Fin.elim0 i
  | (a, X) :: rest, h =>
      all_appendT (all_scaleT (h (a, X) (List.mem_cons_self)))
        (all_wsumListT rest (fun c hc => h c (List.mem_cons_of_mem _ hc)))

/-- A pointwise predicate that holds on every summand holds on the weighted sum
of a finite family. -/
theorem all_wsumT {P : Val → Ty → Prop} {K : ℕ} (cells : Fin K → ℝ × TypedDistVal)
    (h : ∀ j, All P (cells j).2) : All P (wsumT cells) := by
  refine all_wsumListT _ ?_
  intro c hc
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
  exact h j

end TypedDistVal

/-! ## Free variables and weakening -/

/-- The empty context is static. -/
theorem ctxStatic_nil : CtxStatic [] := List.forall_mem_nil _
/-- The empty context is well-formed. -/
theorem ctxWf_nil : CtxWf [] := List.forall_mem_nil _

/-- The prefix of a static context is static. -/
theorem ctxStatic_append_left {Δ Γ : Ctx} (h : CtxStatic (Δ ++ Γ)) : CtxStatic Δ :=
  (List.forall_mem_append.1 h).1
/-- Removing a binding from a static context leaves a static context. -/
theorem ctxStatic_append_tail {Δ Γ : Ctx} {τ : Ty} (h : CtxStatic (Δ ++ τ :: Γ)) :
    CtxStatic (Δ ++ Γ) :=
  List.forall_mem_append.2 ⟨(List.forall_mem_append.1 h).1,
    (List.forall_mem_cons.1 (List.forall_mem_append.1 h).2).2⟩
/-- Removing a binding from a well-formed context leaves a well-formed context. -/
theorem ctxWf_append_tail {Δ Γ : Ctx} {τ : Ty} (h : CtxWf (Δ ++ τ :: Γ)) :
    CtxWf (Δ ++ Γ) :=
  List.forall_mem_append.2 ⟨(List.forall_mem_append.1 h).1,
    (List.forall_mem_cons.1 (List.forall_mem_append.1 h).2).2⟩

mutual
/-- A well-typed value has its free variables below the context length. -/
theorem hasTy_fvBelow_val : ∀ {Γ v τ}, HasTyV Γ v τ → CtxWf Γ → v.FvBelow Γ.length
  | _, _, _, .var hx, _ => (List.getElem?_eq_some_iff.1 hx).1
  | _, _, _, .real, _ => trivial
  | _, _, _, .bool, _ => trivial
  | _, _, _, .lam hm hτ, hΓ => hasTy_fvBelow_tm hm (ctxWf_cons hτ hΓ)
/-- A well-typed term has its free variables below the context length (the
`let` case reads the bound for the body off entry `0`, which exists because the
bound term type has total probability `1`). -/
theorem hasTy_fvBelow_tm : ∀ {Γ m T}, HasTyT Γ m T → CtxWf Γ → m.FvBelow Γ.length
  | _, _, _, .val hv, hΓ => hasTy_fvBelow_val hv hΓ
  | _, _, _, .app hv hw _, hΓ => ⟨hasTy_fvBelow_val hv hΓ, hasTy_fvBelow_val hw hΓ⟩
  | _, _, _, @HasTyT.letin _ _ _ es _ hm hF, hΓ => by
      refine ⟨hasTy_fvBelow_tm hm hΓ, ?_⟩
      have hw := wfDTy_dist_inv (wf_tm hm hΓ)
      have hne : es ≠ [] := fun h => by
        subst h; exact absurd hw.2 (by simp [pmass])
      have h0 : 0 < es.length := List.length_pos_of_ne_nil hne
      exact hasTy_fvBelow_tm (hF ⟨0, h0⟩)
        (ctxWf_cons (hw.1 _ (List.get_mem es ⟨0, h0⟩)) hΓ)
  | _, _, _, .choice hm hn, hΓ => ⟨hasTy_fvBelow_tm hm hΓ, hasTy_fvBelow_tm hn hΓ⟩
  | _, _, _, .ascT (m := m') hm _ _, hΓ => hasTy_fvBelow_tm (m := m') hm hΓ
  | _, _, _, .ascV hv _ _, hΓ => hasTy_fvBelow_val hv hΓ
  | _, _, _, .add hv _ hw _, hΓ => ⟨hasTy_fvBelow_val hv hΓ, hasTy_fvBelow_val hw hΓ⟩
  | _, _, _, .ite hv _ hm hn _, hΓ =>
      ⟨hasTy_fvBelow_val hv hΓ, hasTy_fvBelow_tm hm hΓ, hasTy_fvBelow_tm hn hΓ⟩
end

/-- A closed well-typed value is closed. -/
theorem hasTy_closed_val {v : Val} {τ : Ty} (h : HasTyV [] v τ) : v.FvBelow 0 :=
  hasTy_fvBelow_val h ctxWf_nil

mutual
/-- Weakening by appending to the end of the context (the outermost
bindings). -/
theorem hasTy_wk_val : ∀ {Γ v τ} (Δ : Ctx), HasTyV Γ v τ → HasTyV (Γ ++ Δ) v τ
  | _, _, _, Δ, .var hx => .var (by
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hx).1]; exact hx)
  | _, _, _, _, .real => .real
  | _, _, _, _, .bool => .bool
  | _, _, _, Δ, .lam hm hτ => .lam (hasTy_wk_tm Δ hm) hτ
/-- Weakening for terms: if `Γ ⊢ₛ m : T`, then `Γ, Δ ⊢ₛ m : T`, with `Δ` appended
at the end of the context (the outermost bindings). -/
theorem hasTy_wk_tm : ∀ {Γ m T} (Δ : Ctx), HasTyT Γ m T → HasTyT (Γ ++ Δ) m T
  | _, _, _, Δ, .val hv => .val (hasTy_wk_val Δ hv)
  | _, _, _, Δ, .app hv hw hc => .app (hasTy_wk_val Δ hv) (hasTy_wk_val Δ hw) hc
  | _, _, _, Δ, .letin hm hF => .letin (hasTy_wk_tm Δ hm) (fun i => hasTy_wk_tm Δ (hF i))
  | _, _, _, Δ, .choice hm hn => .choice (hasTy_wk_tm Δ hm) (hasTy_wk_tm Δ hn)
  | _, _, _, Δ, .ascT hm hc hw => .ascT (hasTy_wk_tm Δ hm) hc hw
  | _, _, _, Δ, .ascV hv hc hw => .ascV (hasTy_wk_val Δ hv) hc hw
  | _, _, _, Δ, .add hv h1 hw h2 => .add (hasTy_wk_val Δ hv) h1 (hasTy_wk_val Δ hw) h2
  | _, _, _, Δ, .ite hv hc hm hn h12 =>
      .ite (hasTy_wk_val Δ hv) hc (hasTy_wk_tm Δ hm) (hasTy_wk_tm Δ hn) h12
end

/-! ## Lemma 18: substitution modulo equality -/

/-- The body types of a `let` are equal at equal entries (`det_eq_tm`). -/
theorem let_body_eq {Γ : Ctx} {n : Tm} {es : List (Ty × GProb)} {T : Fin es.length → DTy}
    (hes : IsStaticEntries es) (hesW : WfEntries es)
    (hF : ∀ i, HasTyT ((es.get i).1 :: Γ) n (T i)) (hsn : IsStaticTm n)
    (hΓs : CtxStatic Γ) (hΓw : CtxWf Γ) :
    ∀ j j', EqTy (es.get j).1 (es.get j').1 → EqD (T j) (T j') := fun j j' hceq =>
  det_eq_tm (hF j) (hF j') (.cons hceq (eqCtx_refl hΓs))
    (ctxStatic_cons (isStaticEntries_get_ty hes j) hΓs)
    (ctxStatic_cons (isStaticEntries_get_ty hes j') hΓs)
    (ctxWf_cons (hesW _ (List.get_mem es j)) hΓw)
    (ctxWf_cons (hesW _ (List.get_mem es j')) hΓw) hsn

mutual
/-- Lemma 18 (substitution modulo equality), item 1: substituting a closed
value `w : τ'` with `τ'` equal to `τ` for the variable at position `Γ1.length`
(of type `τ`), and replacing the bindings `Γ1` inside it by pointwise equal ones
`Γ1'`, yields a value whose type is equal to the original one.  In the article's
notation `Γ1` is `Δ` and `Γ2` is `Γ`. -/
theorem subst_val : ∀ {Γ1 Γ2 : Ctx} {τ : Ty} {v : Val} {σ : Ty},
    Γ1 ++ τ :: Γ2 ⊢ₛ v : σ → IsStaticVal v →
    CtxStatic (Γ1 ++ τ :: Γ2) → CtxWf (Γ1 ++ τ :: Γ2) →
    ∀ {Γ1' : Ctx} {w : Val} {τ' : Ty}, EqCtx Γ1 Γ1' →
    ⊢ₛ w : τ' → τ' =ₛ τ →
    ∃ σ', Γ1' ++ Γ2 ⊢ₛ v.subst Γ1.length w : σ' ∧ σ' =ₛ σ
  | Γ1, Γ2, τ, _, σ, .var (x := x) hx, _, hΓs, _, Γ1', w, τ', hctx, hw, hceq => by
      have hlen : Γ1.length = Γ1'.length := List.Forall₂.length_eq hctx
      rcases Nat.lt_trichotomy x Γ1.length with hlt | heq | hgt
      · -- below the substituted position: read the replaced bindings
        simp only [Val.subst, if_neg (by omega : ¬ x = Γ1.length),
          if_neg (by omega : ¬ x > Γ1.length)]
        rw [List.getElem?_append_left hlt] at hx
        obtain ⟨σ', hx', hc⟩ := eqCtx_getElem hctx hx
        refine ⟨σ', .var ?_, EqTy.symm hc⟩
        rw [List.getElem?_append_left (by omega)]
        exact hx'
      · -- the substituted variable itself
        subst heq
        simp only [Val.subst]
        rw [List.getElem?_append_right (le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨τ', hasTy_wk_val (Γ1' ++ Γ2) hw, hceq⟩
      · -- above: shift down, same type
        simp only [Val.subst, if_neg (by omega : ¬ x = Γ1.length), if_pos hgt]
        rw [List.getElem?_append_right (by omega)] at hx
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hgt
        have hidx : x - Γ1.length = d + 1 := by omega
        rw [hidx, List.getElem?_cons_succ] at hx
        refine ⟨σ, .var ?_, EqTy.refl (hΓs σ ?_)⟩
        · rw [List.getElem?_append_right (by omega)]
          have : x - 1 - Γ1'.length = d := by omega
          rw [this]; exact hx
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_of_getElem? hx))
  | _, _, _, _, _, .real, _, _, _, _, _, _, _, _, _ => ⟨.real, .real, .real⟩
  | _, _, _, _, _, .bool, _, _, _, _, _, _, _, _, _ => ⟨.bool, .bool, .bool⟩
  | Γ1, Γ2, τ, _, _, .lam (τ := τ0) hm hτ0, hs, hΓs, hΓw, Γ1', w, τ', hctx, hw, hceq => by
      cases hs with
      | lam hsτ0 hsm =>
        simp only [Val.subst]
        rw [Val.rename_below (hasTy_closed_val hw) (le_refl 0)]
        obtain ⟨T', hm', hc⟩ := subst_tm (Γ1 := τ0 :: Γ1) hm hsm
          (ctxStatic_cons hsτ0 hΓs) (ctxWf_cons hτ0 hΓw)
          (Γ1' := τ0 :: Γ1') (.cons (EqTy.refl hsτ0) hctx) hw hceq
        exact ⟨.arrow τ0 T', .lam hm' hτ0, .arrow (EqTy.refl hsτ0) hc⟩
/-- Lemma 18 (substitution modulo equality), item 2: the statement of `subst_val`
for terms, whose type after the substitution is equal to the original one. -/
theorem subst_tm : ∀ {Γ1 Γ2 : Ctx} {τ : Ty} {m : Tm} {T : DTy},
    Γ1 ++ τ :: Γ2 ⊢ₛ m : T → IsStaticTm m →
    CtxStatic (Γ1 ++ τ :: Γ2) → CtxWf (Γ1 ++ τ :: Γ2) →
    ∀ {Γ1' : Ctx} {w : Val} {τ' : Ty}, EqCtx Γ1 Γ1' →
    ⊢ₛ w : τ' → τ' =ₛ τ →
    ∃ T', Γ1' ++ Γ2 ⊢ₛ m.subst Γ1.length w : T' ∧ T' =ₛ T
  | _, _, _, _, _, .val hv, hs, hΓs, hΓw, _, _, _, hctx, hw, hceq => by
      cases hs with
      | val hsv =>
        obtain ⟨σ', hv', hc⟩ := subst_val hv hsv hΓs hΓw hctx hw hceq
        exact ⟨_, .val hv', eqD_singleton hc⟩
  | _, _, _, _, _, .app hv hu hc, hs, hΓs, hΓw, _, _, _, hctx, hw, hceq => by
      cases hs with
      | app hsv hsu =>
        obtain ⟨σv, hv', hcv⟩ := subst_val hv hsv hΓs hΓw hctx hw hceq
        obtain ⟨σu, hu', hcu⟩ := subst_val hu hsu hΓs hΓw hctx hw hceq
        cases hcv with
        | arrow hs' hd' =>
          exact ⟨_, .app hv' hu' (EqTy.trans hs' (EqTy.trans hc (EqTy.symm hcu))), hd'⟩
  | Γ1, Γ2, τ, _, _, @HasTyT.letin _ _ n es T hm hF, hs, hΓs, hΓw, Γ1', w, τ', hctx, hw, hceq => by
      cases hs with
      | letin hsm hsn =>
        have hes : IsStaticEntries es := by
          exact (isStatic_tm hm hΓs hsm).entries
        have hesW := (wfDTy_dist_inv (wf_tm hm hΓw)).1
        have hbody := let_body_eq hes hesW hF hsn hΓs hΓw
        obtain ⟨Tm', hm', hceqm⟩ := subst_tm hm hsm hΓs hΓw hctx hw hceq
        cases Tm' with
        | dist es' =>
        choose fL hfL using hceqm.cov.1
        choose fR hfR using hceqm.cov.2
        have hcell : ∀ k' : Fin es'.length, ∃ T',
            HasTyT ((es'.get k').1 :: (Γ1' ++ Γ2)) (n.subst (Γ1.length + 1) w) T' ∧
            EqD T' (T (fL k')) := fun k' =>
          subst_tm (Γ1 := (es.get (fL k')).1 :: Γ1) (hF (fL k')) hsn
            (ctxStatic_cons (isStaticEntries_get_ty hes _) hΓs)
            (ctxWf_cons (hesW _ (List.get_mem es _)) hΓw)
            (Γ1' := (es'.get k').1 :: Γ1') (.cons (EqTy.symm (hfL k')) hctx) hw hceq
        choose T' hT' using hcell
        simp only [Tm.subst]
        rw [Val.rename_below (hasTy_closed_val hw) (le_refl 0)]
        refine ⟨letRes es' T', .letin hm' (fun k' => (hT' k').1), ?_⟩
        refine eqD_letRes (hceqm.coup.mono ?_) ?_ ?_
        · intro k' j hkj
          exact EqD.trans (hT' k').2
            (hbody _ _ (EqTy.trans (EqTy.symm (hfL k')) hkj))
        · intro k'
          exact ⟨fL k', (hT' k').2⟩
        · intro j
          exact ⟨fR j, EqD.trans (hT' (fR j)).2
            (hbody _ _ (EqTy.trans (EqTy.symm (hfL (fR j))) (hfR j)))⟩
  | _, _, _, _, _, .choice hm hn, hs, hΓs, hΓw, _, _, _, hctx, hw, hceq => by
      cases hs with
      | choice hp0 hp1 hsm hsn =>
        obtain ⟨T1', hm', h1⟩ := subst_tm hm hsm hΓs hΓw hctx hw hceq
        obtain ⟨T2', hn', h2⟩ := subst_tm hn hsn hΓs hΓw hctx hw hceq
        exact ⟨_, .choice hm' hn',
          eqD_add (eqD_scale hp0 h1) (eqD_scale (by linarith) h2)⟩
  | _, _, _, _, _, .ascT hm hcT hwf, hs, hΓs, hΓw, _, _, _, hctx, hw, hceq => by
      cases hs with
      | ascT hsm hsT =>
        obtain ⟨T'', hm', h⟩ := subst_tm hm hsm hΓs hΓw hctx hw hceq
        exact ⟨_, .ascT hm' (EqD.trans h hcT) hwf, EqD.refl hsT⟩
  | _, _, _, _, _, .ascV hv hcτ hwf, hs, hΓs, hΓw, _, _, _, hctx, hw, hceq => by
      cases hs with
      | ascV hsv hsτ =>
        obtain ⟨σ', hv', h⟩ := subst_val hv hsv hΓs hΓw hctx hw hceq
        exact ⟨_, .ascV hv' (EqTy.trans h hcτ) hwf,
          EqD.refl (IsStaticDTy.point hsτ)⟩
  | _, _, _, _, _, .add hv h1 hu h2, hs, hΓs, hΓw, _, _, _, hctx, hw, hceq => by
      cases hs with
      | add hsv hsu =>
        obtain ⟨σv, hv', hcv⟩ := subst_val hv hsv hΓs hΓw hctx hw hceq
        obtain ⟨σu, hu', hcu⟩ := subst_val hu hsu hΓs hΓw hctx hw hceq
        exact ⟨_, .add hv' (EqTy.trans hcv h1) hu' (EqTy.trans hcu h2),
          EqD.refl (IsStaticDTy.point .real)⟩
  | _, _, _, _, _, .ite hv hcb hm hn h12, hs, hΓs, hΓw, _, _, _, hctx, hw, hceq => by
      cases hs with
      | ite hsv hsm hsn =>
        obtain ⟨σv, hv', hcv⟩ := subst_val hv hsv hΓs hΓw hctx hw hceq
        obtain ⟨T1', hm', h1⟩ := subst_tm hm hsm hΓs hΓw hctx hw hceq
        obtain ⟨T2', hn', h2⟩ := subst_tm hn hsn hΓs hΓw hctx hw hceq
        exact ⟨_, .ite hv' (EqTy.trans hcv hcb) hm' hn'
            (EqD.trans h1 (EqD.trans h12 (EqD.symm h2))),
          h1⟩
end

/-- The case of `subst_tm` (Lemma 18) for a body with a single bound variable,
as in the reduction rules for application and `let`. -/
theorem subst0_tm {τ : Ty} {m : Tm} {T : DTy} (hm : HasTyT [τ] m T) (hsm : IsStaticTm m)
    (hsτ : IsStaticTy τ) (hwτ : WfTy τ) {w : Val} {τ' : Ty}
    (hw : HasTyV [] w τ') (hceq : EqTy τ' τ) :
    ∃ T', HasTyT [] (m.subst0 w) T' ∧ EqD T' T :=
  subst_tm (Γ1 := []) (Γ2 := []) hm hsm (ctxStatic_cons hsτ ctxStatic_nil)
    (ctxWf_cons hwτ ctxWf_nil) (Γ1' := []) .nil hw hceq

/-! ## Typing of closing substitutions -/

/-- Typed closing environments: closed static values whose types are equal to
the types of the context. -/
def EnvTy (Γ : Ctx) (ρ : List Val) : Prop :=
  List.Forall₂ (fun τ v => IsStaticVal v ∧ ∃ τ', HasTyV [] v τ' ∧ EqTy τ' τ) Γ ρ

/-- The values of a typed closing environment are static. -/
theorem envTy_isStaticVal : ∀ {Γ : Ctx} {ρ : List Val}, EnvTy Γ ρ → ∀ v ∈ ρ, IsStaticVal v
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons h ht, v, hv => by
      rcases List.mem_cons.1 hv with rfl | hm
      · exact h.1
      · exact envTy_isStaticVal ht v hm

/-- The values of a typed closing environment are closed. -/
theorem envTy_closed : ∀ {Γ : Ctx} {ρ : List Val}, EnvTy Γ ρ → ∀ v ∈ ρ, v.FvBelow 0
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons h ht, v, hv => by
      rcases List.mem_cons.1 hv with rfl | hm
      · obtain ⟨_, τ', hτ', _⟩ := h
        exact hasTy_closed_val hτ'
      · exact envTy_closed ht v hm


mutual
/-- Closing the outer bindings `Γ` of a static value typed under `Δ ++ Γ` with a
typed environment for `Γ` gives a value typed under `Δ` at an equal type. -/
theorem hasTy_closeAt_val : ∀ {ρ : List Val} {Γ : Ctx}, EnvTy Γ ρ →
    ∀ {Δ : Ctx} {v : Val} {σ : Ty},
    HasTyV (Δ ++ Γ) v σ → IsStaticVal v → CtxStatic (Δ ++ Γ) → CtxWf (Δ ++ Γ) →
    ∃ σ', HasTyV Δ (v.closeAt Δ.length ρ) σ' ∧ EqTy σ' σ
  | [], [], .nil, Δ, v, σ, hv, hsv, hΓs, _ => by
      rw [List.append_nil] at hv hΓs
      rw [Val.closeAt_nil]
      exact ⟨σ, hv, EqTy.refl (isStatic_val hv hΓs hsv)⟩
  | _ :: ρ, _ :: Γ, .cons ⟨hsw, τ', hw, hc⟩ ht, Δ, v, σ, hv, hsv, hΓs, hΓw => by
      obtain ⟨σ1, hv1, hc1⟩ := subst_val hv hsv hΓs hΓw (eqCtx_refl (ctxStatic_append_left hΓs))
        hw hc
      rw [Val.closeAt_cons (hasTy_closed_val hw)]
      obtain ⟨σ2, hv2, hc2⟩ := hasTy_closeAt_val ht hv1 (isStaticVal_subst hsv hsw)
        (ctxStatic_append_tail hΓs) (ctxWf_append_tail hΓw)
      exact ⟨σ2, hv2, EqTy.trans hc2 hc1⟩
end

/-- Closing a static value typed under `Γ` with a typed environment for `Γ` gives
a closed value of an equal type. -/
theorem hasTy_close_val {ρ : List Val} {Γ : Ctx} (hρ : EnvTy Γ ρ) {v : Val} {σ : Ty}
    (hv : HasTyV Γ v σ) (hsv : IsStaticVal v) (hΓs : CtxStatic Γ) (hΓw : CtxWf Γ) :
    ∃ σ', HasTyV [] (v.close ρ) σ' ∧ EqTy σ' σ :=
  hasTy_closeAt_val hρ (Δ := []) hv hsv hΓs hΓw


/-! ## The `let` case of preservation -/

/-- The `let` case of preservation.  Let the bound term reduce to `V`, with
`V.tyD τs` equal to `{{es}}`, and let the bijection `cells` enumerate its
outcomes.  If the body reduced with outcome `cells j` has a type equal to
`T (f j)`, where `f j` is an entry equal to the outcome's type, then the
weighted sum has a type equal to `letRes es T`.  Body types at equal entries
are equal (`hbody`).  The lifting of the equality `hceq` is reindexed along
`cells` (`Lift.reindex`) and the two weighted sums are related by
`eqD_sumScaled`. -/
theorem letRes_assembly {V : DistVal} {τs : Fin V.n → Ty} {es : List (Ty × GProb)}
    {T : Fin es.length → DTy} {K : ℕ} {cells : Fin K → Fin V.n}
    (hinj : Function.Injective cells) (hsurj : ∀ i, ∃ j, cells j = i)
    (hceq : EqD (V.tyD τs) (.dist es))
    (hbody : ∀ j j', EqTy (es.get j).1 (es.get j').1 → EqD (T j) (T j'))
    {XW : Fin K → TypedDistVal} (f : Fin K → Fin es.length)
    (hf : ∀ j, EqTy (τs (cells j)) (es.get (f j)).1)
    (hXW : ∀ j, EqD (XW j).tyD (T (f j))) :
    EqD (TypedDistVal.wsumT (fun j => (V.mass (cells j), XW j))).tyD (letRes es T) := by
  obtain ⟨hl, -, hcovR⟩ := eqD_tyD_inv hceq
  have hstep : ∀ j j', EqTy (τs (cells j)) (es.get j').1 → EqD (XW j).tyD (T j') :=
    fun j j' h => EqD.trans (hXW j) (hbody _ _ (EqTy.trans (EqTy.symm (hf j)) h))
  rw [TypedDistVal.tyD_wsumT]
  refine eqD_sumScaled
    ((hl.reindex (Equiv.ofBijective cells ⟨hinj, hsurj⟩) (Equiv.refl _)).mono hstep)
    (fun j => ⟨f j, hXW j⟩) fun j' => ?_
  obtain ⟨i, hi⟩ := hcovR j'
  obtain ⟨j, rfl⟩ := hsurj i
  exact ⟨j, hstep j j' hi⟩

/-! ## Lemma 19: preservation -/

/-- The type of the typed distribution value `⟨V, τs⟩` is `V.tyD τs`. -/
@[simp] theorem TypedDistVal.tyD_mk (V : DistVal) (τs : Fin V.n → Ty) :
    TypedDistVal.tyD ⟨V, τs⟩ = V.tyD τs := rfl

/-- Preservation, stated with a typed distribution value: the result of
reducing a closed well-typed static program, with a type for each outcome,
has a type equal to the program's type. -/
theorem preservation_core : ∀ {m : Tm} {k : ℕ} {V : DistVal} {T : DTy},
    Red m k V → HasTyT [] m T → IsStaticTm m →
    ∃ X : TypedDistVal, X.V = V ∧ X.All (fun v τ => HasTyV [] v τ) ∧ EqD X.tyD T
  | _, _, _, _, .sv, ht, hs => by
      cases ht with
      | val hv =>
        cases hs with
        | val hsv =>
          refine ⟨⟨DistVal.point _, fun _ => _⟩, rfl, fun _ => hv, ?_⟩
          rw [TypedDistVal.tyD_mk, tyD_point]
          exact EqD.refl (IsStaticDTy.point (isStatic_val hv ctxStatic_nil hsv))
  | _, _, _, _, .sapp h, ht, hs => by
      cases ht with
      | app hv hw hc =>
        cases hv with
        | lam hm hτ =>
          cases hs with
          | app hsv hsw =>
            cases hsv with
            | lam hsτ hsm =>
              obtain ⟨T', hm', hc'⟩ := subst0_tm hm hsm hsτ hτ hw (EqTy.symm hc)
              obtain ⟨X, hXV, hty, hceq⟩ :=
                preservation_core h hm' (isStaticTm_subst hsm hsw)
              exact ⟨X, hXV, hty, EqD.trans hceq hc'⟩
  | _, _, _, _, .schoice (p := p) h1 h2, ht, hs => by
      cases ht with
      | choice hm hn =>
        cases hs with
        | choice hp0 hp1 hsm hsn =>
          obtain ⟨X1, rfl, hty1, hc1⟩ := preservation_core h1 hm hsm
          obtain ⟨X2, rfl, hty2, hc2⟩ := preservation_core h2 hn hsn
          refine ⟨TypedDistVal.appendT (TypedDistVal.scaleT p X1) (TypedDistVal.scaleT (1 - p) X2), rfl,
            TypedDistVal.all_appendT (TypedDistVal.all_scaleT hty1) (TypedDistVal.all_scaleT hty2), ?_⟩
          rw [TypedDistVal.tyD_appendT, TypedDistVal.tyD_scaleT, TypedDistVal.tyD_scaleT]
          exact eqD_add (eqD_scale hp0 hc1) (eqD_scale (by linarith) hc2)
  | _, _, _, _, .slet (cells := cells) (W := W) hm0 hinj hsurj hbody, ht, hs => by
      cases ht with
      | @letin _ _ n es T hm hF =>
        cases hs with
        | letin hsm hsn =>
          obtain ⟨X0, rfl, hty0, hceq0⟩ := preservation_core hm0 hm hsm
          have hes : IsStaticEntries es := by
            exact (isStatic_tm hm ctxStatic_nil hsm).entries
          have hesW := (wfDTy_dist_inv (wf_tm hm ctxWf_nil)).1
          have hbodyc := let_body_eq hes hesW hF hsn ctxStatic_nil ctxWf_nil
          obtain ⟨-, hcovL, -⟩ := eqD_tyD_inv hceq0
          choose f hf using fun j => hcovL (cells j)
          have hcell : ∀ j, ∃ Xj : TypedDistVal, Xj.V = W j ∧
              Xj.All (fun v τ => HasTyV [] v τ) ∧ EqD Xj.tyD (T (f j)) := by
            intro j
            obtain ⟨T', hn', hc'⟩ := subst0_tm (hF (f j)) hsn
              (isStaticEntries_get_ty hes _) (hesW _ (List.get_mem es _))
              (hty0 (cells j)) (hf j)
            obtain ⟨Xj, hXj, htyj, hcj⟩ :=
              preservation_core (hbody j) hn' (isStaticTm_subst hsn (red_static hm0 hsm _))
            exact ⟨Xj, hXj, htyj, EqD.trans hcj hc'⟩
          choose XW hXW using hcell
          refine ⟨TypedDistVal.wsumT (fun j => (X0.V.mass (cells j), XW j)), ?_,
            TypedDistVal.all_wsumT _ (fun j => (hXW j).2.1), ?_⟩
          · rw [TypedDistVal.V_wsumT]
            congr 1
            funext j
            rw [(hXW j).1]
          · exact letRes_assembly hinj hsurj hceq0 hbodyc f hf (fun j => (hXW j).2.2)
  | _, _, _, _, .sascV, ht, hs => by
      cases ht with
      | ascV hv hc _ =>
        refine ⟨⟨DistVal.point _, fun _ => _⟩, rfl, fun _ => hv, ?_⟩
        rw [TypedDistVal.tyD_mk, tyD_point]
        exact eqD_singleton hc
  | _, _, _, _, .sascT h, ht, hs => by
      cases ht with
      | ascT hm hc _ =>
        cases hs with
        | ascT hsm _ =>
          obtain ⟨X, hXV, hty, hceq⟩ := preservation_core h hm hsm
          exact ⟨X, hXV, hty, EqD.trans hceq hc⟩
  | _, _, _, _, .sadd, ht, _ => by
      cases ht with
      | add _ _ _ _ =>
        refine ⟨⟨DistVal.point _, fun _ => .real⟩, rfl, fun _ => .real, ?_⟩
        rw [TypedDistVal.tyD_mk, tyD_point]
        exact EqD.refl (IsStaticDTy.point .real)
  | _, _, _, _, .sit h, ht, hs => by
      cases ht with
      | ite _ _ hm hn h12 =>
        cases hs with
        | ite _ hsm hsn =>
          obtain ⟨X, hXV, hty, hceq⟩ := preservation_core h hm hsm
          exact ⟨X, hXV, hty, hceq⟩
  | _, _, _, _, .sif h, ht, hs => by
      cases ht with
      | ite _ _ hm hn h12 =>
        cases hs with
        | ite _ hsm hsn =>
          obtain ⟨X, hXV, hty, hceq⟩ := preservation_core h hn hsn
          exact ⟨X, hXV, hty, EqD.trans hceq (EqD.symm h12)⟩

/-- Lemma 19 (preservation): if `⊢ₛ m : T` and `m` reduces to `V`, then `V` is
typed by rule (V) at some `{{τsᵢ ^ pᵢ}}` equal to `T`. -/
theorem preservation {m : Tm} {T : DTy} {k : ℕ} {V : DistVal}
    (ht : ⊢ₛ m : T) (hs : IsStaticTm m) (hred : m ⇓ₛ[k] V) :
    ∃ τs : Fin V.n → Ty, DistValHasTy V τs ∧ V.tyD τs =ₛ T := by
  obtain ⟨X, hXV, hty, hceq⟩ := preservation_core hred ht hs
  subst hXV
  exact ⟨X.ty, hty, hceq⟩

/-! ## Lemma 20: termination

Tait's method, with the reducibility predicate `RedV τ v` indexed by the static
type `τ`.  The arrow clause quantifies over closed static arguments whose type
is equal to the domain and that are reducible at the domain, and asks the
application to reduce to a distribution value typed by rule (V) at a type equal
to the codomain, each of whose outcomes is reducible at every entry of the
codomain its type is equal to.  The recursion descends to the entries of the
codomain, so it terminates on the size of the type (`termination_by`);
invariance under equality of the index is the lemma `redV_eq`. -/

set_option linter.unusedVariables false in
/-- Lemma 20 (termination), the reducibility predicate: reducibility of a closed
static value at a static type (the clause for `?` is never used, since the types
of SPLC are static). -/
def RedV : Ty → Val → Prop
  | .real, _ => True
  | .bool, _ => True
  | .unk, _ => True
  | .arrow s (.dist es), v =>
      ∀ (w : Val) (τw : Ty), ⊢ₛ w : τw → IsStaticVal w → τw =ₛ s → RedV s w →
        ∃ (k : ℕ) (V : DistVal) (τs : Fin V.n → Ty),
          .app v w ⇓ₛ[k] V ∧ DistValHasTy V τs ∧ V.tyD τs =ₛ .dist es ∧
          ∀ (i : Fin V.n) (e : Ty × GProb), e ∈ es → τs i =ₛ e.1 → RedV e.1 (V.val i)
termination_by τ _ => sizeOf τ
decreasing_by
  all_goals simp_wf
  · omega
  · rename_i e he _
    have h1 := List.sizeOf_lt_of_mem he
    obtain ⟨a, b⟩ := e
    clear he
    simp at h1 ⊢
    omega

/-- Unfolding of `RedV` at an arrow type with an explicit distribution codomain. -/
theorem redV_arrow {s : Ty} {es : List (Ty × GProb)} {v : Val} :
    RedV (.arrow s (.dist es)) v ↔
      ∀ (w : Val) (τw : Ty), ⊢ₛ w : τw → IsStaticVal w → τw =ₛ s → RedV s w →
        ∃ (k : ℕ) (V : DistVal) (τs : Fin V.n → Ty),
          .app v w ⇓ₛ[k] V ∧ DistValHasTy V τs ∧ V.tyD τs =ₛ .dist es ∧
          ∀ (i : Fin V.n) (e : Ty × GProb), e ∈ es → τs i =ₛ e.1 → RedV e.1 (V.val i) := by
  rw [RedV]

/-- Unfolding of `RedV` at an arrow type, for any codomain. -/
theorem redV_arrow' {s : Ty} {d : DTy} {v : Val} :
    RedV (.arrow s d) v ↔
      ∀ (w : Val) (τw : Ty), ⊢ₛ w : τw → IsStaticVal w → τw =ₛ s → RedV s w →
        ∃ (k : ℕ) (V : DistVal) (τs : Fin V.n → Ty),
          .app v w ⇓ₛ[k] V ∧ DistValHasTy V τs ∧ V.tyD τs =ₛ d ∧
          ∀ (i : Fin V.n) (e : Ty × GProb), e ∈ dentries d → τs i =ₛ e.1 →
            RedV e.1 (V.val i) := by
  cases d with
  | dist es => exact redV_arrow

/-- Every value is reducible at `.real`. -/
theorem redV_real {v : Val} : RedV .real v := by rw [RedV]; trivial
/-- Every value is reducible at `.bool`. -/
theorem redV_bool {v : Val} : RedV .bool v := by rw [RedV]; trivial

mutual
/-- Reducibility is invariant under equality of the index (both directions at
once, since the arrow clause is contravariant in the domain). -/
theorem redV_eq : ∀ {τ τ' : Ty}, EqTy τ τ' → ∀ v, (RedV τ v ↔ RedV τ' v)
  | _, _, .real, _ => Iff.rfl
  | _, _, .bool, _ => Iff.rfl
  | _, _, .arrow hs hd, v => by
      rw [redV_arrow', redV_arrow']
      constructor
      · intro H w τw hw hsw hc hr
        obtain ⟨k, V, τs, hred, hty, hceq, hout⟩ :=
          H w τw hw hsw (EqTy.trans hc (EqTy.symm hs)) ((redV_eq hs w).2 hr)
        exact ⟨k, V, τs, hred, hty, EqD.trans hceq hd,
          fun i => (redD_eq hd (V.val i) (τs i)).1 (hout i)⟩
      · intro H w τw hw hsw hc hr
        obtain ⟨k, V, τs, hred, hty, hceq, hout⟩ :=
          H w τw hw hsw (EqTy.trans hc hs) ((redV_eq hs w).1 hr)
        exact ⟨k, V, τs, hred, hty, EqD.trans hceq (EqD.symm hd),
          fun i => (redD_eq hd (V.val i) (τs i)).2 (hout i)⟩
/-- The outcome clause is invariant under equality of the codomain: each entry
on one side is equal to an entry on the other (coverage), and `redV_eq`
transports along it. -/
theorem redD_eq : ∀ {T T' : DTy}, EqD T T' → ∀ (v : Val) (σ : Ty),
    ((∀ e ∈ dentries T, EqTy σ e.1 → RedV e.1 v) ↔
      (∀ e ∈ dentries T', EqTy σ e.1 → RedV e.1 v))
  | _, _, .dist _ fL fR _ _ hfL hfR, v, σ => by
      constructor
      · intro H e he hc
        obtain ⟨j, rfl⟩ := List.mem_iff_get.1 he
        exact (redV_eq (hfR j) v).1
          (H _ (List.get_mem _ (fR j)) (EqTy.trans hc (EqTy.symm (hfR j))))
      · intro H e he hc
        obtain ⟨i, rfl⟩ := List.mem_iff_get.1 he
        exact (redV_eq (hfL i) v).2
          (H _ (List.get_mem _ (fL i)) (EqTy.trans hc (hfL i)))
end

/-- From the outcome condition of the arrow clause to reducibility at the
outcome's own type (coverage picks an equal entry, `redV_eq` transports). -/
theorem redV_of_entries {V : DistVal} {τs : Fin V.n → Ty} {d : DTy}
    (hceq : EqD (V.tyD τs) d)
    (hout : ∀ (i : Fin V.n) (e : Ty × GProb), e ∈ dentries d → EqTy (τs i) e.1 →
      RedV e.1 (V.val i)) :
    ∀ i, RedV (τs i) (V.val i) := by
  cases d with
  | dist es =>
    intro i
    obtain ⟨-, hcovL, -⟩ := eqD_tyD_inv hceq
    obtain ⟨j, hj⟩ := hcovL i
    exact (redV_eq hj _).2 (hout i _ (List.get_mem es j) hj)

/-! ### Canonical forms -/

/-- The only simple type equal to `.real` is `.real`. -/
theorem eqTy_real_inv : ∀ {τ : Ty}, EqTy τ .real → τ = .real
  | _, .real => rfl
/-- The only simple type equal to `.bool` is `.bool`. -/
theorem eqTy_bool_inv : ∀ {τ : Ty}, EqTy τ .bool → τ = .bool
  | _, .bool => rfl

/-- Canonical forms: a closed value of type `.real` is a real literal. -/
theorem canon_real {v : Val} (h : HasTyV [] v .real) : ∃ r, v = .real r := by
  cases h with
  | var hx => simp at hx
  | real => exact ⟨_, rfl⟩

/-- Canonical forms: a closed value of type `.bool` is a boolean literal. -/
theorem canon_bool {v : Val} (h : HasTyV [] v .bool) : ∃ b, v = .bool b := by
  cases h with
  | var hx => simp at hx
  | bool => exact ⟨_, rfl⟩

/-! ### Reducible environments and the fundamental lemma -/

/-- Reducible closing environments: closed static values whose types are equal
to the types of the context, and reducible at them. -/
def Env (Γ : Ctx) (ρ : List Val) : Prop :=
  List.Forall₂ (fun τ v => IsStaticVal v ∧ (∃ τ', HasTyV [] v τ' ∧ EqTy τ' τ) ∧ RedV τ v) Γ ρ

/-- A reducible closing environment is a typed closing environment. -/
theorem env_envTy {Γ : Ctx} {ρ : List Val} (h : Env Γ ρ) : EnvTy Γ ρ :=
  List.Forall₂.imp (fun _ _ h => ⟨h.1, h.2.1⟩) h

/-- A variable bound in `Γ` has a value in a reducible environment for `Γ`, and
that value is reducible at the variable's type. -/
theorem env_lookup : ∀ {Γ : Ctx} {ρ : List Val}, Env Γ ρ → ∀ {x : ℕ} {τ : Ty},
    Γ[x]? = some τ → ∃ h : x < ρ.length, RedV τ ρ[x]
  | _, _, .nil, x, τ, hx => by simp at hx
  | _, _, .cons hab htail, x, τ, hx => by
      cases x with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨by simp, hab.2.2⟩
      | succ n =>
        simp only [List.getElem?_cons_succ] at hx
        obtain ⟨h1, h2⟩ := env_lookup htail hx
        exact ⟨by simpa using h1, h2⟩

/-- Reducibility of a closed term at a distribution type `T`: it reduces to a
distribution value typed by rule (V) at a type equal to `T`, every outcome
reducible at its own type. -/
def RedT (T : DTy) (m : Tm) : Prop :=
  ∃ (k : ℕ) (V : DistVal) (τs : Fin V.n → Ty),
    m ⇓ₛ[k] V ∧ DistValHasTy V τs ∧ V.tyD τs =ₛ T ∧ ∀ i, RedV (τs i) (V.val i)

mutual
/-- Lemma 20 (termination), fundamental lemma for values: a well-typed static
value closed by a reducible environment is reducible at its type. -/
theorem fundamental_val : ∀ {Γ} {v : Val} {τ}, Γ ⊢ₛ v : τ → IsStaticVal v → CtxStatic Γ → CtxWf Γ →
    ∀ {ρ : List Val}, Env Γ ρ → RedV τ (v.close ρ)
  | _, _, _, .var (x := x) hx, _, _, _, ρ, hρ => by
      obtain ⟨hlt, hr⟩ := env_lookup hρ hx
      have h := Val.closeAt_var (ρ := ρ) (x := x) (k := 0) hlt
      rw [Nat.zero_add] at h
      show RedV _ ((Val.var x).closeAt 0 ρ)
      rw [h]
      exact hr
  | _, _, _, .real, _, _, _, _, _ => redV_real
  | _, _, _, .bool, _, _, _, _, _ => redV_bool
  | _, _, _, .lam (τ := τ0) hm hτ0, hs, hΓs, hΓw, ρ, hρ => by
      cases hs with
      | lam hsτ0 hsm =>
        have hcl := envTy_closed (env_envTy hρ)
        show RedV _ ((Val.lam τ0 _).closeAt 0 ρ)
        rw [Val.closeAt_lam, redV_arrow']
        intro w τw hw hsw hc hr
        have hρ' : Env (τ0 :: _) (w :: ρ) := .cons ⟨hsw, ⟨τw, hw, hc⟩, hr⟩ hρ
        obtain ⟨k, V, τs, hred, hty, hceq, hout⟩ :=
          fundamental_tm hm hsm (ctxStatic_cons hsτ0 hΓs) (ctxWf_cons hτ0 hΓw) hρ'
        refine ⟨k + 1, V, τs, ?_, hty, hceq, fun i e _ hce => (redV_eq hce _).1 (hout i)⟩
        apply Red.sapp
        show Red ((Tm.closeAt _ (0 + 1) ρ).subst 0 w) k V
        rw [Tm.closeAt_subst_comm hcl (hasTy_closed_val hw),
          ← Tm.closeAt_cons (hasTy_closed_val hw)]
        exact hred
/-- Lemma 20 (termination), fundamental lemma for terms: a well-typed static
term closed by a reducible environment is reducible at its type. -/
theorem fundamental_tm : ∀ {Γ} {m : Tm} {T}, Γ ⊢ₛ m : T → IsStaticTm m → CtxStatic Γ → CtxWf Γ →
    ∀ {ρ : List Val}, Env Γ ρ → RedT T (m.close ρ)
  | _, _, _, .val hv, hs, hΓs, hΓw, ρ, hρ => by
      cases hs with
      | val hsv =>
        have hr := fundamental_val hv hsv hΓs hΓw hρ
        obtain ⟨τ', hv', hc⟩ := hasTy_close_val (env_envTy hρ) hv hsv hΓs hΓw
        refine ⟨1, DistVal.point _, fun _ => τ', .sv, fun _ => hv', ?_,
          fun _ => (redV_eq hc _).2 hr⟩
        rw [tyD_point]
        exact eqD_singleton hc
  | _, _, _, .app hv hw hc, hs, hΓs, hΓw, ρ, hρ => by
      cases hs with
      | app hsv hsw =>
        have hrv := fundamental_val hv hsv hΓs hΓw hρ
        have hrw := fundamental_val hw hsw hΓs hΓw hρ
        obtain ⟨τw', hw', hcw⟩ := hasTy_close_val (env_envTy hρ) hw hsw hΓs hΓw
        rw [redV_arrow'] at hrv
        obtain ⟨k, V, τs, hred, hty, hceq, hout⟩ :=
          hrv _ τw' hw' (isStaticVal_closeAt hsw fun v hv =>
            ⟨envTy_isStaticVal (env_envTy hρ) v hv, envTy_closed (env_envTy hρ) v hv⟩)
            (EqTy.trans hcw (EqTy.symm hc)) ((redV_eq hc _).2 hrw)
        exact ⟨k, V, τs, hred, hty, hceq, redV_of_entries hceq hout⟩
  | _, _, _, @HasTyT.letin _ _ n es T hm hF, hs, hΓs, hΓw, ρ, hρ => by
      cases hs with
      | letin hsm hsn =>
        have hcl := envTy_closed (env_envTy hρ)
        have hes : IsStaticEntries es := by
          exact (isStatic_tm hm hΓs hsm).entries
        have hesW := (wfDTy_dist_inv (wf_tm hm hΓw)).1
        have hbodyc := let_body_eq hes hesW hF hsn hΓs hΓw
        obtain ⟨k1, V, τs, hred0, hty0, hceq0, hout0⟩ := fundamental_tm hm hsm hΓs hΓw hρ
        obtain ⟨-, hcovL, -⟩ := eqD_tyD_inv hceq0
        choose f hf using hcovL
        have hsv : ∀ i, IsStaticVal (V.val i) :=
          red_static hred0 (isStaticTm_closeAt hsm fun v hv =>
            ⟨envTy_isStaticVal (env_envTy hρ) v hv, hcl v hv⟩)
        have hcell : ∀ i, ∃ (k : ℕ) (X : TypedDistVal),
            Red ((n.closeAt (0 + 1) ρ).subst0 (V.val i)) k X.V ∧
            X.All (fun v τ => HasTyV [] v τ) ∧ EqD X.tyD (T (f i)) ∧
            X.All (fun v τ => RedV τ v) := by
          intro i
          have hρ' : Env ((es.get (f i)).1 :: _) (V.val i :: ρ) :=
            .cons ⟨hsv i, ⟨τs i, hty0 i, hf i⟩, (redV_eq (hf i) _).1 (hout0 i)⟩ hρ
          obtain ⟨k, W, τsW, hredW, htyW, hceqW, houtW⟩ :=
            fundamental_tm (hF (f i)) hsn (ctxStatic_cons (isStaticEntries_get_ty hes _) hΓs)
              (ctxWf_cons (hesW _ (List.get_mem es _)) hΓw) hρ'
          refine ⟨k, ⟨W, τsW⟩, ?_, htyW, hceqW, houtW⟩
          show Red ((Tm.closeAt _ (0 + 1) ρ).subst 0 (V.val i)) k W
          rw [Tm.closeAt_subst_comm hcl (hasTy_closed_val (hty0 i)),
            ← Tm.closeAt_cons (hasTy_closed_val (hty0 i))]
          exact hredW
        choose kk XW hredW htyW hceqW houtW using hcell
        have hW : ∀ i, Red ((n.closeAt (0 + 1) ρ).subst0 (V.val i))
            (Finset.univ.sup kk) (XW i).V :=
          fun i => red_index_mono (hredW i) (Finset.le_sup (Finset.mem_univ i))
        show RedT _ ((Tm.letin _ _).closeAt 0 ρ)
        rw [Tm.closeAt_letin]
        refine ⟨k1 + Finset.univ.sup kk + 1, (TypedDistVal.wsumT (fun j => (V.mass j, XW j))).V,
          (TypedDistVal.wsumT (fun j => (V.mass j, XW j))).ty, ?_,
          TypedDistVal.all_wsumT (P := fun v τ => HasTyV [] v τ) _ (fun j => htyW j),
          letRes_assembly (cells := id) Function.injective_id (fun i => ⟨i, rfl⟩)
            hceq0 hbodyc f hf hceqW,
          TypedDistVal.all_wsumT (P := fun v τ => RedV τ v) _ (fun j => houtW j)⟩
        rw [TypedDistVal.V_wsumT]
        exact Red.slet hred0 Function.injective_id (fun i => ⟨i, rfl⟩) hW
  | _, _, _, .choice (p := p) hm hn, hs, hΓs, hΓw, ρ, hρ => by
      cases hs with
      | choice hp0 hp1 hsm hsn =>
        obtain ⟨k1, V1, τs1, h1, hty1, hc1, hout1⟩ := fundamental_tm hm hsm hΓs hΓw hρ
        obtain ⟨k2, V2, τs2, h2, hty2, hc2, hout2⟩ := fundamental_tm hn hsn hΓs hΓw hρ
        refine ⟨k1 + k2 + 1,
          (TypedDistVal.appendT (TypedDistVal.scaleT p ⟨V1, τs1⟩) (TypedDistVal.scaleT (1 - p) ⟨V2, τs2⟩)).V,
          (TypedDistVal.appendT (TypedDistVal.scaleT p ⟨V1, τs1⟩) (TypedDistVal.scaleT (1 - p) ⟨V2, τs2⟩)).ty,
          .schoice h1 h2,
          TypedDistVal.all_appendT (P := fun v τ => HasTyV [] v τ)
            (X := TypedDistVal.scaleT p ⟨V1, τs1⟩) (Y := TypedDistVal.scaleT (1 - p) ⟨V2, τs2⟩) hty1 hty2,
          ?_,
          TypedDistVal.all_appendT (P := fun v τ => RedV τ v)
            (X := TypedDistVal.scaleT p ⟨V1, τs1⟩) (Y := TypedDistVal.scaleT (1 - p) ⟨V2, τs2⟩)
            hout1 hout2⟩
        show EqD (TypedDistVal.appendT (TypedDistVal.scaleT p ⟨V1, τs1⟩)
          (TypedDistVal.scaleT (1 - p) ⟨V2, τs2⟩)).tyD _
        rw [TypedDistVal.tyD_appendT, TypedDistVal.tyD_scaleT, TypedDistVal.tyD_scaleT]
        exact eqD_add (eqD_scale hp0 hc1) (eqD_scale (by linarith) hc2)
  | _, _, _, .ascT hm hc _, hs, hΓs, hΓw, ρ, hρ => by
      cases hs with
      | ascT hsm _ =>
        obtain ⟨k, V, τs, h, hty, hceq, hout⟩ := fundamental_tm hm hsm hΓs hΓw hρ
        exact ⟨k + 1, V, τs, .sascT h, hty, EqD.trans hceq hc, hout⟩
  | _, _, _, .ascV hv hc _, hs, hΓs, hΓw, ρ, hρ => by
      cases hs with
      | ascV hsv _ =>
        have hr := fundamental_val hv hsv hΓs hΓw hρ
        obtain ⟨τ'', hv', hc'⟩ := hasTy_close_val (env_envTy hρ) hv hsv hΓs hΓw
        refine ⟨1, DistVal.point _, fun _ => τ'', .sascV, fun _ => hv', ?_,
          fun _ => (redV_eq hc' _).2 hr⟩
        rw [tyD_point]
        exact eqD_singleton (EqTy.trans hc' hc)
  | _, _, _, .add (v := v) (w := w) hv h1 hw h2, hs, hΓs, hΓw, ρ, hρ => by
      cases hs with
      | add hsv hsw =>
        obtain ⟨τv', hv', hcv⟩ := hasTy_close_val (env_envTy hρ) hv hsv hΓs hΓw
        obtain ⟨τw', hw', hcw⟩ := hasTy_close_val (env_envTy hρ) hw hsw hΓs hΓw
        have ev := eqTy_real_inv (EqTy.trans hcv h1)
        have ew := eqTy_real_inv (EqTy.trans hcw h2)
        subst ev ew
        obtain ⟨r1, hr1⟩ := canon_real hv'
        obtain ⟨r2, hr2⟩ := canon_real hw'
        show RedT _ ((Tm.add _ _).closeAt 0 ρ)
        rw [Tm.closeAt_add, show v.closeAt 0 ρ = Val.real r1 from hr1,
          show w.closeAt 0 ρ = Val.real r2 from hr2]
        refine ⟨1, DistVal.point _, fun _ => .real, .sadd, fun _ => .real, ?_, fun _ => redV_real⟩
        rw [tyD_point]
        exact EqD.refl (IsStaticDTy.point .real)
  | _, _, _, .ite (v := v) hv hcb hm hn h12, hs, hΓs, hΓw, ρ, hρ => by
      cases hs with
      | ite hsv hsm hsn =>
        obtain ⟨τv', hv', hcv⟩ := hasTy_close_val (env_envTy hρ) hv hsv hΓs hΓw
        have eb := eqTy_bool_inv (EqTy.trans hcv hcb)
        subst eb
        obtain ⟨b, hb⟩ := canon_bool hv'
        show RedT _ ((Tm.ite _ _ _).closeAt 0 ρ)
        rw [Tm.closeAt_ite, show v.closeAt 0 ρ = Val.bool b from hb]
        cases b with
        | true =>
          obtain ⟨k, V, τs, h, hty, hceq, hout⟩ := fundamental_tm hm hsm hΓs hΓw hρ
          exact ⟨k + 1, V, τs, .sit h, hty, hceq, hout⟩
        | false =>
          obtain ⟨k, V, τs, h, hty, hceq, hout⟩ := fundamental_tm hn hsn hΓs hΓw hρ
          exact ⟨k + 1, V, τs, .sif h, hty, EqD.trans hceq (EqD.symm h12), hout⟩
end

/-! ## Termination, type safety and its reading in probabilities -/

/-- Lemma 20 (termination): every closed well-typed static program reduces to
some distribution value. -/
theorem termination {m : Tm} {T : DTy} (ht : ⊢ₛ m : T) (hs : IsStaticTm m) :
    ∃ (k : ℕ) (V : DistVal), m ⇓ₛ[k] V := by
  obtain ⟨k, V, _, hred, _⟩ := fundamental_tm ht hs ctxStatic_nil ctxWf_nil (ρ := []) .nil
  rw [Tm.close, Tm.closeAt_nil] at hred
  exact ⟨k, V, hred⟩

/-- Theorem 1 (type safety for SPLC): if `⊢ₛ m : T`, then `m` reduces to a
distribution value `V`, typed by rule (V) at some type equal to `T`. -/
theorem type_safety {m : Tm} {T : DTy} (ht : ⊢ₛ m : T) (hs : IsStaticTm m) :
    ∃ (k : ℕ) (V : DistVal) (τs : Fin V.n → Ty),
      m ⇓ₛ[k] V ∧ DistValHasTy V τs ∧ V.tyD τs =ₛ T := by
  obtain ⟨k, V, τs, hred, hty, hceq, _⟩ := fundamental_tm ht hs ctxStatic_nil ctxWf_nil (ρ := []) .nil
  rw [Tm.close, Tm.closeAt_nil] at hred
  exact ⟨k, V, τs, hred, hty, hceq⟩

/-- Theorem 1 (type safety for SPLC), read in terms of probabilities: for a closed program
`⊢ₛ m : {{es}}` reducing to `V`, and for every simple type `τ`, the probability
`V` gives to values whose type is equal to `τ` is the probability `{{es}}` gives
to the class of `τ` (`classMass`).  A corollary of preservation, via the
coupling lemma `classMass_of_coupling`. -/
theorem semantic_soundness {m : Tm} {es : List (Ty × GProb)} {k : ℕ} {V : DistVal}
    (ht : HasTyT [] m (.dist es)) (hs : IsStaticTm m) (hred : Red m k V) :
    ∃ τs : Fin V.n → Ty, DistValHasTy V τs ∧ ∀ τ : Ty,
      classMass EqTy τs V.mass τ
        = classMass EqTy (fun j => (es.get j).1) (fun j => pval (es.get j).2) τ := by
  obtain ⟨τs, hty, hceq⟩ := preservation ht hs hred
  exact ⟨τs, hty, classMass_of_coupling (R := EqTy) (fun _ _ h => EqTy.symm h)
    (fun _ _ _ h1 h2 => EqTy.trans h1 h2) _ _ _ _ (eqD_tyD_inv hceq).1⟩


end GradualProb.SPLC
