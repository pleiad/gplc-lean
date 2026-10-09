import GradualProb.TPLC.Elaboration
import GradualProb.TPLC.Reorder

/-!
# Type safety of TPLC and GPLC

This module proves type safety for TPLC and, through elaboration, for GPLC.
Lemma 38 (substitution preserves typing) supports the application and `let`
cases.  Lemma 42 (preservation for TPLC) states that every reduction of a closed
well-typed TPLC term lands in a well-typed configuration whose runtime type is a
reordering of the term's type and whose entries are all entries of that type.
Theorem 4 (type safety for GPLC) follows: a well-typed GPLC term elaborates
(Lemma 11) to a TPLC term that either converges to such a configuration or
diverges.

## Main results

* `hasTy_subst_tm`, `hasTy_subst0_tm`, `subErr_typed`: Lemma 38 (substitution
  preserves typing).
* `type_safety`, `entriesIn_red`: Lemma 42 (preservation for TPLC).
* `type_safety_converges_or_diverges`: the statement of Theorem 4 for a closed
  well-typed TPLC term.
* `GPLC.type_safety`: Theorem 4 (type safety for GPLC).

## Reading guide

The module starts with the refinement congruences of the type operators, the
typing of configurations (`DConfHasTy`) and the runtime type of each
configuration operator.  Then come the coercion of a value (`Val.coerce`),
Lemma 38, the typing of the coercions at each entry of the routed rules (Dlet) and
(D::μ), and the assembler of the `let` result (`refDist_wsum_letSem`), which
mixes solutions of convex formulas (`convexC_wsum_of_sat`) and is the product
coupling `Lift.sigmaFin`.
Lemma 42 is proved by three inductions on the reduction derivation:
`type_safety_vals` (value typing), `type_safety_gr` (goodness and refinement,
under satisfiability of the result formula) and `type_safety_sat`
(satisfiability).  The module closes with the totality of ascriptions
(`ascV_total`, `dascD_total`), the entries part of Lemma 42 (`entriesIn_red`),
convergence and divergence, and Theorem 4.
-/


namespace GradualProb.TPLC

open GradualProb.GPLC
open Classical
open scoped BigOperators
open GradualProb.CouplingLemma


/-! ## Refinement congruences over the type operators

`RefDist` is the refinement relation by which Lemma 42 relates a runtime type
to a static type; these lemmas show that the type operators preserve it. -/


/-- Lemma 41 (refinement through the type operators): refinement is a congruence
for the choice type at a concrete probability; the two liftings sit side by
side (`Lift.append`). -/
theorem refDist_chooseSem_cong {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {A1 B1 A2 B2 : FDist} (h1 : RefDist A1 B1) (h2 : RefDist A2 B2) :
    RefDist (chooseSem a A1 A2) (chooseSem a B1 B2) := by
  refine RefDist.intro ?_
  rintro x ⟨p1, p2, hp1, hp2, rfl⟩
  obtain ⟨q1, hq1, hl1⟩ := h1.coup p1 hp1
  obtain ⟨q2, hq2, hl2⟩ := h2.coup p2 hp2
  exact ⟨_, ⟨q1, q2, hq1, hq2, rfl⟩, (hl1.smul ha0).append (hl2.smul (sub_nonneg.2 ha1))
    (fun _ _ h => by simpa using h) (fun _ _ h => by simpa using h)⟩

/-- Lemma 41 (refinement through the type operators): refinement is a congruence
for the choice type at an unknown probability. A solution of the hull is one of
`chooseSem a` for some `a ∈ [0,1]`, and `refDist_chooseSem_cong` at that `a`
gives the coupling. -/
theorem refDist_chooseSemU_cong {A1 B1 A2 B2 : FDist}
    (h1 : RefDist A1 B1) (h2 : RefDist A2 B2) :
    RefDist (chooseSemU A1 A2) (chooseSemU B1 B2) := by
  refine RefDist.intro ?_
  rintro x ⟨a, ha0, ha1, hx⟩
  obtain ⟨q, hq, hl⟩ := (refDist_chooseSem_cong ha0 ha1 h1 h2).coup x hx
  exact ⟨q, ⟨a, ha0, ha1, hq⟩, hl⟩

/-- Lemma 41 (refinement through the type operators): refinement into the left
extreme of a hull; if `A` refines `B1` and `B2` is good, then `A` refines
`chooseSemU B1 B2`. The hull point is `a = 1`: the solution of `B1` is pushed
forward along the inclusion of the entries of `B1` (`Lift.pushfwd`). -/
theorem refDist_hull_left {A B1 B2 : FDist}
    (h1 : RefDist A B1) (hg2 : GoodD B2) :
    RefDist A (chooseSemU B1 B2) := by
  refine RefDist.intro fun p hp => ?_
  obtain ⟨q1, hq1, hl⟩ := h1.coup p hp
  obtain ⟨q2, hq2⟩ := hg2.good.sat
  refine ⟨_, ⟨1, zero_le_one, le_rfl, q1, q2, hq1, hq2, rfl⟩, ?_⟩
  have hpad : Fin.append (fun j => 1 * q1 j) (fun j => (1 - 1) * q2 j)
      = pushfwd (Fin.castAdd B2.n) q1 := by rw [pushfwd_castAdd]; simp
  rw [hpad]
  exact hl.trans (.pushfwd (R := fun j k => B1.ty j = (chooseSemU B1 B2).ty k) _
    hl.right_nonneg fun j => by simp) fun _ _ _ => Eq.trans

/-- Lemma 41 (refinement through the type operators): refinement into the right
extreme of a hull; if `A` refines `B2` and `B1` is good, then `A` refines
`chooseSemU B1 B2`. The hull point is `a = 0`: the solution of `B2` is pushed
forward along the inclusion of the entries of `B2` (`Lift.pushfwd`). -/
theorem refDist_hull_right {A B1 B2 : FDist}
    (h2 : RefDist A B2) (hg1 : GoodD B1) :
    RefDist A (chooseSemU B1 B2) := by
  refine RefDist.intro fun p hp => ?_
  obtain ⟨q2, hq2, hl⟩ := h2.coup p hp
  obtain ⟨q1, hq1⟩ := hg1.good.sat
  refine ⟨_, ⟨0, le_rfl, zero_le_one, q1, q2, hq1, hq2, rfl⟩, ?_⟩
  have hpad : Fin.append (fun j => 0 * q1 j) (fun j => (1 - 0) * q2 j)
      = pushfwd (Fin.natAdd B1.n) q2 := by rw [pushfwd_natAdd]; simp
  rw [hpad]
  exact hl.trans (.pushfwd (R := fun j k => B2.ty j = (chooseSemU B1 B2).ty k) _
    hl.right_nonneg fun j => by simp) fun _ _ _ => Eq.trans


/-! ## Typing of distribution configurations

The runtime type of a configuration is a formula type computed from it
(`DConf.confF`).  A configuration is well typed when its values are well typed
at the types they display and its runtime type is good and refines the static
type. -/

/-- Typing of a configuration against a static type `D`, the conclusion of
Lemma 42: every value is well typed at the type it displays, the runtime type is
good, and it refines `D`.

The article's configuration typing `⊢ Φ ▷ 𝒱 : μ′` takes the type `μ′` as part of
the judgment; here it is not a parameter but is computed from the configuration
(`DConf.confF`: the entries are the types the values display, the formula is
the configuration's).  The relation to `D` is `RefDist`: every solution of the
runtime type is coupled with a solution of `D`, with support on equal entries.
This implies the article's reordering `μ′ =ʳ D`.

`vals` holds at every value, including those to which no solution of the
formula gives positive probability: the routing evidence of an enclosing (Dlet)
is computed from every entry of the bound term's runtime type. -/
structure DConfHasTy (V : DConf) (D : FDist) : Prop where
  vals : ∀ i, HasTyV [] (V.val i) ((V.val i).tyEntry)
  good : GoodD V.confF
  reord : RefDist V.confF D

/-- Empty context is good (vacuously). -/
theorem ctxGood_nil : CtxGood ([] : List FTy) := by intro σ h; cases h

/-- A closed well-typed TPLC value displays its typing type. -/
theorem tyEntry_of_hasTy {v : Val} {σ : FTy} (h : HasTyV [] v σ) :
    v.tyEntry = σ := by
  cases h with
  | var hx => simp at hx
  | ascRaw _ _ _ _ => rfl
  | err _ => rfl

/-! ### The runtime type of each operator

The runtime type of each configuration operator is the corresponding type
operator, so the refinement congruences of the type level apply directly in the
proof of Lemma 42. -/

@[simp] theorem confF_point (v : Val) :
    (DConf.point v).confF = pointF v.tyEntry := rfl

@[simp] theorem confF_errAt (μ : FDist) : (DConf.errAt μ).confF = μ := by
  cases μ; rfl

/-- The runtime type of a choice at a concrete probability is the choice type
`chooseSem`. -/
@[simp] theorem confF_choose (a : ℝ) (V1 V2 : DConf) :
    (DConf.choose a V1 V2).confF = chooseSem a V1.confF V2.confF := by
  refine congrArg (fun f => FDist.mk (V1.n + V2.n) f _) ?_
  funext i
  refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i <;>
    simp [DConf.choose, DConf.confF, chooseSem]

/-- The runtime type of a choice at the unknown probability is the hull type
`chooseSemU`. -/
@[simp] theorem confF_chooseU (V1 V2 : DConf) :
    (DConf.chooseU V1 V2).confF = chooseSemU V1.confF V2.confF := by
  refine congrArg (fun f => FDist.mk (V1.n + V2.n) f _) ?_
  funext i
  refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i <;>
    simp [DConf.chooseU, DConf.confF, chooseSemU]

/-! ### The coercion of a value

Rules (D::σ) and (Derr::σ) reduce a value ascription `ε₂ v :: σ'` in one
step to a single value, determined by `ε₂`, `σ'` and `v`. `Val.coerce`
computes that value, and `red_ascV_iff` shows that the reduction of a value
ascription is exactly this function: the inversions of a value-ascription step
follow from the equations of `Val.coerce`. -/

/-- Dirac configurations are injective in their value. -/
theorem DConf.point_inj {v w : Val} (h : DConf.point v = DConf.point w) :
    v = w := by
  simp only [DConf.point, DConf.mk.injEq, heq_eq_eq, true_and] at h
  exact congrFun h.1 0

/-- The coercion of a value to `σt` with evidence `ε2`, by rules (D::σ) and
(Derr::σ): an ascribed value `⟨ε₁ u⟩::σ` becomes `⟨ε₃ u⟩::σt`, with `ε₃` the
meet of `ε₁` and `ε₂`, when the composition is defined (the meet exists and is
well-formed), and the error at `σt` otherwise; an error becomes the error at
`σt`. A variable, which closed values do not contain, has no coercion. -/
noncomputable def Val.coerce (ε2 : TagTy) (σt : FTy) : Val → Option Val
  | .asc ε1 u _ =>
      match emeetTy ε1 ε2 with
      | some ε3 => if GoodTy ε3.toF then some (.asc ε3 u σt) else some (.err σt)
      | none => some (.err σt)
  | .err _ => some (.err σt)
  | .var _ => none

/-- The coercion of an ascribed value whose composition is defined. -/
theorem Val.coerce_asc_ok {ε1 ε2 ε3 : TagTy} {u : Raw} {σ σt : FTy}
    (hm : emeetTy ε1 ε2 = some ε3) (hg : GoodTy ε3.toF) :
    (Val.asc ε1 u σ).coerce ε2 σt = some (.asc ε3 u σt) := by
  simp [Val.coerce, hm, hg]

/-- The coercion of an ascribed value whose composition is undefined. -/
theorem Val.coerce_asc_err {ε1 ε2 : TagTy} {u : Raw} {σ σt : FTy}
    (hd : ¬ ∃ ε3, emeetTy ε1 ε2 = some ε3 ∧ GoodTy ε3.toF) :
    (Val.asc ε1 u σ).coerce ε2 σt = some (.err σt) := by
  simp only [Val.coerce]
  split
  · rename_i ε3 hm
    rw [if_neg (fun hg => hd ⟨ε3, hm, hg⟩)]
  · rfl

/-- The coercion of an error is the error at the target type. -/
@[simp] theorem Val.coerce_err {ε2 : TagTy} {σ σt : FTy} :
    (Val.err σ).coerce ε2 σt = some (.err σt) := rfl

/-- A variable has no coercion. -/
@[simp] theorem Val.coerce_var {ε2 : TagTy} {σt : FTy} {x : ℕ} :
    (Val.var x).coerce ε2 σt = none := rfl

/-- The coercion of an ascribed value, by cases on the definedness of the
composition. -/
theorem Val.coerce_asc_inv {ε1 ε2 : TagTy} {u : Raw} {σ σt : FTy} {w : Val}
    (h : (Val.asc ε1 u σ).coerce ε2 σt = some w) :
    (∃ ε3, emeetTy ε1 ε2 = some ε3 ∧ GoodTy ε3.toF ∧ w = .asc ε3 u σt) ∨
      ((¬ ∃ ε3, emeetTy ε1 ε2 = some ε3 ∧ GoodTy ε3.toF) ∧ w = .err σt) := by
  by_cases hc : ∃ ε3, emeetTy ε1 ε2 = some ε3 ∧ GoodTy ε3.toF
  · obtain ⟨ε3, hm, hg⟩ := hc
    rw [Val.coerce_asc_ok hm hg, Option.some.injEq] at h
    exact .inl ⟨ε3, hm, hg, h.symm⟩
  · rw [Val.coerce_asc_err hc, Option.some.injEq] at h
    exact .inr ⟨hc, h.symm⟩

/-- A value ascription reduces, at any index, to the Dirac on the coercion. -/
theorem red_ascV_coerce : ∀ {ε2 : TagTy} {v : Val} {σt : FTy} {k : ℕ}
    {W : DConf}, Red (.ascV ε2 v σt) k W →
    ∃ w, v.coerce ε2 σt = some w ∧ W = DConf.point w
  | _, _, _, _, _, .dascOk hm hg => ⟨_, Val.coerce_asc_ok hm hg, rfl⟩
  | _, _, _, _, _, .dascErr hd => ⟨_, Val.coerce_asc_err hd, rfl⟩
  | _, _, _, _, _, .eAscV => ⟨_, rfl, rfl⟩
  | _, _, _, _, _, .dmon h0 => red_ascV_coerce h0

/-- The coercion of a value is a one-step reduction of the value ascription. -/
theorem red_ascV_of_coerce {ε2 : TagTy} {v : Val} {σt : FTy} {w : Val}
    (h : v.coerce ε2 σt = some w) : Red (.ascV ε2 v σt) 1 (DConf.point w) := by
  cases v with
  | var x => exact nomatch h
  | err σ => cases h; exact .eAscV
  | asc ε1 u σ =>
    rcases Val.coerce_asc_inv h with ⟨ε3, hm, hg, rfl⟩ | ⟨hd, rfl⟩
    · exact .dascOk hm hg
    · exact .dascErr hd

/-- Rules (D::σ) and (Derr::σ) as a function: a value ascription reduces in one
step to `w` exactly when `w` is the coercion of the value. -/
theorem red_ascV_iff {ε2 : TagTy} {v : Val} {σt : FTy} {w : Val} :
    Red (.ascV ε2 v σt) 1 (DConf.point w) ↔ v.coerce ε2 σt = some w := by
  refine ⟨fun h => ?_, red_ascV_of_coerce⟩
  obtain ⟨w', hw', hpt⟩ := red_ascV_coerce h
  rwa [DConf.point_inj hpt]

/-- The coercion of a value displays the target type, whether it succeeds or
errs. -/
theorem Val.coerce_tyEntry {ε2 : TagTy} {v : Val} {σt : FTy} {w : Val}
    (h : v.coerce ε2 σt = some w) : w.tyEntry = σt := by
  cases v with
  | var x => exact nomatch h
  | err σ => cases h; rfl
  | asc ε1 u σ =>
    rcases Val.coerce_asc_inv h with ⟨ε3, -, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl

/-- Every closed value has a coercion. -/
theorem Val.coerce_total {v : Val} {σ : FTy} (hv : HasTyV [] v σ) (ε2 : TagTy)
    (σt : FTy) : ∃ w, v.coerce ε2 σt = some w := by
  cases v with
  | var x => cases hv with | var hx => simp at hx
  | err σ0 => exact ⟨_, rfl⟩
  | asc ε1 u σ0 =>
    by_cases hc : ∃ ε3, emeetTy ε1 ε2 = some ε3 ∧ GoodTy ε3.toF
    · obtain ⟨ε3, hm, hg⟩ := hc
      exact ⟨_, Val.coerce_asc_ok hm hg⟩
    · exact ⟨_, Val.coerce_asc_err hc⟩

/-- Lemma 39 (one-step coercion of a value), inversion: a one-step reduction of
a value ascription either composes the evidence and coerces the raw value, or
fails and yields the error at the target type, or propagates an `error` operand.
-/
theorem red_ascV_inv {ε2 : TagTy} {v : Val} {σt : FTy} {W : DConf}
    (h : .ascV ε2 v σt ⇓[1] W) :
    (∃ (ε1 : TagTy) (u : Raw) (σv : FTy), v = .asc ε1 u σv ∧
      ((∃ ε3, ε1 ∘ ε2 = some ε3 ∧ GoodTy ε3.toF ∧
          W = DConf.point (.asc ε3 u σt)) ∨
        (¬ (∃ ε3, ε1 ∘ ε2 = some ε3 ∧ GoodTy ε3.toF) ∧
          W = DConf.point (.err σt)))) ∨
    (∃ σ : FTy, v = .err σ ∧ W = DConf.point (.err σt)) := by
  obtain ⟨w, hw, rfl⟩ := red_ascV_coerce h
  cases v with
  | var x => exact nomatch hw
  | err σ => cases hw; exact .inr ⟨σ, rfl, rfl⟩
  | asc ε1 u σv =>
    refine .inl ⟨ε1, u, σv, rfl, ?_⟩
    rcases Val.coerce_asc_inv hw with ⟨ε3, hm, hg, rfl⟩ | ⟨hd, rfl⟩
    · exact .inl ⟨ε3, hm, hg, rfl⟩
    · exact .inr ⟨hd, rfl⟩


/-! ## Lemma 38: substitution preserves typing

Substituting a value `w : τ`, typed in the result context `Δ ++ Γ`, for the
de Bruijn variable at depth `Δ.length` preserves typing.  Under a binder the
value is weakened (`w.rename 0`, typed by `hasTy_wk0_val`).  The proof is by
structural recursion on the term. -/

mutual
/-- Substitution preserves the typing of raw values; the raw-value case of
`hasTy_subst_tm`. -/
theorem hasTy_subst_raw : ∀ (u : Raw) {Δ Γ : List FTy} {σ τ : FTy} {w : Val},
    HasTyV (Δ ++ Γ) w τ → HasTyRaw (Δ ++ τ :: Γ) u σ →
    HasTyRaw (Δ ++ Γ) (u.subst Δ.length w) σ
  | .real _, _, _, _, _, _, _, h => by cases h; rw [Raw.subst]; exact .real
  | .bool _, _, _, _, _, _, _, h => by cases h; rw [Raw.subst]; exact .bool
  | .lam σ0 body, Δ, _, _, _, _, hw, h => by
      cases h with
      | lam hbody hg =>
        rw [Raw.subst]
        have ih := hasTy_subst_tm body (Δ := σ0 :: Δ) (hasTy_wk0_val hw) hbody
        simp only [List.cons_append, List.length_cons] at ih
        exact .lam ih hg
/-- Substitution preserves value typing; the value case of `hasTy_subst_tm`. -/
theorem hasTy_subst_val : ∀ (v : Val) {Δ Γ : List FTy} {σ τ : FTy} {w : Val},
    HasTyV (Δ ++ Γ) w τ → HasTyV (Δ ++ τ :: Γ) v σ →
    HasTyV (Δ ++ Γ) (v.subst Δ.length w) σ
  | .var x, Δ, Γ, σ, τ, w, hw, h => by
      cases h with
      | var hx =>
        rw [Val.subst]
        by_cases h1 : x = Δ.length
        · rw [if_pos h1]; subst h1
          rw [List.getElem?_append_right (le_refl _), Nat.sub_self,
            List.getElem?_cons_zero] at hx
          obtain rfl := Option.some.inj hx
          exact hw
        · rw [if_neg h1]
          by_cases h2 : x > Δ.length
          · rw [if_pos h2]
            refine .var ?_
            have hx2 : Γ[x - 1 - Δ.length]? = some σ := by
              rw [List.getElem?_append_right (by omega : Δ.length ≤ x)] at hx
              rw [show x - Δ.length = (x - 1 - Δ.length) + 1 from by omega,
                List.getElem?_cons_succ] at hx
              exact hx
            rw [List.getElem?_append_right (by omega : Δ.length ≤ x - 1)]
            exact hx2
          · rw [if_neg h2]
            push_neg at h2
            have hlt : x < Δ.length := lt_of_le_of_ne h2 h1
            refine .var ?_
            rw [List.getElem?_append_left hlt]
            rw [List.getElem?_append_left hlt] at hx
            exact hx
  | .asc _ u _, _, _, _, _, _, hw, h => by
      cases h with
      | ascRaw hu hev hge hg => rw [Val.subst]; exact .ascRaw (hasTy_subst_raw u hw hu) hev hge hg
  | .err _, _, _, _, _, _, _, h => by
      cases h with | err hg => rw [Val.subst]; exact .err hg
/-- Lemma 38 (substitution preserves typing), for terms. -/
theorem hasTy_subst_tm : ∀ (m : Tm) {Δ Γ : List FTy} {D : FDist} {τ : FTy} {w : Val},
    Δ ++ Γ ⊢ w : τ → Δ ++ τ :: Γ ⊢ m : D →
    Δ ++ Γ ⊢ m.subst Δ.length w : D
  | .val v, _, _, _, _, _, hw, h => by
      cases h with | val hv => rw [Tm.subst]; exact .val (hasTy_subst_val v hw hv)
  | .app v u, _, _, _, _, _, hw, h => by
      cases h with
      | app hv hu => rw [Tm.subst]; exact .app (hasTy_subst_val v hw hv) (hasTy_subst_val u hw hu)
  | .letin mm _ ns, Δ, _, _, _, w, hw, h => by
      cases h with
      | @letin _ _ _ ty _ _ F hm hbody =>
        rw [Tm.subst_letin]
        refine .letin (hasTy_subst_tm mm hw hm) (fun i => ?_)
        have ih := hasTy_subst_tm (ns i) (Δ := ty i :: Δ) (hasTy_wk0_val hw) (hbody i)
        simp only [List.cons_append, List.length_cons] at ih
        exact ih
  | .choice _ m n, _, _, _, _, _, hw, h => by
      cases h with
      | choice ha0 ha1 hm hn =>
        rw [Tm.subst]; exact .choice ha0 ha1 (hasTy_subst_tm m hw hm) (hasTy_subst_tm n hw hn)
      | choiceU hm hn =>
        rw [Tm.subst]; exact .choiceU (hasTy_subst_tm m hw hm) (hasTy_subst_tm n hw hn)
  | .ascT _ m _, _, _, _, _, _, hw, h => by
      cases h with
      | ascT hm hev hge hg => rw [Tm.subst]; exact .ascT (hasTy_subst_tm m hw hm) hev hge hg
  | .ascV _ v _, _, _, _, _, _, hw, h => by
      cases h with
      | ascV hv hev hge hg => rw [Tm.subst]; exact .ascV (hasTy_subst_val v hw hv) hev hge hg
  | .ite v m n, _, _, _, _, _, hw, h => by
      cases h with
      | ite hv hm hn =>
        rw [Tm.subst]
        exact .ite (hasTy_subst_val v hw hv) (hasTy_subst_tm m hw hm) (hasTy_subst_tm n hw hn)
  | .add v u, _, _, _, _, _, hw, h => by
      cases h with
      | add hv hu =>
        rw [Tm.subst]; exact .add (hasTy_subst_val v hw hv) (hasTy_subst_val u hw hu)
  | .errD _, _, _, _, _, _, _, h => by
      cases h with | errD hg => rw [Tm.subst]; exact .errD hg
end

/-- Lemma 38 (substitution preserves typing), at the most recently bound
variable. -/
theorem hasTy_subst0_tm {Γ : List FTy} {m : Tm} {D : FDist} {τ : FTy} {w : Val}
    (hw : Γ ⊢ w : τ) (h : τ :: Γ ⊢ m : D) : Γ ⊢ m.subst0 w : D :=
  hasTy_subst_tm m (Δ := []) hw h


/-! ### The routed rules: the coercion at every entry is well typed

The evidence facts hold at every entry, so the coercion at each entry of (Dlet) and
(D::μ) is well typed without consuming any satisfiability.  For the routing
evidence `tagReorderD` that both rules compute, the facts are derived entry by
entry from the goodness of the entry types alone (`tagReorderD_cell`). -/

/-- The coercion of a well-typed value is well typed at the target type: by
the meet's reductivity when the composition succeeds, and as an error at the
target otherwise. -/
theorem Val.coerce_typed {e : TagTy} {v w : Val} {σv σt : FTy}
    (hv : HasTyV [] v σv)
    (hev2 : HVTagTy e σv σt) (hg2 : GoodTy e.toF) (hgt : GoodTy σt)
    (h : v.coerce e σt = some w) : HasTyV [] w σt := by
  cases hv with
  | var hx => simp at hx
  | err _ => cases h; exact .err hgt
  | ascRaw hu hev1 hge1 _ =>
    rcases Val.coerce_asc_inv h with ⟨ε3, hmeet, hgε3, rfl⟩ | ⟨-, rfl⟩
    · exact .ascRaw hu (hetransTy_invariant hev1 hev2 hge1 hg2 hmeet) hgε3 hgt
    · exact .err hgt

/-- Lemma 39 (one-step coercion of a value): a fired coercion at a single entry is well
typed at the target entry. -/
theorem cell_coercion_typed {e : TagTy} {v w : Val} {σt : FTy}
    (hv : ⊢ v : v.tyEntry)
    (hev2 : e ⊩ v.tyEntry ∼̇ σt) (hg2 : GoodTy e.toF) (hgt : GoodTy σt)
    (hstep : .ascV e v σt ⇓[1] DConf.point w) :
    ⊢ w : σt :=
  Val.coerce_typed hv hev2 hg2 hgt (red_ascV_iff.1 hstep)

/-- Entrywise facts of the routing evidence `tagReorderD D1 D2`, from the goodness
of the entry types alone: each index of the carrier pairs `=ʳ`-related entries, so its
entry is the tagged reordering of the pair, hereditarily valid for it and with a
good erasure. -/
theorem tagReorderD_cell {D1 D2 : FDist} (hg1 : ∀ i, GoodTy (D1.ty i))
    (hg2 : ∀ j, GoodTy (D2.ty j)) (c : Fin (D1 ∥ᵗ D2).n) :
    (D1 ∥ᵗ D2).ty c ⊩ D1.ty (reorderDL D1 D2 c) ∼̇ D2.ty (reorderDR D1 D2 c) ∧
      GoodTy ((D1 ∥ᵗ D2).ty c).toF := by
  have hRD := ereordTy_of_eq (hg1 _) (reorderD_cell_eq D1 D2 c)
  obtain ⟨e, he, hL, hR⟩ := hvtag_tagReorderTy (hg1 _) (hg2 _) hRD
  obtain rfl : e = (tagReorderD D1 D2).ty c :=
    Option.some.inj (he.symm.trans (tagReorderD_ty_spec D1 D2 c))
  refine ⟨⟨hL, hR⟩, ?_⟩
  rw [tagReorderD_ty_toF]
  exact goodTy_reorderTy (hg1 _) (hg2 _) hRD (reorderD_ty_spec D1 D2 c)

/-- Left half of the entrywise validity of `tagReorderD`, in the index form the
composition consumes (`hemeetD_entry`): the left tag of an entry is the index of
its left projection. -/
theorem tagReorderD_cellL {D1 D2 : FDist} (hg1 : ∀ i, GoodTy (D1.ty i))
    (hg2 : ∀ j, GoodTy (D2.ty j)) (i : Fin (tagReorderD D1 D2).n)
    (h : (tagReorderD D1 D2).l i < D1.n) :
    HVTag .l ((tagReorderD D1 D2).ty i) (D1.ty ⟨_, h⟩) :=
  (tagReorderD_cell hg1 hg2 i).1.1

/-- Goodness of each entry of `tagReorderD`. -/
theorem goodTy_tagReorderD_entry {D1 D2 : FDist} (hg1 : ∀ i, GoodTy (D1.ty i))
    (hg2 : ∀ j, GoodTy (D2.ty j)) (i : Fin (tagReorderD D1 D2).n) :
    GoodTy ((tagReorderD D1 D2).ty i).toF :=
  (tagReorderD_cell hg1 hg2 i).2

/-- Solutions of the computed routing evidence's constraint project onto the
operands: nonnegativity is built in, the left marginal is a solution of `D1`
with the same total probability, and `D2` has a solution (the right
marginal). -/
theorem tagReorderD_C_dest {D1 D2 : FDist} {w : Fin (tagReorderD D1 D2).n → ℝ}
    (hw : (tagReorderD D1 D2).toF.C w) :
    (∀ c, 0 ≤ w c) ∧ (∃ p, D1.C p ∧ (∑ c, w c) = ∑ i, p i) ∧ ∃ q, D2.C q := by
  obtain ⟨h1, h2, hnn⟩ := (reorderD_C_iff D1 D2 w).1 hw
  exact ⟨hnn, ⟨_, h1, (sum_pushfwd (reorderDL D1 D2) w).symm⟩, _, h2⟩

/-- The right marginal of any solution of the constraint of `tagReorderD D1 D2`
is a solution of `D2`: it is the constraint's right-marginal clause.  This is
the push-forward the `let` assembler consumes. -/
theorem tagReorderD_pushR {D1 D2 : FDist} {w : Fin (tagReorderD D1 D2).n → ℝ}
    (hw : (tagReorderD D1 D2).toF.C w) :
    D2.C (pushfwd (reorderDR D1 D2) w) :=
  ((reorderD_C_iff D1 D2 w).1 hw).2.1

/-- In (Dlet) the coercion at each entry is well typed at the target entry.  The
evidence facts are computed entry by entry, so only the goodness of the entry
types of the bound term's runtime type is consumed. -/
theorem dlet_cell_typed {V : DConf} {μ : FDist}
    (hVvals : ∀ i, HasTyV [] (V.val i) ((V.val i).tyEntry)) (hgμ : GoodD μ)
    {c : Fin (tagReorderD V.confF μ).n} {wv : Val}
    (hstep : Red (.ascV ((tagReorderD V.confF μ).ty c) (V.val (reorderDL V.confF μ c))
      (μ.ty (reorderDR V.confF μ c))) 1 (DConf.point wv)) :
    HasTyV [] wv (μ.ty (reorderDR V.confF μ c)) := by
  obtain ⟨hev2, hg2⟩ := tagReorderD_cell (D1 := V.confF)
    (fun i => wf_val (hVvals i) ctxGood_nil) hgμ.tys c
  exact cell_coercion_typed (hVvals _) hev2 hg2 (hgμ.tys _) hstep

/-- Lemma 38 (substitution preserves typing), for the substitution `sub` of the
routed rules: an `error` argument turns the body into the error at the body's
type. -/
theorem subErr_typed {n : Tm} {w : Val} {τ : FTy} {γ : FDist}
    (hw : ⊢ w : τ) (hn : [τ] ⊢ n : γ) (hgγ : GoodD γ) :
    ⊢ n.subErr w γ : γ := by
  cases w with
  | var x => cases hw with | var hx => simp at hx
  | err σe => exact .errD hgγ
  | asc ε u σ => exact hasTy_subst0_tm hw hn

/-- The contractum of (Dapp), the ascribed body with the coerced argument
substituted by `sub`, is well typed at the application's type. -/
theorem dapp_contractum_typed {ε : TagTy} {σ' σa σX : FTy} {mb : Tm}
    {Dres D0 : FDist} {v w : Val} {s : TagTy} {d : TagD} {k1 : ℕ}
    (hv : HasTyV [] (.asc ε (.lam σ' mb) (.arrow σa Dres)) (.arrow σX D0))
    (hw : HasTyV [] v σX)
    (hdom : tagDom ε = some s) (hcod : tagCod ε = some d)
    (hred1 : Red (.ascV s v σ') k1 (DConf.point w)) :
    HasTyT [] ((Tm.ascT d mb Dres).subErr w Dres) D0 := by
  cases hv with
  | ascRaw hlam hevε hgeε hgarr =>
    cases hlam with
    | lam hbody hgσ'2 =>
      cases ε with
      | real => simp [tagDom] at hdom
      | bool => simp [tagDom] at hdom
      | unk => simp [tagDom] at hdom
      | arrow s0 d0 =>
        simp only [tagDom, Option.some.injEq] at hdom
        simp only [tagCod, Option.some.injEq] at hcod
        subst hdom
        subst hcod
        obtain ⟨hprec1, hprec2⟩ := hevε
        cases hprec1 with
        | arrow hs1 hD1 =>
          cases hprec2 with
          | arrow hs2 hD2 =>
            cases hgeε with
            | arrow hgs hgD =>
              cases hgarr with
              | arrow hgσa hgDres =>
                obtain ⟨w', hco, hpt⟩ := red_ascV_coerce hred1
                obtain rfl := DConf.point_inj hpt
                have hgsf : GoodTy s0.flip.toF := by
                  rw [TagTy.flip_toF]; exact hgs
                have hwt := Val.coerce_typed hw
                  ⟨hvtag_flip hs2, hvtag_flip hs1⟩ hgsf hgσ'2 hco
                exact subErr_typed hwt (.ascT hbody ⟨hD1, hD2⟩ hgD hgDres) hgDres

/-- The coercion at each entry of (D::μ) is well typed.  The facts about the
computed evidence are read entry by entry: the left side from `tagReorderD`
(`tagReorderD_cellL`), the right side from the validity of the evidence `εd`
written in the term (which typing guarantees), and the composition
`hemeetD_entry` joins them.  Its consistency at each entry is free, since the
carrier of the meet consists of consistent pairs. -/
theorem dascD_cell_typed {V : DConf} {μ μb : FDist} {εd : TagD}
    (hVvals : ∀ i, HasTyV [] (V.val i) ((V.val i).tyEntry)) (hgμ : GoodD μ)
    (hεdR : HValid .r εd μb) (hgεd : GoodD εd.toF) (hgμb : GoodD μb)
    {c : Fin (emeetD (tagReorderD V.confF μ) εd).n}
    (hR : (emeetD (tagReorderD V.confF μ) εd).r c < μb.n) {wv : Val}
    (hstep : Red (.ascV ((emeetD (tagReorderD V.confF μ) εd).ty c)
      (V.val (reorderDL V.confF μ (meetDL (tagReorderD V.confF μ).toF εd.toF c)))
      (μb.ty ⟨_, hR⟩)) 1 (DConf.point wv)) :
    HasTyV [] wv (μb.ty ⟨_, hR⟩) := by
  have hVg : ∀ i, GoodTy (V.confF.ty i) :=
    fun i => wf_val (hVvals i) ctxGood_nil
  obtain ⟨hrR, -, hhR⟩ := hεdR
  exact cell_coercion_typed (hVvals _)
    (hemeetD_entry (tagReorderD_cellL hVg hgμ.tys)
      (fun j h => hhR j) (goodTy_tagReorderD_entry hVg hgμ.tys)
      (TagD.goodTy_entry hgεd) _ (reorderDL _ _ _).isLt hR)
    (goodTy_emeetD_entry (goodTy_tagReorderD_entry hVg hgμ.tys)
      (TagD.goodTy_entry hgεd) _)
    (hgμb.tys _) hstep

/-- The (D::μ) case of Lemma 42: the mixture of the coercions at the entries is well
typed at the target, each entry routed to the entry of the target type its right tag names.
Only entrywise facts and the right marginal of the computed evidence
(`emeetD_pushR`) are consumed: every solution of the composed formula is
related to its push-forward along the right tags (`Lift.pushfwd`). -/
theorem dascD_safety {V : DConf} {μ μb : FDist} {εd : TagD}
    {wv : Fin (emeetD (tagReorderD V.confF μ) εd).n → Val}
    (hR : ∀ c : Fin (emeetD (tagReorderD V.confF μ) εd).n,
      (emeetD (tagReorderD V.confF μ) εd).r c < μb.n)
    (hsat : ∃ w, (emeetD (tagReorderD V.confF μ) εd).toF.C w)
    (hgV : GoodD V.confF) (hgμ : GoodD μ)
    (hεdR : HValid .r εd μb) (hgεd : GoodD εd.toF) (hgμb : GoodD μb)
    (hVvals : ∀ i, HasTyV [] (V.val i) ((V.val i).tyEntry))
    (hcell : ∀ c, Red (.ascV ((emeetD (tagReorderD V.confF μ) εd).ty c)
      (V.val (reorderDL V.confF μ (meetDL (tagReorderD V.confF μ).toF εd.toF c)))
      (μb.ty ⟨_, hR c⟩)) 1 (DConf.point (wv c))) :
    DConfHasTy (DConf.wsumPoint (emeetD (tagReorderD V.confF μ) εd).toF.C wv) μb := by
  have key : ∀ c, HasTyV [] (wv c) (μb.ty ⟨_, hR c⟩) :=
    fun c => dascD_cell_typed hVvals hgμ hεdR hgεd hgμb (hR c) (hcell c)
  have hgood : GoodD (emeetD (tagReorderD V.confF μ) εd).toF := by
    obtain ⟨w, hw⟩ := hsat
    obtain ⟨hsatL, -⟩ := emeetD_C_dest hw
    exact goodD_emeetD_sat
      (goodD_tagReorderD_sat hgV hgμ (reorderD_sat_of_tagReorderD_sat hsatL))
      hgεd ⟨w, hw⟩
  refine ⟨?_, ?_, ?_⟩
  · intro c
    show HasTyV [] (wv c) ((wv c).tyEntry)
    rw [tyEntry_of_hasTy (key c)]
    exact key c
  · refine GoodD.mk hgood.good (fun c => ?_)
    show GoodTy ((wv c).tyEntry)
    rw [tyEntry_of_hasTy (key c)]
    exact hgμb.tys _
  · refine RefDist.intro fun ω hω => ⟨_, ?_,
      .pushfwd (fun c => (⟨_, hR c⟩ : Fin μb.n))
        (hgood.good.nonneg ω hω) fun c => tyEntry_of_hasTy (key c)⟩
    exact emeetD_pushR hεdR hω hR

/-! ### The `let` assembler

The mixture returned by (Dlet) refines the result type `letSem μ F` of the
`let`.  The statement is over an abstract weight formula `W` whose solutions
are nonnegative and whose push-forward along the routing `κ` solves `μ`.  Given
a solution `ω`, the target solution is that push-forward for the bound term
entries and, per entry, the mixture weighted by `ω` of the solutions that the
refinements of the branches provide (`convexC_wsum_of_sat`).  The coupling is
the product (`Lift.sigmaFin`) of the coupling of `ω` with its push-forward,
which sends each summand to the entry it routes to, with the couplings of the
branches. -/


/-- Lemma 41 (refinement through the type operators), the `let` assembler: the
mixture returned by (Dlet) refines `letSem μ F`. The blocks of the result are
indexed by the entries of the bound term's type. -/
theorem refDist_wsum_letSem {μ : FDist} {F : Fin μ.n → FDist}
    {K : ℕ} {W : (Fin K → ℝ) → Prop} {Vk : Fin K → DConf}
    (hgF : ∀ i, GoodD (F i))
    (κ : Fin K → Fin μ.n)
    (hWnn : ∀ ω, W ω → ∀ c, 0 ≤ ω c)
    (hρC : ∀ ω, W ω → μ.C (pushfwd κ ω))
    (hbr : ∀ c, (∃ ω, W ω ∧ 0 < ω c) → (∃ bc, (Vk c).C bc) →
      RefDist (Vk c).confF (F (κ c))) :
    RefDist (DConf.wsum W Vk).confF (letSem μ F) := by
  refine RefDist.intro ?_
  rintro x ⟨ω, hω, b, hb, hx⟩
  -- the routing coupling: all the weight of the summand `k` goes to the entry `κ k`
  have hu := isCoupling_pushfwd κ (hWnn ω hω)
  have hsu : Supp (fun k a => κ k = a ∧ 0 < ω k) (fun k a => if κ k = a then ω k else 0) :=
    fun _ _ hpos => pos_of_ite_pos hpos
  -- for a summand of positive weight, the refinement of its branch gives a solution
  -- of the branch type of the entry it routes to
  have hex : ∀ k a, ∃ c : Fin (F a).n → ℝ, κ k = a ∧ 0 < ω k →
      (F a).C c ∧ Lift (fun i l => ((Vk k).val i).tyEntry = (F a).ty l) (b k) c := by
    intro k a
    by_cases h : κ k = a ∧ 0 < ω k
    · obtain ⟨rfl, hpos⟩ := h
      obtain ⟨c, hc, hl⟩ := (hbr k ⟨ω, hω, hpos⟩ ⟨b k, hb k hpos⟩).coup (b k) (hb k hpos)
      exact ⟨c, fun _ => ⟨hc, hl⟩⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' h⟩
  choose c hc using hex
  -- per entry, the mixture of those solutions weighted by `ω` is the weight
  -- of the entry times a solution `g a` of its branch type
  have hmix : ∀ a, ∃ g, (F a).C g ∧
      ∀ l, ∑ k, (if κ k = a then ω k else 0) * c k a l = pushfwd κ ω a * g l := fun a =>
    convexC_wsum_of_sat (hgF a).good.convex (hgF a).good.sat (fun k => hu.nonneg k a)
      fun k hk => (hc k a (hsu k a hk)).1
  choose g hg hge using hmix
  -- the product of the routing coupling with the couplings of the branches
  obtain ⟨w, hw, hs⟩ := Lift.sigmaFin
    (T := fun s t => ((Vk (finSigmaFinEquiv.symm s).1).val (finSigmaFinEquiv.symm s).2).tyEntry
      = (F (finSigmaFinEquiv.symm t).1).ty (finSigmaFinEquiv.symm t).2)
    hu hsu (fun k a h => (hc k a h).2) fun k a i l _ h => by
      beta_reduce
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact h
  exact ⟨fun t => pushfwd κ ω (finSigmaFinEquiv.symm t).1 * g _ (finSigmaFinEquiv.symm t).2,
    ⟨_, hρC ω hω, g, hg, fun _ => rfl⟩, w, hw.congr (fun s => (hx s).symm) fun t => hge _ _, hs⟩

/-! ## Lemma 42: preservation for TPLC

The proof is split into three inductions on the reduction derivation:

* `type_safety_vals`: every produced value is well typed at the type it
  displays, with no satisfiability assumption, including the values no
  solution of the formula gives positive probability;
* `type_safety_gr`: the runtime type is good and refines the static type,
  assuming the result formula is satisfiable (it is the conjunction of the
  subderivations' formulas, so the hypothesis projects to each of them);
* `type_safety_sat`: the result formula is satisfiable. For the bound term
  of a (Dlet) it calls `type_safety_vals` and `type_safety_gr` on the
  subderivation, with the satisfiability given by its own induction
  hypothesis.

`type_safety` combines the three, discharging the hypothesis of
`type_safety_gr` with `type_safety_sat`.

The runtime type is the configuration's own formula type, so each case is the
refinement congruence of the corresponding type operator, applied through the
`confF_*` lemmas. -/

/-- The value of a Dirac configuration types at its displayed type. -/
theorem vals_point {v : Val} {σ : FTy} (h : HasTyV [] v σ) :
    ∀ i, HasTyV [] ((DConf.point v).val i)
      (((DConf.point v).val i).tyEntry) := by
  intro _
  rw [tyEntry_of_hasTy h]
  exact h

/-- Goodness and refinement for a Dirac configuration. -/
theorem gr_point {v : Val} {σ : FTy} (h : HasTyV [] v σ) (hg : GoodTy σ) :
    GoodD (DConf.point v).confF ∧ RefDist (DConf.point v).confF (pointF σ) := by
  constructor
  · rw [confF_point, tyEntry_of_hasTy h]
    exact goodD_point hg
  · rw [confF_point, tyEntry_of_hasTy h]
    exact RefDist.refl (goodD_point hg)

/-- Goodness and refinement for the all-errors configuration. -/
theorem gr_errAt {μ : FDist} (hg : GoodD μ) :
    GoodD (DConf.errAt μ).confF ∧ RefDist (DConf.errAt μ).confF μ := by
  constructor
  · rw [confF_errAt]; exact hg
  · rw [confF_errAt]; exact RefDist.refl hg

/-- Lemma 41 (refinement through the type operators): goodness of the runtime
type of a routed mixture, from an abstract weight formula: nonnegative weights
summing to one on every solution, a convex formula, and guarded branch goodness.
A summand that no solution gives positive weight contributes no constraint and only
needs good entry types. Satisfiability of the mixture's formula is a hypothesis.
-/
theorem goodD_confF_wsum {K : ℕ} {W : (Fin K → ℝ) → Prop} {Vk : Fin K → DConf}
    (hWnn : ∀ ω, W ω → ∀ c, 0 ≤ ω c)
    (hWmass : ∀ ω, W ω → (∑ c, ω c) = 1)
    (hWconv : ∀ ω ω', W ω → W ω' → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      W (fun c => t * ω c + (1 - t) * ω' c))
    (hsat : ∃ x, (DConf.wsum W Vk).C x)
    (hgVk : ∀ c, (∃ ω, W ω ∧ 0 < ω c) → (∃ b, (Vk c).C b) →
      GoodC (Vk c).n (Vk c).C)
    (htys : ∀ c i, GoodTy ((Vk c).val i).tyEntry) :
    GoodD (DConf.wsum W Vk).confF := by
  refine GoodD.mk ⟨hsat, ?_, ?_, ?_⟩ (fun t => htys _ _)
  · -- nonnegativity: positive-weight summands have branch solutions
    rintro x ⟨ω, hω, b, hb, hx⟩ t
    rw [hx t]
    rcases (hWnn ω hω (finSigmaFinEquiv.symm t).1).lt_or_eq with hc | hc
    · exact mul_nonneg hc.le
        ((hgVk _ ⟨ω, hω, hc⟩ ⟨b _, hb _ hc⟩).nonneg _ (hb _ hc) _)
    · rw [← hc, zero_mul]
  · -- total probability 1: block totals collapse to the weights
    rintro x ⟨ω, hω, b, hb, hx⟩
    have hterm : ∀ c, (∑ i, ω c * b c i) = ω c := by
      intro c
      rcases (hWnn ω hω c).lt_or_eq with hc | hc
      · rw [← Finset.mul_sum,
          (hgVk c ⟨ω, hω, hc⟩ ⟨b c, hb c hc⟩).mass _ (hb c hc), mul_one]
      · rw [← hc]; simp
    calc (∑ t, x t)
        = ∑ c : Fin K, ∑ i, ω c * b c i := by
          rw [← sum_sigma_proj (fun c i => ω c * b c i)]
          exact Finset.sum_congr rfl fun t _ => hx t
      _ = ∑ c, ω c := Finset.sum_congr rfl fun c _ => hterm c
      _ = 1 := hWmass ω hω
  · -- convexity: mix the weights; per summand of positive weight, mix the branch solutions
    rintro x x' ⟨ω, hω, b, hb, hx⟩ ⟨ω', hω', b', hb', hx'⟩ t ht0 ht1
    have hA : ∀ c, 0 ≤ t * ω c := fun c => mul_nonneg ht0 (hWnn ω hω c)
    have hA' : ∀ c, 0 ≤ (1 - t) * ω' c :=
      fun c => mul_nonneg (by linarith) (hWnn ω' hω' c)
    have key : ∀ c, ∃ B : Fin (Vk c).n → ℝ,
        (0 < t * ω c + (1 - t) * ω' c → (Vk c).C B) ∧
        ∀ i, t * (ω c * b c i) + (1 - t) * (ω' c * b' c i)
          = (t * ω c + (1 - t) * ω' c) * B i := by
      intro c
      by_cases hpos : 0 < t * ω c + (1 - t) * ω' c
      · -- one of the two weights is positive, so the summand is good
        have hgc : GoodC (Vk c).n (Vk c).C := by
          by_cases h : 0 < ω c
          · exact hgVk c ⟨ω, hω, h⟩ ⟨b c, hb c h⟩
          · have h' : 0 < ω' c := by
              rw [eq_zero_of_nonneg_of_not_pos (hWnn ω hω c) h, mul_zero, zero_add] at hpos
              exact (pos_and_pos_of_mul_pos (sub_nonneg.2 ht1) (hWnn ω' hω' c) hpos).2
            exact hgVk c ⟨ω', hω', h'⟩ ⟨b' c, hb' c h'⟩
        obtain ⟨B, hB, hBe⟩ := convexC_wsum₂ hgc.convex (hA c) (hA' c)
          (fun h => hb c (pos_and_pos_of_mul_pos ht0 (hWnn ω hω c) h).2)
          (fun h => hb' c (pos_and_pos_of_mul_pos (sub_nonneg.2 ht1) (hWnn ω' hω' c) h).2)
        exact ⟨B, hB, fun i => by rw [← hBe i]; ring⟩
      · -- zero total weight: both sides vanish
        have hz1 : t * ω c = 0 := by linarith [hA c, hA' c, not_lt.1 hpos]
        have hz2 : (1 - t) * ω' c = 0 := by linarith [hA c, hA' c, not_lt.1 hpos]
        refine ⟨fun _ => 0, fun h => absurd h hpos, fun i => ?_⟩
        linear_combination (b c i) * hz1 + (b' c i) * hz2
    choose B hBC hBe using key
    refine ⟨fun c => t * ω c + (1 - t) * ω' c,
      hWconv ω ω' hω hω' t ht0 ht1, B, hBC, ?_⟩
    intro tt
    show t * x tt + (1 - t) * x' tt = _
    rw [hx tt, hx' tt]
    exact hBe _ _

/-- Lemma 42 (preservation for TPLC), value-typing part, with no satisfiability
assumption: every value of a reduction result is well typed at the type it
displays, including the values to which no solution of the formula gives
positive probability. Those values matter because the routing evidence of an
enclosing (Dlet) or (D::μ) is computed from every entry of the runtime type of
the term they reduce first. -/
theorem type_safety_vals : ∀ {m : Tm} {k : ℕ} {V : DConf}, m ⇓[k] V →
    ∀ {D : FDist}, ⊢ m : D →
    ∀ i, ⊢ V.val i : (V.val i).tyEntry := by
  intro m k V hr
  induction hr with
  | dv =>
      intro D ht
      cases ht with
      | val hv => exact vals_point hv
  | dchoice ha0 ha1 _ _ ih1 ih2 =>
      intro D ht i
      cases ht with
      | choice _ _ hm hn =>
        refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i
        · simpa using ih1 hm i1
        · simpa using ih2 hn i2
  | dchoiceU _ _ ih1 ih2 =>
      intro D ht i
      cases ht with
      | choiceU hm hn =>
        refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i
        · simpa using ih1 hm i1
        · simpa using ih2 hn i2
  | dadd hmeet =>
      intro D ht
      cases ht with
      | add hv hw =>
        cases hv with
        | ascRaw hr1 he1 _ _ =>
          cases hr1
          obtain ⟨he1a, _⟩ := he1; cases he1a
          cases hw with
          | ascRaw hr2 he2 _ _ =>
            cases hr2
            obtain ⟨he2a, _⟩ := he2; cases he2a
            simp only [emeetTy, Option.some.injEq] at hmeet
            subst hmeet
            exact vals_point
              (.ascRaw HasTyRaw.real ⟨HVTag.real, HVTag.real⟩
                GoodTy.real GoodTy.real)
  | dmon _ ih => intro D ht; exact ih ht
  | dit _ ih =>
      intro D ht
      cases ht with
      | ite _ hm _ => exact ih hm
  | dif _ ih =>
      intro D ht
      cases ht with
      | ite _ _ hn => exact ih hn
  | derr =>
      intro D ht
      cases ht with
      | errD hg => exact fun i => .err (hg.tys i)
  | dascOk hmeet hgε3 =>
      intro D ht
      cases ht with
      | ascV hv hev2 hge2 hgσ' =>
        cases hv with
        | ascRaw hu hev1 hge1 _ =>
          exact vals_point
            (.ascRaw hu (hetransTy_invariant hev1 hev2 hge1 hge2 hmeet)
              hgε3 hgσ')
  | dascErr _ =>
      intro D ht
      cases ht with
      | ascV _ _ _ hgσ' => exact vals_point (.err hgσ')
  | eAscV =>
      intro D ht
      cases ht with
      | ascV _ _ _ hgσ' => exact vals_point (.err hgσ')
  | eAddL =>
      intro D ht
      cases ht with
      | add _ _ => exact vals_point (.err GoodTy.real)
  | eAddR =>
      intro D ht
      cases ht with
      | add _ _ => exact vals_point (.err GoodTy.real)
  | eApp =>
      intro D ht
      cases ht with
      | app hv _ =>
        cases hv with
        | err hg => cases hg with | arrow _ hgD => exact fun i => .err (hgD.tys i)
  | eIte hm hn =>
      intro D ht
      cases ht with
      | ite _ hm' hn' =>
        obtain rfl := det_tm hm hm'
        obtain rfl := det_tm hn hn'
        exact fun i => .err ((goodD_chooseU (wf_tm hm ctxGood_nil)
          (wf_tm hn ctxGood_nil)).tys i)
  | dapp hdom hcod hred1 _ _ ih2 =>
      intro D0 ht
      cases ht with
      | app hv hw => exact ih2 (dapp_contractum_typed hv hw hdom hcod hred1)
  | @dlet m1 n ty C ns k1 k2 V wv Vk Fb hred1 htyμ hcell hbty
      hbodyred ihm ihcell ihbody =>
      intro D0 ht
      cases ht with
      | @letin _ _ _ ty2 C2 _ F hm hbodyty =>
        injection det_tm htyμ hm with _ hty hC
        subst hty hC
        have hgμ : GoodD ⟨n, ty, C⟩ := wf_tm hm ctxGood_nil
        have hVvals := ihm hm
        intro i
        have hwv := dlet_cell_typed hVvals hgμ (hcell (finSigmaFinEquiv.symm i).1)
        have hgFb : GoodD (Fb (finSigmaFinEquiv.symm i).1) :=
          wf_tm (hbty (finSigmaFinEquiv.symm i).1)
            (ctxGood_cons (hgμ.tys _) ctxGood_nil)
        exact ihbody _ (subErr_typed hwv (hbty (finSigmaFinEquiv.symm i).1) hgFb)
          (finSigmaFinEquiv.symm i).2
  | @dascD εd m μ μb k1 V wv hvR hredm htyμ hsat hcell ihm =>
      intro D ht
      cases ht with
      | ascT htm hval hgεd hgμb =>
        intro c
        have hwv : HasTyV [] (wv c) (μb.ty ⟨_, emeetD_r_lt_of_hvalid hvR.2 c⟩) :=
          dascD_cell_typed (ihm htyμ) (wf_tm htyμ ctxGood_nil) hval.2 hgεd
            hgμb (emeetD_r_lt_of_hvalid hvR.2 c) (hcell c)
        show HasTyV [] (wv c) ((wv c).tyEntry)
        rw [tyEntry_of_hasTy hwv]
        exact hwv
  | @dascDErr εd m μ μb k1 V _ hredm htyμ hnsat ihm =>
      intro D ht
      cases ht with
      | ascT htm _ _ hgμb =>
        intro i
        exact .err (hgμb.tys i)

/-- Lemma 42 (preservation for TPLC), goodness and refinement part: if the
result formula of a reduction of a closed well-typed term is satisfiable, then
its runtime type is good and refines the static type. Each case projects the
hypothesis to the subderivations, since the result formula is the conjunction of
theirs; `type_safety` discharges it with `type_safety_sat`. -/
theorem type_safety_gr : ∀ {m : Tm} {k : ℕ} {V : DConf}, m ⇓[k] V →
    ∀ {D : FDist}, ⊢ m : D → (∃ p, V.C p) →
    GoodD V.confF ∧ RefDist V.confF D := by
  intro m k V hr
  induction hr with
  | dv =>
      intro D ht _
      cases ht with
      | val hv => exact gr_point hv (wf_val hv ctxGood_nil)
  | dchoice ha0 ha1 _ _ ih1 ih2 =>
      intro D ht hsat
      cases ht with
      | choice _ _ hm hn =>
        obtain ⟨x, p, q, hp, hq, -⟩ := hsat
        obtain ⟨hg1, hr1⟩ := ih1 hm ⟨p, hp⟩
        obtain ⟨hg2, hr2⟩ := ih2 hn ⟨q, hq⟩
        constructor
        · rw [confF_choose]; exact goodD_choose ha0 ha1 hg1 hg2
        · rw [confF_choose]; exact refDist_chooseSem_cong ha0 ha1 hr1 hr2
  | dchoiceU _ _ ih1 ih2 =>
      intro D ht hsat
      cases ht with
      | choiceU hm hn =>
        obtain ⟨x, a, ha0, ha1, p, q, hp, hq, -⟩ := hsat
        obtain ⟨hg1, hr1⟩ := ih1 hm ⟨p, hp⟩
        obtain ⟨hg2, hr2⟩ := ih2 hn ⟨q, hq⟩
        constructor
        · rw [confF_chooseU]; exact goodD_chooseU hg1 hg2
        · rw [confF_chooseU]; exact refDist_chooseSemU_cong hr1 hr2
  | dadd hmeet =>
      intro D ht _
      cases ht with
      | add hv hw =>
        cases hv with
        | ascRaw hr1 he1 _ _ =>
          cases hr1
          obtain ⟨he1a, _⟩ := he1; cases he1a
          cases hw with
          | ascRaw hr2 he2 _ _ =>
            cases hr2
            obtain ⟨he2a, _⟩ := he2; cases he2a
            simp only [emeetTy, Option.some.injEq] at hmeet
            subst hmeet
            exact gr_point
              (.ascRaw HasTyRaw.real ⟨HVTag.real, HVTag.real⟩
                GoodTy.real GoodTy.real) GoodTy.real
  | dmon _ ih => intro D ht hsat; exact ih ht hsat
  | dit _ ih =>
      intro D ht hsat
      cases ht with
      | ite _ hm hn =>
        obtain ⟨hg, hrd⟩ := ih hm hsat
        exact ⟨hg, refDist_hull_left hrd (wf_tm hn ctxGood_nil)⟩
  | dif _ ih =>
      intro D ht hsat
      cases ht with
      | ite _ hm hn =>
        obtain ⟨hg, hrd⟩ := ih hn hsat
        exact ⟨hg, refDist_hull_right hrd (wf_tm hm ctxGood_nil)⟩
  | derr =>
      intro D ht _
      cases ht with
      | errD hg => exact gr_errAt hg
  | dascOk hmeet hgε3 =>
      intro D ht _
      cases ht with
      | ascV hv hev2 hge2 hgσ' =>
        cases hv with
        | ascRaw hu hev1 hge1 _ =>
          exact gr_point
            (.ascRaw hu (hetransTy_invariant hev1 hev2 hge1 hge2 hmeet)
              hgε3 hgσ')
            hgσ'
  | dascErr _ =>
      intro D ht _
      cases ht with
      | ascV _ _ _ hgσ' => exact gr_point (.err hgσ') hgσ'
  | eAscV =>
      intro D ht _
      cases ht with
      | ascV _ _ _ hgσ' => exact gr_point (.err hgσ') hgσ'
  | eAddL =>
      intro D ht _
      cases ht with
      | add _ _ => exact gr_point (.err GoodTy.real) GoodTy.real
  | eAddR =>
      intro D ht _
      cases ht with
      | add _ _ => exact gr_point (.err GoodTy.real) GoodTy.real
  | eApp =>
      intro D ht _
      cases ht with
      | app hv _ =>
        cases hv with
        | err hg => cases hg with | arrow _ hgD => exact gr_errAt hgD
  | eIte hm hn =>
      intro D ht _
      cases ht with
      | ite _ hm' hn' =>
        obtain rfl := det_tm hm hm'
        obtain rfl := det_tm hn hn'
        exact gr_errAt (goodD_chooseU (wf_tm hm ctxGood_nil)
          (wf_tm hn ctxGood_nil))
  | dapp hdom hcod hred1 _ _ ih2 =>
      intro D0 ht hsat
      cases ht with
      | app hv hw => exact ih2 (dapp_contractum_typed hv hw hdom hcod hred1) hsat
  | @dlet m1 n ty C ns k1 k2 V wv Vk Fb hred1 htyμ hcell hbty
      hbodyred ihm ihcell ihbody =>
      intro D0 ht hsat
      cases ht with
      | @letin _ _ _ ty2 C2 _ F hm hbodyty =>
        injection det_tm htyμ hm with _ hty hC
        subst hty hC
        have hgμ : GoodD ⟨n, ty, C⟩ := wf_tm hm ctxGood_nil
        have hVvals := type_safety_vals hred1 hm
        -- bound term satisfiability, straight off the computed evidence's
        -- constraint (it *contains* a bound term solution)
        have hsatV : ∃ p, V.C p := by
          obtain ⟨x0, ω0, hω0, -⟩ := hsat
          obtain ⟨-, ⟨pp, hpp, -⟩, -⟩ := tagReorderD_C_dest hω0
          exact ⟨pp, hpp⟩
        obtain ⟨hgV, hreordV⟩ := ihm hm hsatV
        -- goodness of the computed evidence, from its satisfiability and the
        -- entrywise facts
        have hgood : GoodD (tagReorderD V.confF ⟨n, ty, C⟩).toF :=
          goodD_tagReorderD_sat hgV hgμ (reorderD_sat_of_refDist hsatV hreordV)
        -- every branch is well typed
        have hbrty : ∀ c,
            HasTyT [] ((ns (reorderDR V.confF ⟨n, ty, C⟩ c)).subErr (wv c) (Fb c)) (Fb c) :=
          fun c =>
            subErr_typed (dlet_cell_typed hVvals hgμ (hcell c)) (hbty c)
              (wf_tm (hbty c) (ctxGood_cons (hgμ.tys _) ctxGood_nil))
        -- branch-type alignment with the goal derivation's family
        have hFb : ∀ c, Fb c = F (reorderDR V.confF ⟨n, ty, C⟩ c) :=
          fun c => det_tm (hbty c) (hbodyty _)
        constructor
        · -- goodness of the result configuration type
          refine goodD_confF_wsum (fun ω hω => (tagReorderD_C_dest hω).1)
            ?_ ?_ hsat ?_ ?_
          · intro ω hω
            obtain ⟨-, ⟨pp, hpp, hsum⟩, -⟩ := tagReorderD_C_dest hω
            rw [hsum]
            exact hgV.good.mass pp hpp
          · intro ω ω' hω hω' t ht0 ht1
            exact hgood.good.convex ω ω' hω hω' t ht0 ht1
          · rintro c ⟨ω, hω, hc⟩ hbs
            exact ((ihbody c (hbrty c) hbs).1).good
          · intro c i
            exact wf_val (type_safety_vals (hbodyred c) (hbrty c) i)
              ctxGood_nil
        · -- refinement into the `let` result, solution by solution; the
          -- target marginal is the constraint's own right-marginal clause
          -- (`tagReorderD_pushR`)
          refine refDist_wsum_letSem
            (fun i => wf_tm (hbodyty i)
              (ctxGood_cons (hgμ.tys i) ctxGood_nil))
            (reorderDR V.confF ⟨n, ty, C⟩) (fun ω hω c => (tagReorderD_C_dest hω).1 c)
            (fun ω hω => tagReorderD_pushR hω) ?_
          rintro c ⟨ω, hω, hc⟩ hbs
          have h := (ihbody c (hbrty c) hbs).2
          rw [hFb c] at h
          exact h
  | @dascD εd m μ μb k1 V wv hvR hredm htyμ hsat hcell ihm =>
      intro D ht _
      cases ht with
      | ascT htm hval hgεd hgμb =>
        -- satisfiability of the composed formula gives that of the ascribed term
        -- (the formulas accumulate), and with it the goodness of its runtime
        -- type
        have hsatV : ∃ p, V.C p := by
          obtain ⟨w, hw⟩ := hsat
          obtain ⟨⟨wr, hwr⟩, -⟩ := emeetD_C_dest hw
          obtain ⟨-, ⟨p, hp, -⟩, -⟩ :=
            tagReorderD_C_dest (D1 := V.confF) (D2 := μ) hwr
          exact ⟨p, hp⟩
        have h := dascD_safety (fun c => emeetD_r_lt_of_hvalid hvR.2 c) hsat
          (ihm htyμ hsatV).1 (wf_tm htyμ ctxGood_nil)
          hval.2 hgεd hgμb (type_safety_vals hredm htyμ) hcell
        exact ⟨h.good, h.reord⟩
  | @dascDErr εd m μ μb k1 V _ hredm htyμ hnsat ihm =>
      intro D ht _
      cases ht with
      | ascT htm _ _ hgμb => exact gr_errAt hgμb

/-- Lemma 42 (preservation for TPLC), satisfiability part: the result formula of
every reduction of a closed well-typed term is satisfiable. For (Dlet) the
formula is the constraint of the computed routing evidence together with the
branches' formulas: the constraint is satisfiable because the bound term's
runtime type refines its static type (`type_safety_gr` on the subderivation,
called with the satisfiability of the induction hypothesis, and
`reorderD_sat_of_refDist`), and the branches are satisfiable by induction. For
(D::μ) satisfiability is the rule's firing condition. -/
theorem type_safety_sat : ∀ {m : Tm} {k : ℕ} {V : DConf}, m ⇓[k] V →
    ∀ {D : FDist}, ⊢ m : D → ∃ x, V.C x := by
  intro m k V hr
  induction hr with
  | dv => exact fun _ => ⟨fun _ => 1, rfl⟩
  | dchoice ha0 ha1 _ _ ih1 ih2 =>
      intro D ht
      cases ht with
      | choice _ _ hm hn =>
        obtain ⟨p, hp⟩ := ih1 hm
        obtain ⟨q, hq⟩ := ih2 hn
        exact ⟨_, p, q, hp, hq, rfl⟩
  | dchoiceU _ _ ih1 ih2 =>
      intro D ht
      cases ht with
      | choiceU hm hn =>
        obtain ⟨p, hp⟩ := ih1 hm
        obtain ⟨q, hq⟩ := ih2 hn
        exact ⟨_, 1, zero_le_one, le_refl 1, p, q, hp, hq, rfl⟩
  | dadd _ => exact fun _ => ⟨fun _ => 1, rfl⟩
  | dmon _ ih => exact fun ht => ih ht
  | dit _ ih =>
      intro D ht
      cases ht with
      | ite _ hm _ => exact ih hm
  | dif _ ih =>
      intro D ht
      cases ht with
      | ite _ _ hn => exact ih hn
  | derr =>
      intro D ht
      cases ht with
      | errD hg => exact hg.good.sat
  | dascOk _ _ => exact fun _ => ⟨fun _ => 1, rfl⟩
  | dascErr _ => exact fun _ => ⟨fun _ => 1, rfl⟩
  | eAscV => exact fun _ => ⟨fun _ => 1, rfl⟩
  | eAddL => exact fun _ => ⟨fun _ => 1, rfl⟩
  | eAddR => exact fun _ => ⟨fun _ => 1, rfl⟩
  | eApp =>
      intro D ht
      cases ht with
      | app hv _ =>
        cases hv with
        | err hg => cases hg with | arrow _ hgD => exact hgD.good.sat
  | eIte hm hn =>
      intro D ht
      cases ht with
      | ite _ hm' hn' =>
        obtain rfl := det_tm hm hm'
        obtain rfl := det_tm hn hn'
        exact (goodD_chooseU (wf_tm hm ctxGood_nil)
          (wf_tm hn ctxGood_nil)).good.sat
  | dapp hdom hcod hred1 _ _ ih2 =>
      intro D0 ht
      cases ht with
      | app hv hw => exact ih2 (dapp_contractum_typed hv hw hdom hcod hred1)
  | @dlet m1 n ty C ns k1 k2 V wv Vk Fb hred1 htyμ hcell hbty
      hbodyred ihm ihcell ihbody =>
      intro D0 ht
      cases ht with
      | @letin _ _ _ ty2 C2 _ F hm hbodyty =>
        injection det_tm htyμ hm with _ hty hC
        subst hty hC
        have hgμ : GoodD ⟨n, ty, C⟩ := wf_tm hm ctxGood_nil
        have hVvals := type_safety_vals hred1 hm
        have hsatV : ∃ p, V.C p := ihm hm
        obtain ⟨hgV, hreordV⟩ := type_safety_gr hred1 hm hsatV
        -- the constraint of the computed evidence is satisfiable
        have hsater : ∃ ω, (tagReorderD V.confF ⟨n, ty, C⟩).toF.C ω := by
          rw [tagReorderD_toF]
          exact reorderD_sat_of_refDist (D1 := V.confF) hsatV hreordV
        -- every reduced branch has a satisfiable formula
        have hbsat : ∀ c, ∃ bc, (Vk c).C bc := fun c =>
          ihbody c (subErr_typed (dlet_cell_typed hVvals hgμ (hcell c)) (hbty c)
            (wf_tm (hbty c) (ctxGood_cons (hgμ.tys _) ctxGood_nil)))
        obtain ⟨ω, hω⟩ := hsater
        choose b hb using hbsat
        exact ⟨fun c => ω (finSigmaFinEquiv.symm c).1 *
            b _ (finSigmaFinEquiv.symm c).2,
          ω, hω, b, fun k _ => hb k, fun c => rfl⟩
  | @dascD εd m μ μb k1 V wv hvR hredm htyμ hsat hcell ihm =>
      -- the result formula is that of the computed evidence, and its
      -- satisfiability is the rule's firing condition
      intro D ht
      exact hsat
  | @dascDErr εd m μ μb k1 V _ hredm htyμ hnsat ihm =>
      -- the error's formula is the target type's, satisfiable by goodness
      intro D ht
      cases ht with
      | ascT _ _ _ hgμb => exact hgμb.good.sat

/-- Lemma 42 (preservation for TPLC): every reduction of a closed well-typed
term lands in a well-typed configuration whose runtime type is good and refines
the static type.  The clause on entries is `entriesIn_red`. -/
theorem type_safety {m : Tm} {k : ℕ} {V : DConf} (hr : m ⇓[k] V)
    {D : FDist} (ht : ⊢ m : D) : DConfHasTy V D :=
  ⟨type_safety_vals hr ht,
    (type_safety_gr hr ht (type_safety_sat hr ht)).1,
    (type_safety_gr hr ht (type_safety_sat hr ht)).2⟩

/-! ## Ascriptions do not get stuck

Every value ascription reduces in one step (`ascV_total`), and every well-typed
distribution ascription whose ascribed term reduces has a reduction
(`dascD_total`): (D::μ) fires when its composed formula is satisfiable and
reduces to the error at the target type otherwise. -/


/-- Lemma 39 (one-step coercion of a value): every value ascription reduces in
one step, to a coerced value or to an error; rule (D::σ) branches on the
definedness of the meet, and an `error` operand propagates. -/
theorem ascV_total {v : Val} (hv : ⊢ v : v.tyEntry) (e : TagTy)
    (σt : FTy) : ∃ w, .ascV e v σt ⇓[1] DConf.point w :=
  (Val.coerce_total hv e σt).imp fun _ => red_ascV_of_coerce

/-- Every well-typed distribution ascription whose ascribed term reduces has a
reduction: to the mixture of the coercions at the entries when the composition
`emeetD (tagReorderD V.confF μ) εd` is defined, and to the error at the target
type otherwise. -/
theorem dascD_total {εd : TagD} {m : Tm} {μb : FDist} {k1 : ℕ} {V : DConf}
    (hred : Red m k1 V) (hty : HasTyT [] (.ascT εd m μb) μb) :
    ∃ k V', Red (.ascT εd m μb) k V' := by
  cases hty with
  | ascT htm hval hgεd hgμb =>
    rename_i μ
    by_cases hsat : ∃ w, (emeetD (tagReorderD V.confF μ) εd).toF.C w
    · -- the composition is defined: route entry by entry; the right tags name
      -- entries of the target type by the validity of `εd`
      have hR : ∀ c : Fin (emeetD (tagReorderD V.confF μ) εd).n,
          (emeetD (tagReorderD V.confF μ) εd).r c < μb.n :=
        fun c => hval.2.tag_lt _
      have hcells : ∀ c : Fin (emeetD (tagReorderD V.confF μ) εd).n, ∃ w,
          Red (.ascV ((emeetD (tagReorderD V.confF μ) εd).ty c)
            (V.val (reorderDL V.confF μ (meetDL (tagReorderD V.confF μ).toF εd.toF c)))
            (μb.ty ⟨_, hR c⟩)) 1 (DConf.point w) :=
        fun c => ascV_total (type_safety_vals hred htm _) _ _
      choose wv hwv using hcells
      exact ⟨k1 + 1, _, Red.dascD hval hred htm hsat hwv⟩
    · -- it is not defined: error at the target type
      exact ⟨k1 + 1, _, Red.dascDErr hval hred htm hsat⟩


/-! ## Entries of the result

The second part of Lemma 42: every entry of the runtime type of a result is an
entry of its static type.  Values are created by coercion to a written target
((D::σ), (D::μ), the entrywise coercions of (Dlet)) or copied by the congruences. -/

/-- Lemma 39 (one-step coercion of a value): coercing a value to `σ` produces a
value that displays `σ`, whether the coercion succeeds or errs. The entries of
the result of a distribution ascription are therefore the entries of the target
type. -/
theorem tyEntry_of_red_ascV {ε : TagTy} {v : Val} {σ : FTy} {w : Val}
    (h : .ascV ε v σ ⇓[1] DConf.point w) : w.tyEntry = σ :=
  Val.coerce_tyEntry (red_ascV_iff.1 h)


/-- Every entry of the runtime type of `V` is an entry of `D`: the last clause
of Lemma 42 and of Theorem 4. -/
def EntriesIn (V : DConf) (D : FDist) : Prop :=
  ∀ i : Fin V.n, ∃ j : Fin D.n, (V.val i).tyEntry = D.ty j


/-- If the type of a body is the type the `let` assigns to a branch, each of
its entries is an entry of the `let` result type. -/
theorem letSem_entry_of_eq {D : FDist} {F : Fin D.n → FDist} {G : FDist}
    (j0 : Fin D.n) (h : G = F j0) (j : Fin G.n) :
    ∃ t : Fin (letSem D F).n, (letSem D F).ty t = G.ty j := by
  subst h
  exact ⟨finSigmaFinEquiv ⟨j0, j⟩, letSem_ty_mk j0 j⟩

/-- Lemma 42 (preservation for TPLC), clause on entries: every entry of the
runtime type of a result is an entry of its static type.  Reduction creates no
new types: values are coerced to a written target or copied by the
congruences. -/
theorem entriesIn_red : ∀ {m : Tm} {k : ℕ} {V : DConf}, m ⇓[k] V →
    ∀ {D : FDist}, ⊢ m : D → EntriesIn V D := by
  intro m k V hr
  induction hr with
  | dv =>
      intro D ht
      cases ht with
      | val hv => exact fun _ => ⟨0, tyEntry_of_hasTy hv⟩
  | dchoice ha0 ha1 _ _ ih1 ih2 =>
      intro D ht i
      cases ht with
      | choice _ _ hm hn =>
        refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i
        · obtain ⟨j, hj⟩ := ih1 hm i1
          exact ⟨Fin.castAdd _ j, by
            simpa using hj⟩
        · obtain ⟨j, hj⟩ := ih2 hn i2
          exact ⟨Fin.natAdd _ j, by
            simpa using hj⟩
  | dchoiceU _ _ ih1 ih2 =>
      intro D ht i
      cases ht with
      | choiceU hm hn =>
        refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i
        · obtain ⟨j, hj⟩ := ih1 hm i1
          exact ⟨Fin.castAdd _ j, by
            simpa using hj⟩
        · obtain ⟨j, hj⟩ := ih2 hn i2
          exact ⟨Fin.natAdd _ j, by
            simpa using hj⟩
  | dadd hmeet =>
      intro D ht
      cases ht with
      | add _ _ => exact fun _ => ⟨0, rfl⟩
  | dmon _ ih => intro D ht; exact ih ht
  | dit _ ih =>
      intro D ht i
      cases ht with
      | ite _ hm _ =>
        obtain ⟨j, hj⟩ := ih hm i
        exact ⟨Fin.castAdd _ j, by
          simpa using hj⟩
  | dif _ ih =>
      intro D ht i
      cases ht with
      | ite _ _ hn =>
        obtain ⟨j, hj⟩ := ih hn i
        exact ⟨Fin.natAdd _ j, by
          simpa using hj⟩
  | derr =>
      intro D ht
      cases ht with
      | errD hg => exact fun i => ⟨i, rfl⟩
  | dascOk hmeet hgε3 =>
      intro D ht
      cases ht with
      | ascV _ _ _ _ => exact fun _ => ⟨0, rfl⟩
  | dascErr _ =>
      intro D ht
      cases ht with
      | ascV _ _ _ _ => exact fun _ => ⟨0, rfl⟩
  | eAscV =>
      intro D ht
      cases ht with
      | ascV _ _ _ _ => exact fun _ => ⟨0, rfl⟩
  | eAddL =>
      intro D ht
      cases ht with
      | add _ _ => exact fun _ => ⟨0, rfl⟩
  | eAddR =>
      intro D ht
      cases ht with
      | add _ _ => exact fun _ => ⟨0, rfl⟩
  | eApp =>
      intro D ht
      cases ht with
      | app hv _ =>
        cases hv with
        | err hg => exact fun i => ⟨i, rfl⟩
  | eIte hm hn =>
      intro D ht
      cases ht with
      | ite _ hm' hn' =>
        obtain rfl := det_tm hm hm'
        obtain rfl := det_tm hn hn'
        exact fun i => ⟨i, rfl⟩
  | dapp hdom hcod hred1 _ _ ih2 =>
      intro D0 ht
      cases ht with
      | app hv hw => exact ih2 (dapp_contractum_typed hv hw hdom hcod hred1)
  | @dlet m1 n ty C ns k1 k2 V wv Vk Fb hred1 htyμ hcell hbty
      hbodyred ihm ihcell ihbody =>
      intro D0 ht
      cases ht with
      | @letin _ _ _ ty2 C2 _ F hm hbodyty =>
        injection det_tm htyμ hm with _ hty hC
        subst hty hC
        have hgμ : GoodD ⟨n, ty, C⟩ := wf_tm hm ctxGood_nil
        have hVvals := type_safety_vals hred1 hm
        intro i
        have hwv := dlet_cell_typed hVvals hgμ (hcell (finSigmaFinEquiv.symm i).1)
        have hgFb : GoodD (Fb (finSigmaFinEquiv.symm i).1) :=
          wf_tm (hbty (finSigmaFinEquiv.symm i).1)
            (ctxGood_cons (hgμ.tys _) ctxGood_nil)
        obtain ⟨j, hj⟩ := ihbody (finSigmaFinEquiv.symm i).1
          (subErr_typed hwv (hbty (finSigmaFinEquiv.symm i).1) hgFb)
          (finSigmaFinEquiv.symm i).2
        have hFb : Fb (finSigmaFinEquiv.symm i).1
            = F (reorderDR V.confF ⟨n, ty, C⟩ (finSigmaFinEquiv.symm i).1) :=
          det_tm (hbty (finSigmaFinEquiv.symm i).1) (hbodyty _)
        obtain ⟨t, ht'⟩ := letSem_entry_of_eq (D := ⟨n, ty, C⟩) (F := F)
          (reorderDR V.confF ⟨n, ty, C⟩ (finSigmaFinEquiv.symm i).1) hFb j
        exact ⟨t, by rw [ht']; exact hj⟩
  | @dascD εd m μ μb k1 V wv hvR hredm htyμ hsat hcell ihm =>
      intro D ht
      cases ht with
      | ascT htm hval hgεd hgμb =>
        exact fun c => ⟨⟨_, emeetD_r_lt_of_hvalid hvR.2 c⟩, tyEntry_of_red_ascV (hcell c)⟩
  | @dascDErr εd m μ μb k1 V _ hredm htyμ hnsat ihm =>
      intro D ht
      cases ht with
      | ascT htm _ _ hgμb => exact fun i => ⟨i, rfl⟩


/-- Convergence of a TPLC term, the article's `⇓`: some big-step reduction
exists. -/
def Converges (m : Tm) : Prop := ∃ (k : ℕ) (V : DConf), Red m k V


/-- The derivation index of every reduction is at least one. -/
theorem red_index_pos {m : Tm} {k : ℕ} {V : DConf} (h : Red m k V) : 1 ≤ k := by
  cases h <;> omega


/-- Divergence of a TPLC term, the article's `⇑`: no big-step reduction
exists. -/
def Diverges (m : Tm) : Prop := ¬ Converges m

/-- Theorem 4 (type safety for GPLC), stated for a closed well-typed TPLC term: it
converges to a well-typed configuration whose runtime type refines the static
type and whose entries are all entries of it, or it diverges.  Case 1 is
`type_safety` with `entriesIn_red`; case 2 is its complement. -/
theorem type_safety_converges_or_diverges {m : Tm} {D : FDist} (ht : HasTyT [] m D) :
    (∃ (k : ℕ) (V : DConf), Red m k V ∧ DConfHasTy V D ∧ EntriesIn V D) ∨
      Diverges m := by
  by_cases h : Converges m
  · obtain ⟨k, V, hr⟩ := h
    exact Or.inl ⟨k, V, hr, type_safety hr ht, entriesIn_red hr ht⟩
  · exact Or.inr h

/-- Theorem 4 (type safety for GPLC).  The source term elaborates (Lemma 11,
`elaboration_preserves_types_closed`) and `type_safety_converges_or_diverges`
applies to the elaborated term.  As in the article, convergence and divergence of
a GPLC term quantify existentially over its elaboration. -/
theorem _root_.GradualProb.GPLC.type_safety {m : GPLC.Tm} {D : FDist} (hty : ⊢ m : D) :
    ∃ tm, ⊢ m : D ⇝ tm ∧
      ((∃ (k : ℕ) (V : DConf), tm ⇓[k] V ∧ DConfHasTy V D ∧ EntriesIn V D) ∨
        Diverges tm) := by
  obtain ⟨tm, hel, ht⟩ := elaboration_preserves_types_closed hty
  exact ⟨tm, hel, type_safety_converges_or_diverges ht⟩

/-! ## Shapes of closed values and inversion of the arrow evidence -/

/-- An evidence hereditarily valid against `Real` is `Real`. -/
theorem hvtag_real {π : Side} : ∀ {e : TagTy}, HVTag π e .real → e = .real
  | _, .real => rfl

/-- An evidence hereditarily valid against `Bool` is `Bool`. -/
theorem hvtag_bool {π : Side} : ∀ {e : TagTy}, HVTag π e .bool → e = .bool
  | _, .bool => rfl

/-- A closed value of type `Real` is either a literal ascribed with the
evidence `Real` or an error. -/
theorem closed_real_val_shape {v : Val} (h : HasTyV [] v .real) :
    (∃ r : ℝ, v = .asc .real (.real r) .real) ∨ (∃ σe : FTy, v = .err σe) := by
  cases h with
  | var hx => simp at hx
  | @ascRaw _ ε u σu σ hu he _ _ =>
    obtain rfl : ε = .real := hvtag_real he.2
    cases he.1 with
    | real => cases hu with | real => exact .inl ⟨_, rfl⟩
    | unk => cases hu
  | err _ => exact .inr ⟨_, rfl⟩

/-- A closed value of type `Bool` is a boolean literal or an error (the mirror
of `closed_real_val_shape`). -/
theorem closed_bool_val_shape {v : Val} (h : HasTyV [] v .bool) :
    (∃ b : Bool, v = .asc .bool (.bool b) .bool) ∨ (∃ σe : FTy, v = .err σe) := by
  cases h with
  | var hx => simp at hx
  | @ascRaw _ ε u σu σ hu he _ _ =>
    obtain rfl : ε = .bool := hvtag_bool he.2
    cases he.1 with
    | bool => cases hu with | bool => exact .inl ⟨_, rfl⟩
    | unk => cases hu
  | err _ => exact .inr ⟨_, rfl⟩

/-- Inversion of `tagDom`/`tagCod`: only an arrow evidence has them. -/
theorem tagDom_arrow : ∀ {e s : TagTy} {dd : TagD},
    tagDom e = some s → tagCod e = some dd →
    ∃ s0, e = .arrow s0 dd ∧ s = s0.flip
  | .arrow s0 d0, s, dd, hd, hc => by
      simp only [tagDom, Option.some.injEq] at hd
      simp only [tagCod, Option.some.injEq] at hc
      exact ⟨s0, by rw [hc], hd.symm⟩
  | .real, _, _, hd, _ => nomatch hd
  | .bool, _, _, hd, _ => nomatch hd
  | .unk, _, _, hd, _ => nomatch hd

end GradualProb.TPLC
