import GradualProb.TPLC.Meet

/-!
# Example 6: the meet of two evidences

This module checks the computation of Example 6 with the meet of
`TPLC/Meet`: the evidences of the example are computed rather than
postulated, and both compositions of the example are defined.

## Main results

* `prog_precise_step`: the precise composition `ε₁ ∘ ε₂` is defined.
* `prog_less_precise_step_coverage_free`: the less precise composition `ε₁′ ∘ ε₂′`
  is defined.
-/

open scoped BigOperators

namespace GradualProb.TPLC

open GradualProb.GPLC
open Classical

/-! ## Example 6: the two compositions

The evidences of Example 6, computed with the meet rather than postulated.
The two programs of the example cast a function twice, and the ascription in
the body composes the two evidences. `prog_precise_step` shows that the
precise composition `ε₁ ∘ ε₂` is defined, even for annotation consistency;
`prog_less_precise_step_coverage_free` shows that the less precise composition
`ε₁′ ∘ ε₂′` is defined for runtime consistency (Figure 12): the extra entry of
`ε₁′` receives probability 0. -/

/-! ### The four simple types of Example 6 -/

/-- `σ_A = 𝔹 → {{ℝ¹}}`. -/
@[reducible] def sA : FTy := .arrow .bool (pointF .real)
/-- `σ_B = ℝ → {{𝔹¹}}`. -/
@[reducible] def sB : FTy := .arrow .real (pointF .bool)
/-- `σ_A′ = ? → {{ℝ¹}}`. -/
@[reducible] def sA' : FTy := .arrow .unk (pointF .real)
/-- `σ_B′ = ℝ → {{?¹}}`. -/
@[reducible] def sB' : FTy := .arrow .real (pointF .unk)

/-- `σ_A` is well-formed. -/
theorem goodTy_sA : GoodTy sA := .arrow .bool (goodD_point .real)
/-- `σ_B` is well-formed. -/
theorem goodTy_sB : GoodTy sB := .arrow .real (goodD_point .bool)
/-- `σ_A′` is well-formed. -/
theorem goodTy_sA' : GoodTy sA' := .arrow .unk (goodD_point .real)

/-- A two-entry distribution type `{{t0^?, t1^?}}` whose probabilities form any
probability vector. -/
@[reducible] def freeD (t0 t1 : FTy) : FDist :=
  .mk 2 (fun i => if (i : ℕ) = 0 then t0 else t1)
    (fun p => 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 0 + p 1 = 1)

/-- `freeD t0 t1` is well-formed when `t0` and `t1` are. -/
theorem goodD_freeD {t0 t1 : FTy} (h0 : GoodTy t0) (h1 : GoodTy t1) :
    GoodD (freeD t0 t1) := by
  refine GoodD.mk ⟨⟨fun _ => 1/2, by norm_num⟩, ?_, ?_, ?_⟩ ?_
  · rintro p ⟨ha, hb, _⟩ i
    fin_cases i
    · exact ha
    · exact hb
  · rintro p ⟨_, _, hs⟩
    rw [Fin.sum_univ_two]; exact hs
  · rintro p q ⟨ha, hb, hs⟩ ⟨ha', hb', hs'⟩ t ht ht1
    refine ⟨by positivity, by positivity, ?_⟩
    nlinarith [hs, hs']
  · intro i
    show GoodTy (if (i : ℕ) = 0 then t0 else t1)
    by_cases h : (i : ℕ) = 0
    · rw [if_pos h]; exact h0
    · rw [if_neg h]; exact h1

/-! ### Distribution types of the example -/

/-- `{{σ_A^?, σ_B^?}}`, the codomain of the precise function's type and of
the annotations `σ₁ = σ₂`. -/
@[reducible] def E1 : FDist := freeD sA sB
/-- `{{σ_A′^?, σ_B^?}}`, the codomain of the less precise function's type. -/
@[reducible] def E1' : FDist := freeD sA' sB

/-- `{{σ_A^?, σ_B^?}}` is well-formed. -/
theorem goodD_E1 : GoodD E1 := goodD_freeD goodTy_sA goodTy_sB

/-! ### Meets of two point distributions

Every entry of the meet of two point distributions has the same type, and
every solution of its formula sums to 1, so the size of the carrier never
needs to be computed. -/

/-- Every entry of the meet of the point distributions of `s` and `t` is
`s ⊓ t`. -/
theorem meetD_point_ty {s t m : FTy} (hm : meetTy s t = some m)
    (c : Fin (meetD (pointF s) (pointF t)).n) :
    (meetD (pointF s) (pointF t)).ty c = m := by
  show (meetTy s t).getD FTy.unk = m
  rw [hm]; rfl

/-- Every solution of the formula of the meet of two point distributions sums
to 1. -/
theorem meetD_point_sum {s t : FTy} {p : Fin (meetD (pointF s) (pointF t)).n → ℝ}
    (hp : (meetD (pointF s) (pointF t)).C p) : (∑ c, p c) = 1 :=
  ((sum_pushfwd (meetDL _ _) p).symm.trans (Fin.sum_univ_one _)).trans
    ((meetD_C_iff _ _ p).1 hp).1

/-! ### Consistent pairs and their meets -/

/-- Two consistent simple types give consistent point distributions. -/
theorem econsD_point {s t : FTy} (h : EConsTy s t) : EConsD (pointF s) (pointF t) :=
  .intro ⟨fun _ => 1, fun _ => 1, rfl, rfl, Lift.point rfl rfl h⟩

/-- The meet of the point distributions of two consistent simple types is
defined. -/
theorem meetD_point_sat {s t : FTy} (h : EConsTy s t) :
    ∃ p, (meetD (pointF s) (pointF t)).C p :=
  meetD_sat_iff_econsD.mpr (econsD_point h)

/-- `σ_A′ ∼̇ σ_A` in runtime consistency. -/
theorem econsTy_sA'_sA : EConsTy sA' sA := .arrow .unkL (econsD_point .real)
/-- `σ_B ∼̇ σ_B′` in runtime consistency. -/
theorem econsTy_sB_sB' : EConsTy sB sB' := .arrow .real (econsD_point .unkR)

/-- `σ_A′ ⊓ σ_A = 𝔹 → {{ℝ¹}}`. -/
@[reducible] noncomputable def MAA : FTy := .arrow .bool (meetD (pointF .real) (pointF .real))
/-- `σ_B ⊓ σ_B′ = ℝ → {{𝔹¹}}`. -/
@[reducible] noncomputable def MBB' : FTy := .arrow .real (meetD (pointF .bool) (pointF .unk))

/-- The meet `σ_A′ ⊓ σ_A` is defined and is `MAA`. -/
theorem meet_sA'_sA : meetTy sA' sA = some MAA := rfl
/-- The meet `σ_B ⊓ σ_B′` is defined and is `MBB'`. -/
theorem meet_sB_sB' : meetTy sB sB' = some MBB' := rfl

/-- Every element of `Fin 2` is `0` or `1`. -/
theorem fin2_cases : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide

/-! ### The diagonal coupling -/

/-- The diagonal coupling of two two-entry distributions, with weight `1/2`
on each diagonal pair. -/
noncomputable def Gd : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 1/2 else 0

/-- The diagonal coupling couples the two uniform weight vectors on two
entries (`IsCoupling.diag`). -/
theorem isCoupling_Gd :
    IsCoupling (fun _ : Fin 2 => (1/2 : ℝ)) (fun _ : Fin 2 => (1/2 : ℝ)) Gd :=
  .diag fun _ => by norm_num

/-- The diagonal coupling is positive only on the diagonal (`Supp.diag`). -/
theorem Gd_pos_diag {i j : Fin 2} (h : 0 < Gd i j) : i = j :=
  Supp.diag (fun _ : Fin 2 => (1/2 : ℝ)) i j h

/-! ### The evidences of the program

The precise program casts a function of type `ℝ → E1` to `σ₁ = ℝ → E1` and
then to `σ₂ = σ₁`; the less precise one casts a function of type `ℝ → E1'` to the
less precise annotation `σ₁′ = ℝ → Eaa` and then to `σ₂`. Each evidence is the meet
of the type of what is cast with the annotation, so `ε₁ = ε₂ = σ₁ ⊓ σ₁`,
`ε₁′ = (ℝ → E1') ⊓ σ₁′ = ℝ → (E1' ⊓ Eaa)` and
`ε₂′ = σ₁′ ⊓ σ₂ = ℝ → (Eaa ⊓ E1)`. -/

/-- `σ₁ = σ₂ = ℝ → {{σ_A^?, σ_B^?}}`, also the type of the precise
function. -/
@[reducible] def P1 : FTy := .arrow .real E1
/-- `{{σ_A′^?, σ_B′^?}}`, the codomain of the less precise annotation `σ₁′`. -/
@[reducible] def Eaa : FDist := freeD sA' sB'

/-- `σ₁` is well-formed. -/
theorem goodTy_P1 : GoodTy P1 := .arrow .real goodD_E1

/-! ### Consistency between meets of point distributions -/

/-- If `s ⊓ t = m`, `s′ ⊓ t′ = m′` and `m ∼̇ m′`, then the meets of the
corresponding point distributions are runtime consistent. -/
theorem econsD_meetD_meetD {s t m s' t' m' : FTy}
    (hm : meetTy s t = some m) (hm' : meetTy s' t' = some m')
    (hl : EConsTy s t) (hl' : EConsTy s' t') (hc : EConsTy m m') :
    EConsD (meetD (pointF s) (pointF t)) (meetD (pointF s') (pointF t')) := by
  obtain ⟨p, hp⟩ := meetD_point_sat hl
  obtain ⟨p', hp'⟩ := meetD_point_sat hl'
  exact EConsD.intro ⟨p, p', hp, hp', fun c c' => p c * p' c',
    ⟨fun c c' => mul_nonneg (meetD_C_nonneg hp c) (meetD_C_nonneg hp' c'),
      fun c => by rw [← Finset.mul_sum, meetD_point_sum hp', mul_one],
      fun c' => by rw [← Finset.sum_mul, meetD_point_sum hp, one_mul]⟩,
    fun c c' _ => by
      beta_reduce
      rw [meetD_point_ty hm c, meetD_point_ty hm' c']
      exact hc⟩

/-! ### Meets of the entries -/

/-- `σ_A′ ⊓ σ_A′ = ? → {{ℝ¹}}`. -/
@[reducible] noncomputable def MA'A' : FTy := .arrow .unk (meetD (pointF .real) (pointF .real))
/-- `σ_B′ ⊓ σ_B = ℝ → {{𝔹¹}}`. -/
@[reducible] noncomputable def MB'B : FTy := .arrow .real (meetD (pointF .unk) (pointF .bool))

/-- The meet `σ_A′ ⊓ σ_A′` is defined and is `MA'A'`. -/
theorem meet_sA'_sA' : meetTy sA' sA' = some MA'A' := rfl
/-- The meet `σ_B′ ⊓ σ_B` is defined and is `MB'B`. -/
theorem meet_sB'_sB : meetTy sB' sB = some MB'B := rfl

/-- The precise evidences: `ε₁ = ε₂ = σ₁ ⊓ σ₁`. -/
theorem meet_P1_P1 : meetTy P1 P1 = some (.arrow .real (meetD E1 E1)) := rfl

/-! ### The precise composition -/

/-- The point distributions of two inconsistent simple types are
inconsistent. -/
theorem not_econsD_point {s t : FTy} (h : ¬ EConsTy s t) :
    ¬ EConsD (pointF s) (pointF t) := by
  intro hc
  obtain ⟨p, q, hp, hq, w, hw, hsupp⟩ := hc.coup
  obtain ⟨j, hj⟩ := hw.exists_pos_of_left (i := 0) (hp ▸ one_pos)
  exact h (hsupp 0 j hj)

/-- `σ₁ ∼̇ σ₁` in runtime consistency. -/
theorem econsTy_P1_P1 : EConsTy P1 P1 := econsTy_of_consTy (ConsTy.refl goodTy_P1)
/-- `σ_A′ ∼̇ σ_A′` in runtime consistency. -/
theorem econsTy_sA'_sA' : EConsTy sA' sA' := econsTy_of_consTy (ConsTy.refl goodTy_sA')
/-- `σ_B′ ∼̇ σ_B` in runtime consistency. -/
theorem econsTy_sB'_sB : EConsTy sB' sB := .arrow .real (econsD_point .unkL)

/-- Example 6, precise side: `ε₁ ∘ ε₂` is defined. The two evidences are the
same well-formed type, so they are consistent even for annotation consistency
(`ConsTy`, Definition 4), by reflexivity. -/
theorem prog_precise_step :
    ConsTy (.arrow .real (meetD E1 E1)) (.arrow .real (meetD E1 E1)) :=
  ConsTy.refl (goodTy_meetTy goodTy_P1 goodTy_P1 econsTy_P1_P1 meet_P1_P1)

/-! ### The less precise composition -/

/-- Every entry of `Eaa ⊓ E1` pairs operand entries with the same index. -/
theorem diagR (c' : Fin (meetD Eaa E1).n) :
    meetDL Eaa E1 c' = meetDR Eaa E1 c' := by
  have hl := meetCell_cons Eaa E1 c'
  rcases fin2_cases (meetDL Eaa E1 c') with hi | hi <;>
    rcases fin2_cases (meetDR Eaa E1 c') with hj | hj <;> rw [hi, hj] <;> try rfl
  · rw [hi, hj] at hl
    exact absurd hl (fun hx => by cases hx with | arrow _ hDx =>
      exact not_econsD_point (fun hy => by cases hy) hDx)
  · rw [hi, hj] at hl
    exact absurd hl (fun hx => by cases hx with | arrow hs _ => cases hs)

/-- For each index `i`, some entry of `Eaa ⊓ E1` pairs the two entries `i`. -/
theorem right_cell_of (i : Fin 2) :
    ∃ c', meetDL Eaa E1 c' = i ∧ meetDR Eaa E1 c' = i := by
  refine meetD_cell_exists (D1 := Eaa) (D2 := E1) ?_
  rcases fin2_cases i with h | h <;> subst h
  · exact econsTy_sA'_sA
  · exact econsTy_sB'_sB

/-- Summing a constant `k` over the entries of `Eaa ⊓ E1` whose left tag is `i`
gives `k`: exactly one entry has left tag `i`. -/
theorem sum_right_ind (i : Fin 2) (k : ℝ) :
    (∑ c' : Fin (meetD Eaa E1).n, if meetDL Eaa E1 c' = i then k else 0) = k := by
  obtain ⟨c0, h0, h0'⟩ := right_cell_of i
  rw [Finset.sum_eq_single c0]
  · rw [if_pos h0]
  · intro b _ hb
    by_cases hbi : meetDL Eaa E1 b = i
    · exact absurd (meetD_cell_unique (hbi.trans h0.symm)
        (by rw [← diagR b, ← diagR c0, hbi, h0])) hb
    · rw [if_neg hbi]
  · intro hc0; exact absurd (Finset.mem_univ c0) hc0

/-- The diagonal coupling vanishes on the inconsistent pairs of entries of
`E1'` and `Eaa`. -/
theorem Gd_eq_zero_off_meet_E1'_Eaa : ∀ i j, ¬ EConsTy (E1'.ty i) (Eaa.ty j) → Gd i j = 0 := by
  intro i j h
  by_cases hij : i = j
  · exfalso; subst hij
    rcases fin2_cases i with hi | hi <;> subst hi
    · exact h econsTy_sA'_sA'
    · exact h econsTy_sB_sB'
  · rw [Gd, if_neg hij]

/-- The diagonal coupling vanishes on the inconsistent pairs of entries of
`Eaa` and `E1`. -/
theorem Gd_eq_zero_off_meet_Eaa_E1 : ∀ i j, ¬ EConsTy (Eaa.ty i) (E1.ty j) → Gd i j = 0 := by
  intro i j h
  by_cases hij : i = j
  · exfalso; subst hij
    rcases fin2_cases i with hi | hi <;> subst hi
    · exact h econsTy_sA'_sA
    · exact h econsTy_sB'_sB
  · rw [Gd, if_neg hij]

/-- The diagonal coupling solves the formula of `E1' ⊓ Eaa`. -/
theorem solL : (meetD E1' Eaa).C (fun c => Gd (meetDL E1' Eaa c) (meetDR E1' Eaa c)) :=
  meetD_C_of_coupling (p := fun _ => 1/2) (qs := fun _ => 1/2)
    ⟨by norm_num, by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num, by norm_num⟩
    isCoupling_Gd
    (fun i j hpos => Classical.byContradiction fun h =>
      hpos.ne' (Gd_eq_zero_off_meet_E1'_Eaa i j h))

/-- The diagonal coupling solves the formula of `Eaa ⊓ E1`. -/
theorem solR : (meetD Eaa E1).C (fun c => Gd (meetDL Eaa E1 c) (meetDR Eaa E1 c)) :=
  meetD_C_of_coupling (p := fun _ => 1/2) (qs := fun _ => 1/2)
    ⟨by norm_num, by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num, by norm_num⟩
    isCoupling_Gd
    (fun i j hpos => Classical.byContradiction fun h => hpos.ne' (Gd_eq_zero_off_meet_Eaa_E1 i j h))

/-- Example 6, less precise side: `ε₁′ ∘ ε₂′` is defined, that is, its operands are
runtime-consistent (`EConsTy`, Figure 12). The extra entry of `ε₁′` receives
probability 0, and the diagonal coupling closes. -/
theorem prog_less_precise_step_coverage_free :
    EConsTy (.arrow .real (meetD E1' Eaa)) (.arrow .real (meetD Eaa E1)) := by
  refine .arrow .real ?_
  refine EConsD.intro ⟨fun c => Gd (meetDL E1' Eaa c) (meetDR E1' Eaa c),
    fun c' => Gd (meetDL Eaa E1 c') (meetDR Eaa E1 c'), solL, solR,
    fun c c' => if meetDL Eaa E1 c' = meetDL E1' Eaa c
      then Gd (meetDL E1' Eaa c) (meetDR E1' Eaa c) else 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact fun c c' => ite_nonneg (isCoupling_Gd.nonneg _ _) le_rfl
  · intro c; exact sum_right_ind (meetDL E1' Eaa c) _
  · intro c'
    have hG : ∀ i j, ¬ EConsTy (E1'.ty i) (Eaa.ty j) →
        (if meetDL Eaa E1 c' = i then Gd i j else 0) = 0 := by
      intro i j h
      by_cases hij : meetDL Eaa E1 c' = i
      · rw [if_pos hij]; exact Gd_eq_zero_off_meet_E1'_Eaa i j h
      · rw [if_neg hij]
    have hsum := sum_meetD_grid (D1 := E1') (D2 := Eaa)
      (fun i j => if meetDL Eaa E1 c' = i then Gd i j else 0) hG
    show (∑ c, (if meetDL Eaa E1 c' = meetDL E1' Eaa c
        then Gd (meetDL E1' Eaa c) (meetDR E1' Eaa c) else 0))
      = Gd (meetDL Eaa E1 c') (meetDR Eaa E1 c')
    rw [hsum, ← diagR c']
    rcases fin2_cases (meetDL Eaa E1 c') with hi | hi <;> rw [hi] <;>
      simp [Gd, Fin.sum_univ_two] <;> norm_num
  · intro c c' hpos
    obtain ⟨h, hpos⟩ := pos_of_ite_pos hpos
    have hd : meetDL E1' Eaa c = meetDR E1' Eaa c := Gd_pos_diag hpos
    rw [meetD_ty', meetD_ty', ← hd, ← diagR c', h]
    rcases fin2_cases (meetDL E1' Eaa c) with hi | hi <;> rw [hi]
    · show EConsTy ((meetTy sA' sA').getD FTy.unk) ((meetTy sA' sA).getD FTy.unk)
      rw [meet_sA'_sA', meet_sA'_sA]
      exact .arrow .unkL (econsD_meetD_meetD rfl rfl .real .real .real)
    · show EConsTy ((meetTy sB sB').getD FTy.unk) ((meetTy sB' sB).getD FTy.unk)
      rw [meet_sB_sB', meet_sB'_sB]
      exact .arrow .real
        (econsD_meetD_meetD (meetTy_unk_right .bool) rfl .unkR .unkL .bool)

end GradualProb.TPLC
