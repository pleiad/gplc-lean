import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Couplings

Couplings of finite distributions and the lifting of a relation to
distributions (Definitions 2 and 3), with the constructions on couplings that
the development uses wherever the article lifts a relation. A distribution is
a family of points indexed by a finite type, with a vector of weights; a
symbolic distribution has, instead of the weights, the set of solutions of its
formula.

## Main definitions

* `IsCoupling p q w`: `w` is a coupling of the weight vectors `p` and `q`
  (Definition 2, condition 1).
* `Supp R w`: the positive cells of `w` lie in `R` (Definition 2, condition 2).
* `Lift R p q`: the lifting of `R` (Definition 2).
* `SymLift R ψ₁ ψ₂`: the lifting of `R` to symbolic distributions
  (Definition 3), which relates some solution of each constraint; and
  `SymLiftAll R ψ₁ ψ₂`, which relates every solution of `ψ₁` to some solution
  of `ψ₂`, the form that precision uses.
* `pushfwd f w`: the push-forward of the weights `w` along `f`; `massOf P val
  w`: the weight of a predicate.

## Main results

* `IsCoupling.diag`, `IsCoupling.point`, `IsCoupling.symm`, `IsCoupling.smul`,
  `IsCoupling.add`, `IsCoupling.reindex`: the diagonal coupling, the coupling
  of one-point distributions, transposition, scaling, sums and reindexing.
* `IsCoupling.glue`, `glue₂_pos`, `coupling_glue` (Lemma 26): two couplings
  sharing a middle marginal compose; `glue₃` is the three-index weight behind
  the composition.
* `IsCoupling.tensor`: the tensor composition of couplings behind Lemma 12.
* `IsCoupling.append`, `IsCoupling.sigma`, `IsCoupling.sigmaFin`,
  `Lift.sigmaFin`: the block-diagonal coupling of appended weight vectors and
  the product over a dependent sum.
* `isCoupling_pushfwd`, `isCoupling_pushfwd_prod`, `IsCoupling.restrict`:
  couplings from push-forwards, and the restriction of a coupling to the cells
  of its support.
* `sum_cells`, `isCoupling_restrict_cells`, `IsCoupling.restrict_of_supp`:
  sums and couplings over an injective enumeration of the cells of a support.
* `Lift.refl`, `Lift.symm`, `Lift.mono`, `Lift.comp`, `Lift.trans`;
  `SymLift.refl`, `SymLift.symm`, `SymLift.mono`, `SymLift.comp_left`,
  `SymLift.comp_right`; `SymLiftAll.refl`, `SymLiftAll.mono`,
  `SymLiftAll.trans`, `SymLiftAll.symLift`: reflexivity, symmetry,
  monotonicity and composition of the liftings.
* `Lift.congr`, `Lift.reindex`, `Lift.smul`, `Lift.append`, `Lift.stack`,
  `Lift.sigmaFin`, `Lift.pushfwd`, `Lift.pushfwd_prod`, `Lift.restrict`,
  `Lift.tensor`: the constructions above at the level of the lifting.
* `cov_append`, `cov_sigmaFin`: the coverage clauses of appended and
  concatenated families.
* `coupling_of_classMass`, `classMass_of_coupling`: for an equivalence
  relation `R`, a coupling supported on `R` exists iff the two distributions
  put equal probability on every `R`-class. This is the core of the
  distribution case of Lemma 2 (`SPLC.eqD_dist_iff_coupling`).
* `sum_sigma_proj`: sums over a dependent concatenation of index sets.

## Reading guide

The definitions come first, then the elementary facts (positivity and zero
cells), the constructions, the push-forward and the probability of a
predicate, the properties of the lifting, and the coverage of concatenated
families. The `(⟸)` direction of the class-probability characterization uses
the proportional coupling `w i j = p i · q j / M`, with `M` the common class
probability; Lean's convention `x / 0 = 0` handles empty classes. Reflexivity,
symmetry and transitivity of `R` are plain hypotheses.
-/

namespace GradualProb

open scoped BigOperators

/-! ## Couplings and liftings (Definitions 2 and 3)

A finite distribution is a family of points indexed by a finite type `ι`,
with a weight vector `p : ι → ℝ`. A symbolic distribution replaces the weight
vector by a constraint `ψ : (ι → ℝ) → Prop`, the set of solutions of its
formula. The relation `R` being lifted is stated on the indices: for families
of points `a` and `b`, the article's `a_i R b_j` is `R i j`. -/

section Defs

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Definition 2 (relation lifting), condition 1: `w` is a coupling of the
weight vectors `p` and `q`, that is, a nonnegative matrix whose rows sum to `p`
and whose columns sum to `q`. -/
structure IsCoupling (p : ι → ℝ) (q : κ → ℝ) (w : ι → κ → ℝ) : Prop where
  /-- The weights of a coupling are nonnegative. -/
  nonneg : ∀ i j, 0 ≤ w i j
  /-- The rows of a coupling sum to the left weights. -/
  row : ∀ i, ∑ j, w i j = p i
  /-- The columns of a coupling sum to the right weights. -/
  col : ∀ j, ∑ i, w i j = q j

/-- Definition 2 (relation lifting), condition 2: every pair to which `w`
gives positive weight is related by `R`. -/
def Supp {ι κ : Type*} (R : ι → κ → Prop) (w : ι → κ → ℝ) : Prop :=
  ∀ i j, 0 < w i j → R i j

/-- Definition 2 (relation lifting): the lifting `L_R(D_A, D_B)` of `R` to
the distributions with weights `p` and `q`. Some coupling of `p` and `q` has its
support in `R`; that coupling is the witness `ω ⊢ D_A R D_B`. -/
def Lift (R : ι → κ → Prop) (p : ι → ℝ) (q : κ → ℝ) : Prop :=
  ∃ w, IsCoupling p q w ∧ Supp R w

/-- Definition 3 (coupling over symbolic distributions): the lifting
`L_R(D_A^ψ₁, D_B^ψ₂)` of `R` to symbolic distributions. Some solution of `ψ₁`
and some solution of `ψ₂` are related by the lifting of `R`. This is the form
that consistency uses. -/
def SymLift (R : ι → κ → Prop) (ψ₁ : (ι → ℝ) → Prop) (ψ₂ : (κ → ℝ) → Prop) : Prop :=
  ∃ p q, ψ₁ p ∧ ψ₂ q ∧ Lift R p q

/-- The lifting of `R` to symbolic distributions in the form that precision
uses (Figure 8): every solution of `ψ₁` is related by the lifting of `R` to
some solution of `ψ₂`. -/
def SymLiftAll (R : ι → κ → Prop) (ψ₁ : (ι → ℝ) → Prop) (ψ₂ : (κ → ℝ) → Prop) : Prop :=
  ∀ p, ψ₁ p → ∃ q, ψ₂ q ∧ Lift R p q

end Defs

/-! ## Positivity -/

/-- A positive sum has a positive summand. -/
theorem exists_pos_of_sum_pos {ι : Type*} [Fintype ι] {f : ι → ℝ} (h : 0 < ∑ i, f i) :
    ∃ i, 0 < f i := by
  by_contra hno
  exact absurd (Finset.sum_nonpos fun i _ => not_lt.1 fun hi => hno ⟨i, hi⟩) (not_le.2 h)

/-- A nonnegative number that is not positive is zero. -/
theorem eq_zero_of_nonneg_of_not_pos {x : ℝ} (h0 : 0 ≤ x) (h : ¬ 0 < x) : x = 0 :=
  le_antisymm (not_lt.1 h) h0

/-- Both factors of a positive product of nonnegative numbers are positive. -/
theorem pos_and_pos_of_mul_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a * b) :
    0 < a ∧ 0 < b := by
  refine ⟨ha.lt_of_ne fun h0 => ?_, hb.lt_of_ne fun h0 => ?_⟩
  · rw [← h0, zero_mul] at h; exact lt_irrefl 0 h
  · rw [← h0, mul_zero] at h; exact lt_irrefl 0 h

/-- A positive guarded weight has a true guard and a positive weight. -/
theorem pos_of_ite_pos {P : Prop} [Decidable P] {a : ℝ} (h : 0 < (if P then a else 0)) :
    P ∧ 0 < a := by
  by_cases hP : P
  · exact ⟨hP, by rwa [if_pos hP] at h⟩
  · rw [if_neg hP] at h; exact absurd h (lt_irrefl 0)

/-- `x / c * c = x` when `c = 0` forces `x = 0`. -/
theorem div_mul_cancel_of_imp {x c : ℝ} (h : c = 0 → x = 0) : x / c * c = x := by
  by_cases hc : c = 0
  · rw [hc, h hc]; simp
  · field_simp

/-! ## Elementary facts on couplings -/

namespace IsCoupling

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι → ℝ} {q : κ → ℝ} {w : ι → κ → ℝ}

/-- A cell of a coupling is at most its row weight. -/
theorem le_left (h : IsCoupling p q w) (i : ι) (j : κ) : w i j ≤ p i := by
  rw [← h.row i]
  exact Finset.single_le_sum (f := fun j => w i j) (fun j _ => h.nonneg i j) (Finset.mem_univ j)

/-- A cell of a coupling is at most its column weight. -/
theorem le_right (h : IsCoupling p q w) (i : ι) (j : κ) : w i j ≤ q j := by
  rw [← h.col j]
  exact Finset.single_le_sum (f := fun i => w i j) (fun i _ => h.nonneg i j) (Finset.mem_univ i)

/-- The left weights of a coupling are nonnegative. -/
theorem left_nonneg (h : IsCoupling p q w) (i : ι) : 0 ≤ p i := by
  rw [← h.row i]; exact Finset.sum_nonneg fun j _ => h.nonneg i j

/-- The right weights of a coupling are nonnegative. -/
theorem right_nonneg (h : IsCoupling p q w) (j : κ) : 0 ≤ q j := by
  rw [← h.col j]; exact Finset.sum_nonneg fun i _ => h.nonneg i j

/-- A positive cell has a positive row weight. -/
theorem left_pos (h : IsCoupling p q w) {i : ι} {j : κ} (hpos : 0 < w i j) : 0 < p i :=
  lt_of_lt_of_le hpos (h.le_left i j)

/-- A positive cell has a positive column weight. -/
theorem right_pos (h : IsCoupling p q w) {i : ι} {j : κ} (hpos : 0 < w i j) : 0 < q j :=
  lt_of_lt_of_le hpos (h.le_right i j)

/-- A row of weight zero is zero. -/
theorem eq_zero_of_left (h : IsCoupling p q w) {i : ι} (hi : p i = 0) (j : κ) : w i j = 0 :=
  le_antisymm (hi ▸ h.le_left i j) (h.nonneg i j)

/-- A column of weight zero is zero. -/
theorem eq_zero_of_right (h : IsCoupling p q w) {j : κ} (hj : q j = 0) (i : ι) : w i j = 0 :=
  le_antisymm (hj ▸ h.le_right i j) (h.nonneg i j)

/-- A row of positive weight has a positive cell. -/
theorem exists_pos_of_left (h : IsCoupling p q w) {i : ι} (hi : 0 < p i) : ∃ j, 0 < w i j :=
  exists_pos_of_sum_pos (h.row i ▸ hi)

/-- A column of positive weight has a positive cell. -/
theorem exists_pos_of_right (h : IsCoupling p q w) {j : κ} (hj : 0 < q j) : ∃ i, 0 < w i j :=
  exists_pos_of_sum_pos (h.col j ▸ hj)

/-- The two sides of a coupling have the same total weight. -/
theorem sum_eq (h : IsCoupling p q w) : ∑ i, p i = ∑ j, q j := by
  rw [← Finset.sum_congr rfl fun i _ => h.row i, ← Finset.sum_congr rfl fun j _ => h.col j]
  exact Finset.sum_comm

/-- A coupling of `p` and `q` is a coupling of any weights equal to them. -/
theorem congr {p' : ι → ℝ} {q' : κ → ℝ} (h : IsCoupling p q w) (hp : ∀ i, p i = p' i)
    (hq : ∀ j, q j = q' j) : IsCoupling p' q' w :=
  ⟨h.nonneg, fun i => (h.row i).trans (hp i), fun j => (h.col j).trans (hq j)⟩

end IsCoupling

/-- Outside the support relation a nonnegative weight is zero. -/
theorem Supp.eq_zero {ι κ : Type*} {R : ι → κ → Prop} {w : ι → κ → ℝ} (h : Supp R w)
    {i : ι} {j : κ} (h0 : 0 ≤ w i j) (hR : ¬ R i j) : w i j = 0 :=
  eq_zero_of_nonneg_of_not_pos h0 fun hpos => hR (h i j hpos)

/-- The support condition is monotone in the relation. -/
theorem Supp.mono {ι κ : Type*} {R S : ι → κ → Prop} {w : ι → κ → ℝ} (h : Supp R w)
    (hRS : ∀ i j, R i j → S i j) : Supp S w :=
  fun i j hpos => hRS i j (h i j hpos)

/-! ## Constructions of couplings -/

section Constructions

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι → ℝ} {q : κ → ℝ} {w : ι → κ → ℝ}

/-- The diagonal coupling of a weight vector with itself. -/
theorem IsCoupling.diag [DecidableEq ι] {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) :
    IsCoupling p p (fun i j => if i = j then p i else 0) where
  nonneg i _ := ite_nonneg (hp i) le_rfl
  row i := by simp
  col j := by simp

omit [Fintype ι] in
/-- The diagonal coupling is supported on equal indices. -/
theorem Supp.diag [DecidableEq ι] (p : ι → ℝ) :
    Supp (fun i j => i = j) (fun i j => if i = j then p i else 0) :=
  fun _ _ hpos => (pos_of_ite_pos hpos).1

/-- The coupling of two one-point distributions. -/
theorem IsCoupling.point {p q : Fin 1 → ℝ} (hp : p 0 = 1) (hq : q 0 = 1) :
    IsCoupling p q (fun _ _ => 1) where
  nonneg _ _ := zero_le_one
  row i := by rw [Fin.sum_univ_one, Subsingleton.elim i 0, hp]
  col j := by rw [Fin.sum_univ_one, Subsingleton.elim j 0, hq]

/-- The transpose of a coupling. -/
theorem IsCoupling.symm (h : IsCoupling p q w) : IsCoupling q p (fun j i => w i j) :=
  ⟨fun j i => h.nonneg i j, h.col, h.row⟩

omit [Fintype ι] [Fintype κ] in
/-- The transpose of a matrix supported on `R` is supported on the converse. -/
theorem Supp.symm {R : ι → κ → Prop} (h : Supp R w) : Supp (fun j i => R i j) (fun j i => w i j) :=
  fun j i => h i j

/-- Scaling a coupling by a nonnegative factor. -/
theorem IsCoupling.smul (h : IsCoupling p q w) {a : ℝ} (ha : 0 ≤ a) :
    IsCoupling (fun i => a * p i) (fun j => a * q j) (fun i j => a * w i j) :=
  ⟨fun i j => mul_nonneg ha (h.nonneg i j), fun i => by rw [← Finset.mul_sum, h.row],
    fun j => by rw [← Finset.mul_sum, h.col]⟩

/-- The sum of two couplings. -/
theorem IsCoupling.add {p' : ι → ℝ} {q' : κ → ℝ} {w' : ι → κ → ℝ}
    (h : IsCoupling p q w) (h' : IsCoupling p' q' w') :
    IsCoupling (fun i => p i + p' i) (fun j => q j + q' j) (fun i j => w i j + w' i j) :=
  ⟨fun i j => add_nonneg (h.nonneg i j) (h'.nonneg i j),
    fun i => by rw [Finset.sum_add_distrib, h.row, h'.row],
    fun j => by rw [Finset.sum_add_distrib, h.col, h'.col]⟩

/-- Transport of a coupling along bijections of the two index types. -/
theorem IsCoupling.reindex {ι' κ' : Type*} [Fintype ι'] [Fintype κ'] (h : IsCoupling p q w)
    (e₁ : ι' ≃ ι) (e₂ : κ' ≃ κ) :
    IsCoupling (fun i => p (e₁ i)) (fun j => q (e₂ j)) (fun i j => w (e₁ i) (e₂ j)) :=
  ⟨fun _ _ => h.nonneg _ _,
    fun i => by rw [← h.row]; exact Equiv.sum_comp e₂ (fun j => w (e₁ i) j),
    fun j => by rw [← h.col]; exact Equiv.sum_comp e₁ (fun i => w i (e₂ j))⟩

/-- The product coupling of two nonnegative weight vectors of total weight 1. -/
theorem IsCoupling.prod {p : ι → ℝ} {q : κ → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ j, q j = 1) : IsCoupling p q (fun i j => p i * q j) where
  nonneg i j := mul_nonneg (hp i) (hq j)
  row i := by rw [← Finset.mul_sum, hq1, mul_one]
  col j := by rw [← Finset.sum_mul, hp1, one_mul]

end Constructions

/-! ### Composition (Lemma 26)

Two couplings that share a middle marginal `q` compose. The three-index
weight `glue₃` distributes the weight of each middle point; summing it over
the middle index gives the composed coupling `glue₂`. -/

section Glue

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
  {p : ι → ℝ} {q : κ → ℝ} {r : μ → ℝ} {w₁ : ι → κ → ℝ} {w₂ : κ → μ → ℝ}

/-- The three-index weight `w₁ i j · w₂ j k / q j` behind the composition of
two couplings through their shared marginal `q`. -/
noncomputable def glue₃ (q : κ → ℝ) (w₁ : ι → κ → ℝ) (w₂ : κ → μ → ℝ) (i : ι) (j : κ) (k : μ) : ℝ :=
  w₁ i j * w₂ j k / q j

/-- The composition `∑_j w₁ i j · w₂ j k / q j` of two couplings through
their shared marginal `q`. -/
noncomputable def glue₂ (q : κ → ℝ) (w₁ : ι → κ → ℝ) (w₂ : κ → μ → ℝ) (i : ι) (k : μ) : ℝ :=
  ∑ j, glue₃ q w₁ w₂ i j k

/-- The three-index weight is nonnegative. -/
theorem glue₃_nonneg (h₁ : IsCoupling p q w₁) (h₂ : IsCoupling q r w₂) (i : ι) (j : κ) (k : μ) :
    0 ≤ glue₃ q w₁ w₂ i j k :=
  div_nonneg (mul_nonneg (h₁.nonneg i j) (h₂.nonneg j k)) (h₁.right_nonneg j)

/-- Summing the three-index weight over the last index gives back `w₁`. -/
theorem sum_glue₃_right (h₁ : IsCoupling p q w₁) (h₂ : IsCoupling q r w₂) (i : ι) (j : κ) :
    ∑ k, glue₃ q w₁ w₂ i j k = w₁ i j := by
  have hfac : ∑ k, glue₃ q w₁ w₂ i j k = w₁ i j / q j * ∑ k, w₂ j k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by unfold glue₃; ring
  rw [hfac, h₂.row j]
  exact div_mul_cancel_of_imp fun hq => h₁.eq_zero_of_right hq i

/-- Summing the three-index weight over the first index gives back `w₂`. -/
theorem sum_glue₃_left (h₁ : IsCoupling p q w₁) (h₂ : IsCoupling q r w₂) (j : κ) (k : μ) :
    ∑ i, glue₃ q w₁ w₂ i j k = w₂ j k := by
  have hfac : ∑ i, glue₃ q w₁ w₂ i j k = w₂ j k / q j * ∑ i, w₁ i j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by unfold glue₃; ring
  rw [hfac, h₁.col j]
  exact div_mul_cancel_of_imp fun hq => h₂.eq_zero_of_left hq k

/-- A positive three-index weight comes from two positive cells. -/
theorem glue₃_pos (h₁ : IsCoupling p q w₁) (h₂ : IsCoupling q r w₂) {i : ι} {j : κ} {k : μ}
    (hpos : 0 < glue₃ q w₁ w₂ i j k) : 0 < w₁ i j ∧ 0 < w₂ j k := by
  unfold glue₃ at hpos
  have hnum : 0 < w₁ i j * w₂ j k := by
    rcases div_pos_iff.1 hpos with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · exact absurd h (not_lt.2 (h₁.right_nonneg j))
  exact pos_and_pos_of_mul_pos (h₁.nonneg i j) (h₂.nonneg j k) hnum

/-- Lemma 26 (composition of couplings): a coupling of `p` and `q` and a
coupling of `q` and `r` compose into a coupling of `p` and `r`. -/
theorem IsCoupling.glue (h₁ : IsCoupling p q w₁) (h₂ : IsCoupling q r w₂) :
    IsCoupling p r (glue₂ q w₁ w₂) where
  nonneg i k := Finset.sum_nonneg fun j _ => glue₃_nonneg h₁ h₂ i j k
  row i := by
    unfold glue₂
    rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ => sum_glue₃_right h₁ h₂ i j, h₁.row i]
  col k := by
    unfold glue₂
    rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ => sum_glue₃_left h₁ h₂ j k, h₂.col k]

/-- Lemma 26 (composition of couplings): a positive weight of the composed
coupling factors through a pair of positive cells. -/
theorem glue₂_pos (h₁ : IsCoupling p q w₁) (h₂ : IsCoupling q r w₂) {i : ι} {k : μ}
    (hpos : 0 < glue₂ q w₁ w₂ i k) : ∃ j, 0 < w₁ i j ∧ 0 < w₂ j k := by
  obtain ⟨j, hj⟩ := exists_pos_of_sum_pos (f := fun j => glue₃ q w₁ w₂ i j k) hpos
  exact ⟨j, glue₃_pos h₁ h₂ hj⟩

/-- The composed coupling is supported on the composition of the supports. -/
theorem Supp.glue {R : ι → κ → Prop} {S : κ → μ → Prop} (s₁ : Supp R w₁) (s₂ : Supp S w₂)
    (h₁ : IsCoupling p q w₁) (h₂ : IsCoupling q r w₂) :
    Supp (Relation.Comp R S) (glue₂ q w₁ w₂) := fun i k hpos =>
  let ⟨j, hj₁, hj₂⟩ := glue₂_pos h₁ h₂ hpos
  ⟨j, s₁ i j hj₁, s₂ j k hj₂⟩

end Glue

/-! ### Tensor composition -/

/-- Tensor composition of couplings, used for Lemma 12 (monotonicity of
evidence combination) at distribution types. A coupling `P` of `p₁` and `p₂`
and couplings `u` of `p₁` and `q₁`, `v` of `p₂` and `q₂` compose into a
coupling `Q` of `q₁` and `q₂` and a weight `W` between the two pair index
spaces, transporting `P` independently in each coordinate
(`W i j a b = P i j · u i a · v j b / (p₁ᵢ·p₂ⱼ)`, zero where a marginal is
zero). A positive weight of `W` factors through positive weights of `P`, `u`
and `v`. With the composition of couplings of Lemma 26 (the article's `⊙`),
`Q` is the composite of the transpose of `u`, `P` and `v`. -/
theorem IsCoupling.tensor {ι₁ ι₂ κ₁ κ₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype κ₁]
    [Fintype κ₂] {p₁ : ι₁ → ℝ} {p₂ : ι₂ → ℝ} {q₁ : κ₁ → ℝ} {q₂ : κ₂ → ℝ}
    {P : ι₁ → ι₂ → ℝ} {u : ι₁ → κ₁ → ℝ} {v : ι₂ → κ₂ → ℝ}
    (hP : IsCoupling p₁ p₂ P) (hu : IsCoupling p₁ q₁ u) (hv : IsCoupling p₂ q₂ v) :
    ∃ (Q : κ₁ → κ₂ → ℝ) (W : ι₁ → ι₂ → κ₁ → κ₂ → ℝ),
      IsCoupling q₁ q₂ Q ∧
      (∀ i j a b, 0 ≤ W i j a b) ∧
      (∀ i j, ∑ a, ∑ b, W i j a b = P i j) ∧
      (∀ a b, (∑ i, ∑ j, W i j a b) = Q a b) ∧
      (∀ i j a b, 0 < W i j a b → 0 < P i j ∧ 0 < u i a ∧ 0 < v j b) := by
  have hP1 : ∀ i, p₁ i = 0 → ∀ j, P i j = 0 := fun i h j => hP.eq_zero_of_left h j
  have hP2 : ∀ j, p₂ j = 0 → ∀ i, P i j = 0 := fun j h i => hP.eq_zero_of_right h i
  set W : ι₁ → ι₂ → κ₁ → κ₂ → ℝ :=
    fun i j a b => P i j * u i a * v j b / (p₁ i * p₂ j) with hWdef
  have hWnn : ∀ i j a b, 0 ≤ W i j a b := fun i j a b => by
    rw [hWdef]
    exact div_nonneg (mul_nonneg (mul_nonneg (hP.nonneg i j) (hu.nonneg i a)) (hv.nonneg j b))
      (mul_nonneg (hu.left_nonneg i) (hv.left_nonneg j))
  have hSb : ∀ i j a, (∑ b, W i j a b) = P i j * u i a / p₁ i := by
    intro i j a
    rcases eq_or_ne (p₂ j) 0 with h2 | h2
    · simp only [hWdef, hP2 j h2 i, zero_mul, zero_div, Finset.sum_const_zero]
    · have e : (∑ b, W i j a b) = P i j * u i a / (p₁ i * p₂ j) * ∑ b, v j b := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by rw [hWdef]; ring)
      rw [e, hv.row j]; field_simp
  have hSa : ∀ i j b, (∑ a, W i j a b) = P i j * v j b / p₂ j := by
    intro i j b
    rcases eq_or_ne (p₁ i) 0 with h1 | h1
    · simp only [hWdef, hP1 i h1 j, zero_mul, zero_div, Finset.sum_const_zero]
    · have e : (∑ a, W i j a b) = P i j * v j b / (p₁ i * p₂ j) * ∑ a, u i a := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun a _ => by rw [hWdef]; ring)
      rw [e, hu.row i]; field_simp
  have hWsum : ∀ i j, ∑ a, ∑ b, W i j a b = P i j := by
    intro i j
    rw [Finset.sum_congr rfl (fun a _ => hSb i j a)]
    rcases eq_or_ne (p₁ i) 0 with h1 | h1
    · simp only [hP1 i h1 j, zero_mul, zero_div, Finset.sum_const_zero]
    · have e : (∑ a, P i j * u i a / p₁ i) = P i j / p₁ i * ∑ a, u i a := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun a _ => by ring)
      rw [e, hu.row i]; field_simp
  refine ⟨fun a b => ∑ i, ∑ j, W i j a b, W, ⟨?_, ?_, ?_⟩, hWnn, hWsum, fun _ _ => rfl, ?_⟩
  · intro a b
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hWnn i j a b))
  · intro a
    calc ∑ b, ∑ i, ∑ j, W i j a b
        = ∑ i, ∑ j, ∑ b, W i j a b := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ i, ∑ j, P i j * u i a / p₁ i :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hSb i j a))
      _ = ∑ i, u i a := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rcases eq_or_ne (p₁ i) 0 with h1 | h1
          · simp only [hP1 i h1, zero_mul, zero_div, Finset.sum_const_zero]
            exact (hu.eq_zero_of_left h1 a).symm
          · have e : (∑ j, P i j * u i a / p₁ i) = (u i a / p₁ i) * ∑ j, P i j := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
            rw [e, hP.row i]; field_simp
      _ = q₁ a := hu.col a
  · intro b
    calc ∑ a, ∑ i, ∑ j, W i j a b
        = ∑ i, ∑ j, ∑ a, W i j a b := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ i, ∑ j, P i j * v j b / p₂ j :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hSa i j b))
      _ = ∑ j, v j b := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rcases eq_or_ne (p₂ j) 0 with h2 | h2
          · simp only [hP2 j h2, zero_mul, zero_div, Finset.sum_const_zero]
            exact (hv.eq_zero_of_left h2 b).symm
          · have e : (∑ i, P i j * v j b / p₂ j) = (v j b / p₂ j) * ∑ i, P i j := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
            rw [e, hP.col j]; field_simp
      _ = q₂ b := hv.col b
  · intro i j a b hpos
    rw [hWdef] at hpos
    have hnum : 0 < P i j * u i a * v j b := by
      rcases div_pos_iff.mp hpos with ⟨hx, _⟩ | ⟨_, hc⟩
      · exact hx
      · exact absurd hc (not_lt.2 (mul_nonneg (hu.left_nonneg i) (hv.left_nonneg j)))
    obtain ⟨hPu, hv0⟩ := pos_and_pos_of_mul_pos
      (mul_nonneg (hP.nonneg i j) (hu.nonneg i a)) (hv.nonneg j b) hnum
    obtain ⟨hP0, hu0⟩ := pos_and_pos_of_mul_pos (hP.nonneg i j) (hu.nonneg i a) hPu
    exact ⟨hP0, hu0, hv0⟩

/-! ### Block-diagonal coupling of appended vectors -/

section Append

variable {n₁ n₂ m₁ m₂ : ℕ} {p : Fin n₁ → ℝ} {p' : Fin n₂ → ℝ} {q : Fin m₁ → ℝ}
  {q' : Fin m₂ → ℝ} {u : Fin n₁ → Fin m₁ → ℝ} {v : Fin n₂ → Fin m₂ → ℝ}

/-- The block-diagonal matrix with blocks `u` and `v`. -/
def blockDiag (u : Fin n₁ → Fin m₁ → ℝ) (v : Fin n₂ → Fin m₂ → ℝ) :
    Fin (n₁ + n₂) → Fin (m₁ + m₂) → ℝ :=
  fun i => Fin.addCases
    (fun i₁ => Fin.addCases (fun j₁ => u i₁ j₁) (fun _ => 0))
    (fun i₂ => Fin.addCases (fun _ => 0) (fun j₂ => v i₂ j₂)) i

/-- The upper left block of `blockDiag u v` is `u`. -/
@[simp] theorem blockDiag_castAdd_castAdd (u : Fin n₁ → Fin m₁ → ℝ) (v : Fin n₂ → Fin m₂ → ℝ)
    (i : Fin n₁) (j : Fin m₁) : blockDiag u v (Fin.castAdd n₂ i) (Fin.castAdd m₂ j) = u i j := by
  simp [blockDiag]

/-- The upper right block of `blockDiag u v` is zero. -/
@[simp] theorem blockDiag_castAdd_natAdd (u : Fin n₁ → Fin m₁ → ℝ) (v : Fin n₂ → Fin m₂ → ℝ)
    (i : Fin n₁) (j : Fin m₂) : blockDiag u v (Fin.castAdd n₂ i) (Fin.natAdd m₁ j) = 0 := by
  simp [blockDiag]

/-- The lower left block of `blockDiag u v` is zero. -/
@[simp] theorem blockDiag_natAdd_castAdd (u : Fin n₁ → Fin m₁ → ℝ) (v : Fin n₂ → Fin m₂ → ℝ)
    (i : Fin n₂) (j : Fin m₁) : blockDiag u v (Fin.natAdd n₁ i) (Fin.castAdd m₂ j) = 0 := by
  simp [blockDiag]

/-- The lower right block of `blockDiag u v` is `v`. -/
@[simp] theorem blockDiag_natAdd_natAdd (u : Fin n₁ → Fin m₁ → ℝ) (v : Fin n₂ → Fin m₂ → ℝ)
    (i : Fin n₂) (j : Fin m₂) : blockDiag u v (Fin.natAdd n₁ i) (Fin.natAdd m₁ j) = v i j := by
  simp [blockDiag]

/-- Two couplings side by side: the block-diagonal matrix couples the appended
weight vectors. -/
theorem IsCoupling.append (hu : IsCoupling p q u) (hv : IsCoupling p' q' v) :
    IsCoupling (Fin.append p p') (Fin.append q q') (blockDiag u v) where
  nonneg i j := by
    induction i using Fin.addCases with
    | left i₁ =>
      induction j using Fin.addCases with
      | left j₁ => simpa using hu.nonneg i₁ j₁
      | right j₂ => simp
    | right i₂ =>
      induction j using Fin.addCases with
      | left j₁ => simp
      | right j₂ => simpa using hv.nonneg i₂ j₂
  row i := by
    induction i using Fin.addCases with
    | left i₁ => rw [Fin.sum_univ_add]; simp [hu.row]
    | right i₂ => rw [Fin.sum_univ_add]; simp [hv.row]
  col j := by
    induction j using Fin.addCases with
    | left j₁ => rw [Fin.sum_univ_add]; simp [hu.col]
    | right j₂ => rw [Fin.sum_univ_add]; simp [hv.col]

/-- The support of a block-diagonal matrix: a relation that contains the
support of each block, on the corresponding indices, contains the support of
the whole. -/
theorem Supp.append {R₁ : Fin n₁ → Fin m₁ → Prop} {R₂ : Fin n₂ → Fin m₂ → Prop}
    {S : Fin (n₁ + n₂) → Fin (m₁ + m₂) → Prop} (hu : Supp R₁ u) (hv : Supp R₂ v)
    (hl : ∀ i j, R₁ i j → S (Fin.castAdd n₂ i) (Fin.castAdd m₂ j))
    (hr : ∀ i j, R₂ i j → S (Fin.natAdd n₁ i) (Fin.natAdd m₁ j)) :
    Supp S (blockDiag u v) := by
  intro i j hpos
  induction i using Fin.addCases with
  | left i₁ =>
    induction j using Fin.addCases with
    | left j₁ => exact hl _ _ (hu _ _ (by simpa using hpos))
    | right j₂ => simp at hpos
  | right i₂ =>
    induction j using Fin.addCases with
    | left j₁ => simp at hpos
    | right j₂ => exact hr _ _ (hv _ _ (by simpa using hpos))

end Append

section Stack

variable {κ : Type*} [Fintype κ] {n₁ n₂ : ℕ} {p : Fin n₁ → ℝ} {p' : Fin n₂ → ℝ}
  {q q' : κ → ℝ} {u : Fin n₁ → κ → ℝ} {v : Fin n₂ → κ → ℝ}

/-- Two couplings onto the same index type, one above the other: the stacked
matrix couples the appended left weights with the sum of the right weights. -/
theorem IsCoupling.stack (hu : IsCoupling p q u) (hv : IsCoupling p' q' v) :
    IsCoupling (Fin.append p p') (fun j => q j + q' j) (Fin.append u v) where
  nonneg i j := by
    induction i using Fin.addCases with
    | left i₁ => simpa using hu.nonneg i₁ j
    | right i₂ => simpa using hv.nonneg i₂ j
  row i := by
    induction i using Fin.addCases with
    | left i₁ => simpa using hu.row i₁
    | right i₂ => simpa using hv.row i₂
  col j := by rw [Fin.sum_univ_add]; simp [hu.col, hv.col]

end Stack

/-! ### Product over a dependent sum -/

section Sigma

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {α : ι → Type*} {β : κ → Type*}
  [∀ i, Fintype (α i)] [∀ j, Fintype (β j)]
  {p : ι → ℝ} {q : κ → ℝ} {u : ι → κ → ℝ}
  {b : ∀ i, α i → ℝ} {c : ι → ∀ j, β j → ℝ} {v : ∀ i j, α i → β j → ℝ}

/-- The product of a coupling `u` of `p` and `q` with a family of couplings
`v i j`, one for every positive cell of `u`, of the weights `b i` and `c i j`:
`W (i,k) (j,l) = u i j · v i j k l` couples the weights `p i · b i k` with
the `u`-weighted sums `∑ i, u i j · c i j l`. -/
theorem IsCoupling.sigma (hu : IsCoupling p q u)
    (hv : ∀ i j, 0 < u i j → IsCoupling (b i) (c i j) (v i j)) :
    IsCoupling (fun x : Σ i, α i => p x.1 * b x.1 x.2)
      (fun y : Σ j, β j => ∑ i, u i y.1 * c i y.1 y.2)
      (fun x y => u x.1 y.1 * v x.1 y.1 x.2 y.2) where
  nonneg x y := by
    rcases (hu.nonneg x.1 y.1).lt_or_eq with h | h
    · exact mul_nonneg h.le ((hv _ _ h).nonneg _ _)
    · rw [← h, zero_mul]
  row x := by
    obtain ⟨i, k⟩ := x
    rw [Fintype.sum_sigma]
    have hj : ∀ j, ∑ l, u i j * v i j k l = u i j * b i k := by
      intro j
      rcases (hu.nonneg i j).lt_or_eq with h | h
      · rw [← Finset.mul_sum, (hv i j h).row]
      · simp [← h]
    rw [Finset.sum_congr rfl fun j _ => hj j, ← Finset.sum_mul, hu.row]
  col y := by
    obtain ⟨j, l⟩ := y
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    show ∑ k, u i j * v i j k l = u i j * c i j l
    rcases (hu.nonneg i j).lt_or_eq with h | h
    · rw [← Finset.mul_sum, (hv i j h).col]
    · simp [← h]

/-- A positive weight of the product coupling comes from a positive cell of
`u` and a positive cell of the corresponding `v i j`. -/
theorem IsCoupling.sigma_pos (hu : IsCoupling p q u)
    (hv : ∀ i j, 0 < u i j → IsCoupling (b i) (c i j) (v i j))
    {x : Σ i, α i} {y : Σ j, β j} (hpos : 0 < u x.1 y.1 * v x.1 y.1 x.2 y.2) :
    0 < u x.1 y.1 ∧ 0 < v x.1 y.1 x.2 y.2 := by
  have hu0 : 0 < u x.1 y.1 := by
    rcases (hu.nonneg x.1 y.1).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
  exact ⟨hu0, (pos_and_pos_of_mul_pos hu0.le ((hv _ _ hu0).nonneg _ _) hpos).2⟩

end Sigma

/-! ## Push-forward

The push-forward of a weight vector along a map of indices, with the sums
over its fibers, and the probability that a weight vector gives to a
predicate. -/

section Pushfwd

variable {ι κ μ : Type*} [Fintype ι] [DecidableEq κ]

/-- The push-forward of the weights `w` along `f`: the weight of `j` is the
total weight of the indices that `f` sends to `j`. -/
noncomputable def pushfwd (f : ι → κ) (w : ι → ℝ) (j : κ) : ℝ :=
  ∑ i, if f i = j then w i else 0

/-- The push-forward of nonnegative weights is nonnegative. -/
theorem pushfwd_nonneg {f : ι → κ} {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (j : κ) :
    0 ≤ pushfwd f w j :=
  Finset.sum_nonneg fun i _ => ite_nonneg (hw i) le_rfl

/-- A nonnegative weight is at most the push-forward weight of its image. -/
theorem le_pushfwd {f : ι → κ} {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (i : ι) :
    w i ≤ pushfwd f w (f i) := by
  have h := Finset.single_le_sum (f := fun k => if f k = f i then w k else 0)
    (fun k _ => ite_nonneg (hw k) le_rfl) (Finset.mem_univ i)
  simpa [pushfwd] using h

/-- A positive push-forward weight comes from a positive weight in the fiber. -/
theorem pushfwd_pos {f : ι → κ} {w : ι → ℝ} {j : κ} (h : 0 < pushfwd f w j) :
    ∃ i, f i = j ∧ 0 < w i := by
  obtain ⟨i, hi⟩ := exists_pos_of_sum_pos (f := fun i => if f i = j then w i else 0) h
  exact ⟨i, pos_of_ite_pos hi⟩

/-- The push-forward preserves the total weight. -/
theorem sum_pushfwd [Fintype κ] (f : ι → κ) (w : ι → ℝ) : ∑ j, pushfwd f w j = ∑ i, w i := by
  unfold pushfwd
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- Integration against a push-forward: `∑ j, (f_* w) j · F j = ∑ i, w i · F (f i)`. -/
theorem sum_pushfwd_mul [Fintype κ] (f : ι → κ) (w : ι → ℝ) (F : κ → ℝ) :
    ∑ j, pushfwd f w j * F j = ∑ i, w i * F (f i) := by
  unfold pushfwd
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by simp [ite_mul]

/-- The push-forward weight of a set of indices is the weight of its preimage. -/
theorem sum_ite_pushfwd [Fintype κ] (f : ι → κ) (w : ι → ℝ) (P : κ → Prop) [DecidablePred P] :
    (∑ j, if P j then pushfwd f w j else 0) = ∑ i, if P (f i) then w i else 0 := by
  have h := sum_pushfwd_mul f w (fun j => if P j then 1 else 0)
  simpa [mul_ite] using h

/-- Pushing forward along `f` and then along `g` is pushing forward along
their composition. -/
theorem pushfwd_comp [Fintype κ] [Fintype μ] [DecidableEq μ] (f : ι → κ) (g : κ → μ) (w : ι → ℝ) :
    pushfwd g (pushfwd f w) = pushfwd (fun i => g (f i)) w :=
  funext fun k => sum_ite_pushfwd f w (fun j => g j = k)

/-- The push-forward commutes with scaling. -/
theorem pushfwd_mul_left (f : ι → κ) (a : ℝ) (w : ι → ℝ) :
    pushfwd f (fun i => a * w i) = fun j => a * pushfwd f w j := by
  funext j
  unfold pushfwd
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

/-- The push-forward commutes with sums. -/
theorem pushfwd_add (f : ι → κ) (w w' : ι → ℝ) :
    pushfwd f (fun i => w i + w' i) = fun j => pushfwd f w j + pushfwd f w' j := by
  funext j
  unfold pushfwd
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

/-- The push-forward commutes with convex combinations. -/
theorem pushfwd_mix (f : ι → κ) (t : ℝ) (w w' : ι → ℝ) :
    pushfwd f (fun i => t * w i + (1 - t) * w' i)
      = fun j => t * pushfwd f w j + (1 - t) * pushfwd f w' j := by
  rw [pushfwd_add f (fun i => t * w i) (fun i => (1 - t) * w' i), pushfwd_mul_left,
    pushfwd_mul_left]

/-- The push-forward along an injective map keeps each weight. -/
theorem pushfwd_apply_of_injective {f : ι → κ} (hf : Function.Injective f) (w : ι → ℝ) (i : ι) :
    pushfwd f w (f i) = w i := by
  unfold pushfwd
  rw [Finset.sum_eq_single i (fun k _ hk => if_neg fun h => hk (hf h))
    (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]

/-- The push-forward along the identity is the identity. -/
theorem pushfwd_id {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ) :
    pushfwd (fun i => i) w = w :=
  funext fun i => pushfwd_apply_of_injective (f := fun i => i) (fun _ _ h => h) w i

/-- The restriction of a weight vector `f` along an injective map `e` that
reaches every index of nonzero weight pushes forward along `e` to `f`. -/
theorem pushfwd_restrict {γ : Type*} [Fintype γ] {e : γ → κ} (he : Function.Injective e)
    {f : κ → ℝ} (hr : ∀ j, f j ≠ 0 → j ∈ Set.range e) : pushfwd e (fun c => f (e c)) = f := by
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨c, rfl⟩ := hj
    exact pushfwd_apply_of_injective he _ c
  · rw [not_not.1 (mt (hr j) hj)]
    exact Finset.sum_eq_zero fun c _ => if_neg fun h => hj ⟨c, h⟩

/-- The push-forward weight of `j` is the total weight of the fiber of `j`. -/
theorem pushfwd_eq_sum_filter (f : ι → κ) (w : ι → ℝ) (j : κ) :
    pushfwd f w j = ∑ i ∈ Finset.univ.filter (fun i => f i = j), w i :=
  (Finset.sum_filter _ _).symm

/-- The push-forward of appended weights along appended maps is the sum of
the two push-forwards. -/
theorem pushfwd_append {n m : ℕ} (f : Fin n → κ) (g : Fin m → κ) (w : Fin n → ℝ)
    (w' : Fin m → ℝ) (j : κ) :
    pushfwd (Fin.append f g) (Fin.append w w') j = pushfwd f w j + pushfwd g w' j := by
  unfold pushfwd
  rw [Fin.sum_univ_add]
  simp

/-- The push-forward along the inclusion of the left part of an appended index
set keeps the weights and puts zero on the right part. -/
theorem pushfwd_castAdd {n : ℕ} (m : ℕ) (w : Fin n → ℝ) :
    pushfwd (Fin.castAdd m) w = Fin.append w (fun _ => 0) := by
  funext k
  induction k using Fin.addCases with
  | left j =>
    rw [Fin.append_left]
    exact pushfwd_apply_of_injective (Fin.castAdd_injective n m) w j
  | right j =>
    rw [Fin.append_right]
    exact Finset.sum_eq_zero fun i _ => if_neg (by simp [Fin.ext_iff]; omega)

/-- The push-forward along the inclusion of the right part of an appended index
set keeps the weights and puts zero on the left part. -/
theorem pushfwd_natAdd (n : ℕ) {m : ℕ} (w : Fin m → ℝ) :
    pushfwd (Fin.natAdd n) w = Fin.append (fun _ => 0) w := by
  funext k
  induction k using Fin.addCases with
  | left j =>
    rw [Fin.append_left]
    exact Finset.sum_eq_zero fun i _ => if_neg (by simp [Fin.ext_iff]; omega)
  | right j =>
    rw [Fin.append_right]
    exact pushfwd_apply_of_injective (Fin.natAdd_injective m n) w j

/-- Integration against a push-forward, over any finite set that contains the
image of `f`; the target type need not be finite. -/
theorem sum_finset_pushfwd_mul (f : ι → κ) (w : ι → ℝ) (F : κ → ℝ) {T : Finset κ}
    (hT : ∀ i, f i ∈ T) : ∑ j ∈ T, pushfwd f w j * F j = ∑ i, w i * F (f i) := by
  unfold pushfwd
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by simp [ite_mul, hT i]

/-- Two weighted families with the same push-forward integrate every function
alike. -/
theorem sum_mul_eq_of_pushfwd_eq {ι' : Type*} [Fintype ι'] {f : ι → κ} {g : ι' → κ}
    {a : ι → ℝ} {b : ι' → ℝ} (h : pushfwd f a = pushfwd g b) (F : κ → ℝ) :
    ∑ i, a i * F (f i) = ∑ j, b j * F (g j) := by
  rw [← sum_finset_pushfwd_mul f a F (T := Finset.univ.image f ∪ Finset.univ.image g)
      (by simp),
    ← sum_finset_pushfwd_mul g b F (T := Finset.univ.image f ∪ Finset.univ.image g)
      (by simp), h]

/-- The coupling of a weight vector with its push-forward along `f`: all the
weight of `i` goes to `f i`. -/
theorem isCoupling_pushfwd [Fintype κ] (f : ι → κ) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) :
    IsCoupling w (pushfwd f w) (fun i j => if f i = j then w i else 0) where
  nonneg i _ := ite_nonneg (hw i) le_rfl
  row i := by simp
  col _ := rfl

omit [Fintype ι] in
/-- The coupling of a weight vector with its push-forward along `f` is
supported on the graph of `f`. -/
theorem supp_pushfwd (f : ι → κ) (w : ι → ℝ) :
    Supp (fun i j => f i = j) (fun i j => if f i = j then w i else 0) :=
  fun _ _ hpos => (pos_of_ite_pos hpos).1

/-- A weight vector on cells that are sent to pairs by `e` couples its two
marginals: the push-forward along `e` is a coupling of the push-forwards along
the two components of `e`. -/
theorem isCoupling_pushfwd_prod [Fintype κ] [DecidableEq ι] {γ : Type*} [Fintype γ] (e : γ → ι × κ)
    {x : γ → ℝ} (hx : ∀ c, 0 ≤ x c) :
    IsCoupling (pushfwd (fun c => (e c).1) x) (pushfwd (fun c => (e c).2) x)
      (fun i j => pushfwd e x (i, j)) where
  nonneg _ _ := pushfwd_nonneg hx _
  row i := by
    unfold pushfwd
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : (e c).1 = i <;> simp [Prod.ext_iff, h]
  col j := by
    unfold pushfwd
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : (e c).2 = j <;> simp [Prod.ext_iff, h]

/-- Restriction of a coupling to the cells of its support: if the injective
map `e` reaches every pair of nonzero weight, the weights of the cells have the
weights of the coupling as marginals. -/
theorem IsCoupling.restrict [Fintype κ] [DecidableEq ι] {γ : Type*} [Fintype γ] {p : ι → ℝ}
    {q : κ → ℝ} {w : ι → κ → ℝ} (h : IsCoupling p q w) {e : γ → ι × κ}
    (he : Function.Injective e)
    (hr : ∀ i j, w i j ≠ 0 → (i, j) ∈ Set.range e) :
    pushfwd (fun c => (e c).1) (fun c => w (e c).1 (e c).2) = p ∧
    pushfwd (fun c => (e c).2) (fun c => w (e c).1 (e c).2) = q := by
  have hzero : ∀ x : ι × κ, x ∉ Set.range e → w x.1 x.2 = 0 := fun x hx => by
    by_contra hne; exact hx (hr x.1 x.2 hne)
  constructor
  · funext i
    unfold pushfwd
    rw [Fintype.sum_of_injective e he _ (fun x : ι × κ => if x.1 = i then w x.1 x.2 else 0)
      (fun x hx => by simp [hzero x hx]) (fun _ => rfl), Fintype.sum_prod_type, ← h.row i]
    simp
  · funext j
    unfold pushfwd
    rw [Fintype.sum_of_injective e he _ (fun x : ι × κ => if x.2 = j then w x.1 x.2 else 0)
      (fun x hx => by simp [hzero x hx]) (fun _ => rfl), Fintype.sum_prod_type, ← h.col j,
      Finset.sum_comm]
    simp

end Pushfwd

section Cells

variable {ι κ γ : Type*} [Fintype ι] [Fintype κ] [Fintype γ]

/-- A sum over cells that an injective map sends to pairs is the sum over all
pairs, for a function that vanishes outside the cells. -/
theorem sum_cells {e : γ → ι × κ} (he : Function.Injective e) (G : ι → κ → ℝ)
    (hr : ∀ i j, G i j ≠ 0 → (i, j) ∈ Set.range e) :
    ∑ c, G (e c).1 (e c).2 = ∑ i, ∑ j, G i j :=
  (Fintype.sum_of_injective e he _ (fun x : ι × κ => G x.1 x.2)
    (fun x hx => of_not_not fun hne => hx (hr x.1 x.2 hne)) fun _ => rfl).trans
    (Fintype.sum_prod_type fun x : ι × κ => G x.1 x.2)

/-- A family of weights on pairs, all of them zero outside the cells that the
injective map `e` enumerates, couples its totals with its restriction to the
cells. -/
theorem isCoupling_restrict_cells {μ : Type*} [Fintype μ] {T : μ → ι → κ → ℝ}
    (hT : ∀ i a b, 0 ≤ T i a b) {e : γ → ι × κ} (he : Function.Injective e)
    (hr : ∀ i a b, 0 < T i a b → (a, b) ∈ Set.range e) :
    IsCoupling (fun i => ∑ a, ∑ b, T i a b) (fun c => ∑ i, T i (e c).1 (e c).2)
      (fun i c => T i (e c).1 (e c).2) where
  nonneg _ _ := hT _ _ _
  row i := sum_cells he (T i) fun a b hne => hr i a b ((hT i a b).lt_of_ne' hne)
  col _ := rfl

variable [DecidableEq ι] [DecidableEq κ]

/-- Restriction of a coupling supported on `P` to cells that enumerate the
pairs of `P`: the weights of the cells have the weights of the coupling as
marginals (`IsCoupling.restrict`). -/
theorem IsCoupling.restrict_of_supp {p : ι → ℝ} {q : κ → ℝ} {w : ι → κ → ℝ}
    {P : ι → κ → Prop} (h : IsCoupling p q w) (hs : Supp P w) {e : γ → ι × κ}
    (he : Function.Injective e) (hr : ∀ i j, P i j → (i, j) ∈ Set.range e) :
    pushfwd (fun c => (e c).1) (fun c => w (e c).1 (e c).2) = p ∧
    pushfwd (fun c => (e c).2) (fun c => w (e c).1 (e c).2) = q :=
  h.restrict he fun i j hne => hr i j (hs i j ((h.nonneg i j).lt_of_ne' hne))

end Cells

section MassOf

variable {ι κ α : Type*} [Fintype ι]

/-- The weight that the family of points `val`, with weights `w`, gives to the
points that satisfy `P`. -/
noncomputable def massOf (P : α → Prop) [DecidablePred P] (val : ι → α) (w : ι → ℝ) : ℝ :=
  ∑ i, if P (val i) then w i else 0

variable {P : α → Prop} [DecidablePred P] {val : ι → α} {w : ι → ℝ}

/-- The weight of a predicate under nonnegative weights is nonnegative. -/
theorem massOf_nonneg (hw : ∀ i, 0 ≤ w i) : 0 ≤ massOf P val w :=
  Finset.sum_nonneg fun i _ => ite_nonneg (hw i) le_rfl

/-- A point that satisfies the predicate weighs at most the predicate. -/
theorem le_massOf (hw : ∀ i, 0 ≤ w i) {i : ι} (hi : P (val i)) : w i ≤ massOf P val w := by
  have h := Finset.single_le_sum (f := fun k => if P (val k) then w k else 0)
    (fun k _ => ite_nonneg (hw k) le_rfl) (Finset.mem_univ i)
  simpa [massOf, hi] using h

/-- A predicate of positive weight holds at a point of positive weight. -/
theorem massOf_pos (h : 0 < massOf P val w) : ∃ i, P (val i) ∧ 0 < w i := by
  obtain ⟨i, hi⟩ := exists_pos_of_sum_pos (f := fun i => if P (val i) then w i else 0) h
  exact ⟨i, pos_of_ite_pos hi⟩

/-- The weight of a predicate commutes with scaling. -/
theorem massOf_mul_left (P : α → Prop) [DecidablePred P] (val : ι → α) (a : ℝ) (w : ι → ℝ) :
    massOf P val (fun i => a * w i) = a * massOf P val w := by
  unfold massOf
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

/-- The weight of a predicate under a push-forward is its weight on the
composed family. -/
theorem massOf_pushfwd [Fintype κ] [DecidableEq κ] (P : α → Prop) [DecidablePred P]
    (f : ι → κ) (val : κ → α) (w : ι → ℝ) :
    massOf P val (pushfwd f w) = massOf P (fun i => val (f i)) w :=
  sum_ite_pushfwd f w (fun j => P (val j))

/-- The weight of a predicate on appended families is the sum of its weights
on the two parts. -/
theorem massOf_append (P : α → Prop) [DecidablePred P] {n m : ℕ} (v₁ : Fin n → α)
    (v₂ : Fin m → α) (w₁ : Fin n → ℝ) (w₂ : Fin m → ℝ) :
    massOf P (Fin.append v₁ v₂) (Fin.append w₁ w₂) = massOf P v₁ w₁ + massOf P v₂ w₂ := by
  unfold massOf
  rw [Fin.sum_univ_add]
  simp

/-- The weight of a predicate depends only on which points satisfy it. -/
theorem massOf_congr {β : Type*} {P : α → Prop} {Q : β → Prop} [DecidablePred P]
    [DecidablePred Q] {val : ι → α} {val' : ι → β} {w : ι → ℝ}
    (h : ∀ i, P (val i) ↔ Q (val' i)) : massOf P val w = massOf Q val' w :=
  Finset.sum_congr rfl fun i _ => if_congr (h i) rfl rfl

/-- The weight of a predicate on a one-point family. -/
theorem massOf_fin_one (P : α → Prop) [DecidablePred P] (val : Fin 1 → α) (w : Fin 1 → ℝ) :
    massOf P val w = if P (val 0) then w 0 else 0 :=
  Fin.sum_univ_one _

/-- The weight of a predicate can be computed over an injective enumeration
of the indices that reaches every index of nonzero weight. -/
theorem massOf_comp_of_injective {ι' : Type*} [Fintype ι'] (P : α → Prop) [DecidablePred P]
    (val : ι → α) (w : ι → ℝ) {e : ι' → ι} (he : Function.Injective e)
    (hr : ∀ i, w i ≠ 0 → i ∈ Set.range e) :
    massOf P (fun k => val (e k)) (fun k => w (e k)) = massOf P val w :=
  Fintype.sum_of_injective e he _ (fun i => if P (val i) then w i else 0)
    (fun i hi => by simp [not_not.1 fun h => hi (hr i h)]) fun _ => rfl

end MassOf

/-! ## The lifting of a relation

Reflexivity, symmetry, monotonicity and composition of the lifting, for
concrete distributions (`Lift`) and for symbolic ones (`SymLift`,
`SymLiftAll`), and the liftings that the constructions above yield. -/

section LiftLemmas

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
  {R : ι → κ → Prop} {p : ι → ℝ} {q : κ → ℝ} {r : μ → ℝ}

/-- The lifting is monotone in the relation. -/
theorem Lift.mono {S : ι → κ → Prop} (h : Lift R p q) (hRS : ∀ i j, R i j → S i j) :
    Lift S p q :=
  let ⟨w, hw, hs⟩ := h; ⟨w, hw, hs.mono hRS⟩

/-- The lifting of a reflexive relation relates every nonnegative weight
vector to itself. -/
theorem Lift.refl [DecidableEq ι] {R : ι → ι → Prop} {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hR : ∀ i, R i i) : Lift R p p :=
  ⟨_, .diag hp, (Supp.diag p).mono fun i _ hij => hij ▸ hR i⟩

/-- The lifting of the converse relation is the converse of the lifting. -/
theorem Lift.symm (h : Lift R p q) : Lift (fun j i => R i j) q p :=
  let ⟨_, hw, hs⟩ := h; ⟨_, hw.symm, hs.symm⟩

/-- Liftings compose: the lifting of `R` followed by the lifting of `S` is
contained in the lifting of their composition. -/
theorem Lift.comp {S : κ → μ → Prop} (h₁ : Lift R p q) (h₂ : Lift S q r) :
    Lift (Relation.Comp R S) p r :=
  let ⟨_, hw₁, hs₁⟩ := h₁
  let ⟨_, hw₂, hs₂⟩ := h₂
  ⟨_, hw₁.glue hw₂, hs₁.glue hs₂ hw₁ hw₂⟩

/-- Transitivity of the lifting, along any relation `T` that contains the
composition of `R` and `S`. -/
theorem Lift.trans {S : κ → μ → Prop} {T : ι → μ → Prop} (h₁ : Lift R p q) (h₂ : Lift S q r)
    (hT : ∀ i j k, R i j → S j k → T i k) : Lift T p r :=
  (h₁.comp h₂).mono fun i k ⟨j, hij, hjk⟩ => hT i j k hij hjk

/-- The weights related by a lifting on the left are nonnegative. -/
theorem Lift.left_nonneg (h : Lift R p q) (i : ι) : 0 ≤ p i :=
  let ⟨_, hw, _⟩ := h; hw.left_nonneg i

/-- The weights related by a lifting on the right are nonnegative. -/
theorem Lift.right_nonneg (h : Lift R p q) (j : κ) : 0 ≤ q j :=
  let ⟨_, hw, _⟩ := h; hw.right_nonneg j

/-- The lifting is preserved by scaling both sides by a nonnegative factor. -/
theorem Lift.smul (h : Lift R p q) {a : ℝ} (ha : 0 ≤ a) :
    Lift R (fun i => a * p i) (fun j => a * q j) :=
  let ⟨_, hw, hs⟩ := h
  ⟨_, hw.smul ha, fun i j hpos =>
    hs i j (pos_and_pos_of_mul_pos ha (hw.nonneg i j) hpos).2⟩

/-- Scaling a lifting by a nonnegative factor `a`, when the relation is only
required for a positive `a`: if `a = 0`, the scaled coupling has no positive
cell. -/
theorem Lift.smul_of_pos {a : ℝ} (h : Lift (fun i j => 0 < a → R i j) p q) (ha : 0 ≤ a) :
    Lift R (fun i => a * p i) (fun j => a * q j) :=
  let ⟨_, hw, hs⟩ := h
  ⟨_, hw.smul ha, fun i j hpos =>
    let ⟨h0, hpos'⟩ := pos_and_pos_of_mul_pos ha (hw.nonneg i j) hpos
    hs i j hpos' h0⟩

/-- The lifting is preserved by sums. -/
theorem Lift.add {p' : ι → ℝ} {q' : κ → ℝ} (h : Lift R p q) (h' : Lift R p' q') :
    Lift R (fun i => p i + p' i) (fun j => q j + q' j) := by
  obtain ⟨w, hw, hs⟩ := h
  obtain ⟨w', hw', hs'⟩ := h'
  refine ⟨_, hw.add hw', fun i j hpos => ?_⟩
  by_cases h0 : 0 < w i j
  · exact hs i j h0
  · rw [eq_zero_of_nonneg_of_not_pos (hw.nonneg i j) h0, zero_add] at hpos
    exact hs' i j hpos

/-- The lifting of two one-point distributions with related points. -/
theorem Lift.point {R : Fin 1 → Fin 1 → Prop} {p q : Fin 1 → ℝ} (hp : p 0 = 1) (hq : q 0 = 1)
    (hR : R 0 0) : Lift R p q :=
  ⟨_, .point hp hq, fun i j _ => by rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; exact hR⟩

/-- A nonnegative weight vector is related to its push-forward along `f` by
the lifting of any relation that contains the graph of `f`. -/
theorem Lift.pushfwd [DecidableEq κ] (f : ι → κ) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hR : ∀ i, R i (f i)) : Lift R w (pushfwd f w) :=
  ⟨_, isCoupling_pushfwd f hw, (supp_pushfwd f w).mono fun i _ hij => hij ▸ hR i⟩

/-- Liftings of appended weight vectors: the two liftings sit side by side,
and the relation `S` on the appended indices contains `R₁` on the left parts
and `R₂` on the right parts. -/
theorem Lift.append {n₁ n₂ m₁ m₂ : ℕ} {p : Fin n₁ → ℝ} {p' : Fin n₂ → ℝ} {q : Fin m₁ → ℝ}
    {q' : Fin m₂ → ℝ} {R₁ : Fin n₁ → Fin m₁ → Prop} {R₂ : Fin n₂ → Fin m₂ → Prop}
    {S : Fin (n₁ + n₂) → Fin (m₁ + m₂) → Prop} (h₁ : Lift R₁ p q) (h₂ : Lift R₂ p' q')
    (hl : ∀ i j, R₁ i j → S (Fin.castAdd n₂ i) (Fin.castAdd m₂ j))
    (hr : ∀ i j, R₂ i j → S (Fin.natAdd n₁ i) (Fin.natAdd m₁ j)) :
    Lift S (Fin.append p p') (Fin.append q q') :=
  let ⟨_, hu, su⟩ := h₁
  let ⟨_, hv, sv⟩ := h₂
  ⟨_, hu.append hv, su.append sv hl hr⟩

/-- A lifting between `p` and `q` is a lifting between any weights equal to
them. -/
theorem Lift.congr {p' : ι → ℝ} {q' : κ → ℝ} (h : Lift R p q) (hp : ∀ i, p i = p' i)
    (hq : ∀ j, q j = q' j) : Lift R p' q' :=
  let ⟨w, hw, hs⟩ := h; ⟨w, hw.congr hp hq, hs⟩

/-- Transport of a lifting along bijections of the two index types. -/
theorem Lift.reindex {ι' κ' : Type*} [Fintype ι'] [Fintype κ'] (h : Lift R p q)
    (e₁ : ι' ≃ ι) (e₂ : κ' ≃ κ) :
    Lift (fun i j => R (e₁ i) (e₂ j)) (fun i => p (e₁ i)) (fun j => q (e₂ j)) :=
  let ⟨_, hw, hs⟩ := h; ⟨_, hw.reindex e₁ e₂, fun _ _ => hs _ _⟩

/-- An index of positive weight on the right of a lifting is related to an
index of positive weight on the left. -/
theorem Lift.exists_of_right_pos (h : Lift R p q) {j : κ} (hj : 0 < q j) :
    ∃ i, 0 < p i ∧ R i j :=
  let ⟨_, hw, hs⟩ := h
  let ⟨i, hi⟩ := hw.exists_pos_of_right hj
  ⟨i, hw.left_pos hi, hs i j hi⟩

/-- A nonnegative weight vector is related to its push-forward along `f` by
the lifting of any relation that contains the graph of `f` on the indices of
positive weight. -/
theorem Lift.pushfwd_of_pos [DecidableEq κ] (f : ι → κ) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hR : ∀ i, 0 < w i → R i (f i)) : Lift R w (GradualProb.pushfwd f w) :=
  ⟨_, isCoupling_pushfwd f hw, fun i _ hpos =>
    let ⟨hij, hi⟩ := pos_of_ite_pos hpos
    hij ▸ hR i hi⟩

/-- The restriction of a nonnegative weight vector `f` along an injective map
`e` that reaches every index of nonzero weight is related to `f` by the lifting
of any relation that contains the graph of `e`. -/
theorem Lift.restrict [DecidableEq κ] {e : ι → κ} (he : Function.Injective e) {f : κ → ℝ}
    (hf : ∀ j, 0 ≤ f j) (hr : ∀ j, f j ≠ 0 → j ∈ Set.range e) (hR : ∀ c, R c (e c)) :
    Lift R (fun c => f (e c)) f := by
  have h := Lift.pushfwd e (w := fun c => f (e c)) (fun c => hf (e c)) hR
  rwa [pushfwd_restrict he hr] at h

/-- Nonnegative weights on cells that `e` sends to pairs related by `R`: the
two marginals are related by the lifting of `R` (`isCoupling_pushfwd_prod`). -/
theorem Lift.pushfwd_prod [DecidableEq ι] [DecidableEq κ] {γ : Type*} [Fintype γ]
    (e : γ → ι × κ) {x : γ → ℝ} (hx : ∀ c, 0 ≤ x c) (hR : ∀ c, R (e c).1 (e c).2) :
    Lift R (GradualProb.pushfwd (fun c => (e c).1) x)
      (GradualProb.pushfwd (fun c => (e c).2) x) :=
  ⟨_, isCoupling_pushfwd_prod e hx, fun i j hpos => by
    obtain ⟨c, hc, -⟩ := pushfwd_pos hpos
    have h := hR c
    rwa [hc] at h⟩

/-- Liftings onto the same index type, one above the other: the appended left
weights are related to the sum of the right weights by the lifting of any
relation `S` that contains `R₁` on the first block of rows and `R₂` on the
second. -/
theorem Lift.stack {n₁ n₂ : ℕ} {p : Fin n₁ → ℝ} {p' : Fin n₂ → ℝ} {q q' : κ → ℝ}
    {R₁ : Fin n₁ → κ → Prop} {R₂ : Fin n₂ → κ → Prop} {S : Fin (n₁ + n₂) → κ → Prop}
    (h₁ : Lift R₁ p q) (h₂ : Lift R₂ p' q') (hl : ∀ i j, R₁ i j → S (Fin.castAdd n₂ i) j)
    (hr : ∀ i j, R₂ i j → S (Fin.natAdd n₁ i) j) :
    Lift S (Fin.append p p') (fun j => q j + q' j) := by
  obtain ⟨u, hu, su⟩ := h₁
  obtain ⟨v, hv, sv⟩ := h₂
  refine ⟨_, hu.stack hv, fun i j hpos => ?_⟩
  induction i using Fin.addCases with
  | left i₁ => exact hl _ _ (su _ _ (by simpa using hpos))
  | right i₂ => exact hr _ _ (sv _ _ (by simpa using hpos))

/-- The tensor composition `IsCoupling.tensor` at the level of the lifting: a
coupling `P` of `p₁` and `p₂` is transported along liftings of `R₁`, from `p₁`
to `q₁`, and of `R₂`, from `p₂` to `q₂`, to a coupling `Q` of `q₁` and `q₂`.
As weight vectors on pairs, `P` and `Q` are related by the lifting of the
componentwise relation. -/
theorem Lift.tensor {ι₁ ι₂ κ₁ κ₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype κ₁] [Fintype κ₂]
    {p₁ : ι₁ → ℝ} {p₂ : ι₂ → ℝ} {q₁ : κ₁ → ℝ} {q₂ : κ₂ → ℝ} {P : ι₁ → ι₂ → ℝ}
    {R₁ : ι₁ → κ₁ → Prop} {R₂ : ι₂ → κ₂ → Prop}
    (hP : IsCoupling p₁ p₂ P) (h₁ : Lift R₁ p₁ q₁) (h₂ : Lift R₂ p₂ q₂) :
    ∃ Q, IsCoupling q₁ q₂ Q ∧
      Lift (fun (x : ι₁ × ι₂) (y : κ₁ × κ₂) => R₁ x.1 y.1 ∧ R₂ x.2 y.2)
        (fun x => P x.1 x.2) (fun y => Q y.1 y.2) := by
  obtain ⟨u, hu, hus⟩ := h₁
  obtain ⟨v, hv, hvs⟩ := h₂
  obtain ⟨Q, W, hQ, hWnn, hWP, hWQ, hWpos⟩ := hP.tensor hu hv
  refine ⟨Q, hQ, fun x y => W x.1 x.2 y.1 y.2,
    ⟨fun _ _ => hWnn _ _ _ _, fun x => ?_, fun y => ?_⟩, fun x y hpos => ?_⟩
  · rw [Fintype.sum_prod_type]; exact hWP x.1 x.2
  · rw [Fintype.sum_prod_type]; exact hWQ y.1 y.2
  · obtain ⟨-, hu0, hv0⟩ := hWpos _ _ _ _ hpos
    exact ⟨hus _ _ hu0, hvs _ _ hv0⟩

variable {ψ₁ : (ι → ℝ) → Prop} {ψ₂ : (κ → ℝ) → Prop} {ψ₃ : (μ → ℝ) → Prop}

/-- The symbolic lifting is monotone in the relation. -/
theorem SymLift.mono {S : ι → κ → Prop} (h : SymLift R ψ₁ ψ₂) (hRS : ∀ i j, R i j → S i j) :
    SymLift S ψ₁ ψ₂ :=
  let ⟨p, q, hp, hq, hl⟩ := h; ⟨p, q, hp, hq, hl.mono hRS⟩

/-- The symbolic lifting of the converse relation is the converse of the
symbolic lifting. -/
theorem SymLift.symm (h : SymLift R ψ₁ ψ₂) : SymLift (fun j i => R i j) ψ₂ ψ₁ :=
  let ⟨p, q, hp, hq, hl⟩ := h; ⟨q, p, hq, hp, hl.symm⟩

/-- The symbolic lifting of a reflexive relation relates a satisfiable
constraint with nonnegative solutions to itself. -/
theorem SymLift.refl [DecidableEq ι] {R : ι → ι → Prop} {ψ : (ι → ℝ) → Prop} {p : ι → ℝ}
    (hp : ψ p) (hnn : ∀ i, 0 ≤ p i) (hR : ∀ i, R i i) : SymLift R ψ ψ :=
  ⟨p, p, hp, hp, .refl hnn hR⟩

/-- The universal symbolic lifting is monotone in the relation. -/
theorem SymLiftAll.mono {S : ι → κ → Prop} (h : SymLiftAll R ψ₁ ψ₂)
    (hRS : ∀ i j, R i j → S i j) : SymLiftAll S ψ₁ ψ₂ := fun p hp =>
  let ⟨q, hq, hl⟩ := h p hp; ⟨q, hq, hl.mono hRS⟩

/-- The universal symbolic lifting of a reflexive relation relates a
constraint with nonnegative solutions to itself. -/
theorem SymLiftAll.refl [DecidableEq ι] {R : ι → ι → Prop} {ψ : (ι → ℝ) → Prop}
    (hnn : ∀ p, ψ p → ∀ i, 0 ≤ p i) (hR : ∀ i, R i i) : SymLiftAll R ψ ψ :=
  fun p hp => ⟨p, hp, .refl (hnn p hp) hR⟩

/-- Transitivity of the universal symbolic lifting, along any relation `T`
that contains the composition of `R` and `S`. -/
theorem SymLiftAll.trans {S : κ → μ → Prop} {T : ι → μ → Prop} (h₁ : SymLiftAll R ψ₁ ψ₂)
    (h₂ : SymLiftAll S ψ₂ ψ₃) (hT : ∀ i j k, R i j → S j k → T i k) :
    SymLiftAll T ψ₁ ψ₃ := fun p hp =>
  let ⟨q, hq, hl₁⟩ := h₁ p hp
  let ⟨r, hr, hl₂⟩ := h₂ q hq
  ⟨r, hr, hl₁.trans hl₂ hT⟩

/-- On a satisfiable left constraint, the universal symbolic lifting gives the
symbolic lifting. -/
theorem SymLiftAll.symLift (h : SymLiftAll R ψ₁ ψ₂) (hsat : ∃ p, ψ₁ p) : SymLift R ψ₁ ψ₂ :=
  let ⟨p, hp⟩ := hsat
  let ⟨q, hq, hl⟩ := h p hp
  ⟨p, q, hp, hq, hl⟩

/-- A symbolic lifting composes on the right with a universal symbolic
lifting. -/
theorem SymLift.comp_right {S : κ → μ → Prop} {T : ι → μ → Prop} (h : SymLift R ψ₁ ψ₂)
    (h₂ : SymLiftAll S ψ₂ ψ₃) (hT : ∀ i j k, R i j → S j k → T i k) : SymLift T ψ₁ ψ₃ :=
  let ⟨p, q, hp, hq, hl⟩ := h
  let ⟨r, hr, hl₂⟩ := h₂ q hq
  ⟨p, r, hp, hr, hl.trans hl₂ hT⟩

/-- A symbolic lifting composes on the left with a universal symbolic
lifting of its left constraint. -/
theorem SymLift.comp_left {S : ι → μ → Prop} {T : μ → κ → Prop} (h : SymLift R ψ₁ ψ₂)
    (h₁ : SymLiftAll S ψ₁ ψ₃) (hT : ∀ i j k, S i k → R i j → T k j) : SymLift T ψ₃ ψ₂ :=
  let ⟨p, q, hp, hq, hl⟩ := h
  let ⟨r, hr, hl₁⟩ := h₁ p hp
  ⟨r, q, hr, hq, hl₁.symm.trans hl fun k i j hik hij => hT i j k hik hij⟩

end LiftLemmas

/-! ### Product over a `Fin`-indexed dependent concatenation -/

section SigmaFin

variable {m m' : ℕ} {n : Fin m → ℕ} {n' : Fin m' → ℕ}
  {p : Fin m → ℝ} {q : Fin m' → ℝ} {u : Fin m → Fin m' → ℝ}
  {b : ∀ i, Fin (n i) → ℝ} {c : Fin m → ∀ j, Fin (n' j) → ℝ}
  {v : ∀ i j, Fin (n i) → Fin (n' j) → ℝ}

/-- The product coupling `IsCoupling.sigma` on the `Fin`-indexed dependent
concatenations of the two families of blocks: the block of a cell `κ` is
`(finSigmaFinEquiv.symm κ).1` and its position in the block is
`(finSigmaFinEquiv.symm κ).2`. -/
theorem IsCoupling.sigmaFin (hu : IsCoupling p q u)
    (hv : ∀ i j, 0 < u i j → IsCoupling (b i) (c i j) (v i j)) :
    IsCoupling
      (fun κ : Fin (∑ i, n i) =>
        p (finSigmaFinEquiv.symm κ).1 * b _ (finSigmaFinEquiv.symm κ).2)
      (fun κ' : Fin (∑ j, n' j) =>
        ∑ i, u i (finSigmaFinEquiv.symm κ').1 * c i _ (finSigmaFinEquiv.symm κ').2)
      (fun κ κ' => u (finSigmaFinEquiv.symm κ).1 (finSigmaFinEquiv.symm κ').1 *
        v _ _ (finSigmaFinEquiv.symm κ).2 (finSigmaFinEquiv.symm κ').2) :=
  (hu.sigma hv).reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm

/-- The lifting that the product coupling yields: if `u` couples `p` and `q`
with support in `R`, and for every pair of blocks in `R` the weights `b i` and
`c i j` are related by the lifting of `S i j`, then the concatenated weights
are related by the lifting of any relation `T` that contains `S i j` on the
cells of every pair of blocks in `R`. -/
theorem Lift.sigmaFin {R : Fin m → Fin m' → Prop}
    {S : ∀ i j, Fin (n i) → Fin (n' j) → Prop}
    {T : Fin (∑ i, n i) → Fin (∑ j, n' j) → Prop}
    (hu : IsCoupling p q u) (hs : Supp R u)
    (hv : ∀ i j, R i j → Lift (S i j) (b i) (c i j))
    (hT : ∀ i j k l, R i j → S i j k l →
      T (finSigmaFinEquiv ⟨i, k⟩) (finSigmaFinEquiv ⟨j, l⟩)) :
    Lift T
      (fun κ : Fin (∑ i, n i) =>
        p (finSigmaFinEquiv.symm κ).1 * b _ (finSigmaFinEquiv.symm κ).2)
      (fun κ' : Fin (∑ j, n' j) =>
        ∑ i, u i (finSigmaFinEquiv.symm κ').1 * c i _ (finSigmaFinEquiv.symm κ').2) := by
  classical
  have hex : ∀ i j, ∃ v : Fin (n i) → Fin (n' j) → ℝ,
      0 < u i j → IsCoupling (b i) (c i j) v ∧ Supp (S i j) v := by
    intro i j
    by_cases h : 0 < u i j
    · obtain ⟨v, hv, hsv⟩ := hv i j (hs i j h)
      exact ⟨v, fun _ => ⟨hv, hsv⟩⟩
    · exact ⟨fun _ _ => 0, fun h' => absurd h' h⟩
  choose v hv using hex
  refine ⟨_, hu.sigmaFin (v := v) fun i j h => (hv i j h).1, fun κ κ' hpos => ?_⟩
  obtain ⟨hu0, hv0⟩ := hu.sigma_pos (v := v) (fun i j h => (hv i j h).1)
    (x := finSigmaFinEquiv.symm κ) (y := finSigmaFinEquiv.symm κ') hpos
  have := hT _ _ _ _ (hs _ _ hu0) ((hv _ _ hu0).2 _ _ hv0)
  simpa using this

end SigmaFin

/-! ## Coverage of appended and concatenated families

The coverage clauses that accompany a lifting ask every member of a family to
have a partner in the other family. These lemmas give the coverage of the
families that the type operators build. -/

section Coverage

variable {α β : Type*} {P : α → β → Prop}

/-- Coverage of appended families: if every member of each part has a partner
in the corresponding part of the other family, then every member of the
appended family has a partner in the other appended family. -/
theorem cov_append {n₁ n₂ m₁ m₂ : ℕ} {a₁ : Fin n₁ → α} {a₂ : Fin n₂ → α} {b₁ : Fin m₁ → β}
    {b₂ : Fin m₂ → β} (h₁ : ∀ i, ∃ j, P (a₁ i) (b₁ j)) (h₂ : ∀ i, ∃ j, P (a₂ i) (b₂ j))
    (i : Fin (n₁ + n₂)) : ∃ j, P (Fin.append a₁ a₂ i) (Fin.append b₁ b₂ j) := by
  induction i using Fin.addCases with
  | left i => obtain ⟨j, hj⟩ := h₁ i; exact ⟨Fin.castAdd _ j, by simpa using hj⟩
  | right i => obtain ⟨j, hj⟩ := h₂ i; exact ⟨Fin.natAdd _ j, by simpa using hj⟩

/-- Coverage of dependent concatenations: if every member of the block `i` has
a partner in the block `f i` of the other family, then every member of the
concatenated family has a partner in the other concatenated family. -/
theorem cov_sigmaFin {m m' : ℕ} {n : Fin m → ℕ} {n' : Fin m' → ℕ} {a : ∀ i, Fin (n i) → α}
    {b : ∀ j, Fin (n' j) → β} (f : Fin m → Fin m') (h : ∀ i k, ∃ l, P (a i k) (b (f i) l))
    (κ : Fin (∑ i, n i)) :
    ∃ κ' : Fin (∑ j, n' j),
      P (a _ (finSigmaFinEquiv.symm κ).2) (b _ (finSigmaFinEquiv.symm κ').2) := by
  obtain ⟨l, hl⟩ := h _ (finSigmaFinEquiv.symm κ).2
  exact ⟨finSigmaFinEquiv ⟨f _, l⟩, by rw [Equiv.symm_apply_apply]; exact hl⟩

end Coverage

end GradualProb


namespace GradualProb.CouplingLemma

open scoped BigOperators
open Classical

variable {α : Type*}

/-- Total probability that the distribution `(f, w)` puts on the `R`-class of
`x`. -/
noncomputable def classMass {n : ℕ} (R : α → α → Prop)
    (f : Fin n → α) (w : Fin n → ℝ) (x : α) : ℝ :=
  ∑ i, if R (f i) x then w i else 0

/-- The class probability `classMass` depends only on the `R`-class of the probe
point. -/
theorem classMass_congr {n : ℕ} {R : α → α → Prop}
    (hsymm : ∀ x y, R x y → R y x) (htrans : ∀ x y z, R x y → R y z → R x z)
    (f : Fin n → α) (w : Fin n → ℝ) {x y : α} (hxy : R x y) :
    classMass R f w x = classMass R f w y := by
  unfold classMass
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hiff : R (f i) x ↔ R (f i) y :=
    ⟨fun h => htrans _ _ _ h hxy, fun h => htrans _ _ _ h (hsymm _ _ hxy)⟩
  rw [propext hiff]

/-- A point lies in its own class, so its weight is `≤` the class probability. -/
theorem le_classMass {n : ℕ} {R : α → α → Prop}
    (f : Fin n → α) (hself : ∀ k, R (f k) (f k)) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (i : Fin n) :
    w i ≤ classMass R f w (f i) := by
  unfold classMass
  have hii : (if R (f i) (f i) then w i else 0) = w i := by simp [hself i]
  calc w i = if R (f i) (f i) then w i else 0 := hii.symm
    _ ≤ ∑ k, if R (f k) (f i) then w k else 0 := by
        refine Finset.single_le_sum (f := fun k => if R (f k) (f i) then w k else 0)
          (fun k _ => ?_) (Finset.mem_univ i)
        by_cases h : R (f k) (f i) <;> simp [h, hw k]

/-- The class probability `classMass` is nonnegative. -/
theorem classMass_nonneg {n : ℕ} {R : α → α → Prop}
    (f : Fin n → α) (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (x : α) :
    0 ≤ classMass R f w x := by
  unfold classMass
  refine Finset.sum_nonneg (fun k _ => ?_)
  by_cases hk : R (f k) x <;> simp [hk, hw k]

/-- Pull a constant out of a guarded sum. -/
private theorem sum_ite_const_mul {β : Type*} [Fintype β]
    (c : β → Prop) (g : β → ℝ) (K : ℝ) :
    (∑ j, if c j then K * g j else 0) = K * ∑ j, if c j then g j else 0 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : c j <;> simp [h]

/-- Coupling lemma, `(⟸)`: equal class probability yields the lifting of `R`. -/
theorem coupling_of_classMass {n m : ℕ} {R : α → α → Prop}
    (hsymm : ∀ x y, R x y → R y x) (htrans : ∀ x y z, R x y → R y z → R x z)
    (a : Fin n → α) (p : Fin n → ℝ) (b : Fin m → α) (q : Fin m → ℝ)
    (hrefla : ∀ i, R (a i) (a i)) (hreflb : ∀ j, R (b j) (b j))
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hmass : ∀ x, classMass R a p x = classMass R b q x) :
    Lift (fun i j => R (a i) (b j)) p q := by
  refine ⟨fun i j => if R (a i) (b j) then p i * q j / classMass R a p (a i) else 0,
    ⟨?_, ?_, ?_⟩, ?_⟩
  · -- nonnegativity
    intro i j
    by_cases h : R (a i) (b j)
    · simp only [h, if_true]
      exact div_nonneg (mul_nonneg (hp i) (hq j)) (classMass_nonneg a p hp _)
    · simp [h]
  · -- row sums
    intro i
    have hcond : ∀ j, (if R (a i) (b j) then p i * q j / classMass R a p (a i) else 0)
        = (if R (b j) (a i) then (p i / classMass R a p (a i)) * q j else 0) := by
      intro j
      have hiff : R (a i) (b j) ↔ R (b j) (a i) := ⟨fun h => hsymm _ _ h, fun h => hsymm _ _ h⟩
      rw [propext hiff]
      by_cases h : R (b j) (a i)
      · simp only [h, if_true]; ring
      · simp [h]
    simp only [hcond]
    rw [sum_ite_const_mul (fun j => R (b j) (a i)) q (p i / classMass R a p (a i))]
    have hsum : (∑ j, if R (b j) (a i) then q j else 0) = classMass R a p (a i) :=
      (hmass (a i)).symm
    rw [hsum]
    by_cases hM0 : classMass R a p (a i) = 0
    · have hpi : p i = 0 := by
        have hle := le_classMass a hrefla p hp i; rw [hM0] at hle; linarith [hp i]
      rw [hpi]; simp
    · field_simp
  · -- column sums
    intro j
    have hcond : ∀ i, (if R (a i) (b j) then p i * q j / classMass R a p (a i) else 0)
        = (if R (a i) (b j) then (q j / classMass R b q (b j)) * p i else 0) := by
      intro i
      by_cases h : R (a i) (b j)
      · have hclass : classMass R a p (a i) = classMass R a p (b j) :=
          classMass_congr hsymm htrans a p h
        rw [hclass, hmass (b j)]; simp only [h, if_true]; ring
      · simp [h]
    simp only [hcond]
    rw [sum_ite_const_mul (fun i => R (a i) (b j)) p (q j / classMass R b q (b j))]
    have hsum : (∑ i, if R (a i) (b j) then p i else 0) = classMass R b q (b j) :=
      hmass (b j)
    rw [hsum]
    by_cases hN0 : classMass R b q (b j) = 0
    · have hqj : q j = 0 := by
        have hle := le_classMass b hreflb q hq j; rw [hN0] at hle; linarith [hq j]
      rw [hqj]; simp
    · field_simp
  · -- support
    intro i j hpos
    by_cases h : R (a i) (b j)
    · exact h
    · simp [h] at hpos

/-- Coupling lemma, `(⟹)`: the lifting of `R` forces equal class probability. -/
theorem classMass_of_coupling {n m : ℕ} {R : α → α → Prop}
    (hsymm : ∀ x y, R x y → R y x) (htrans : ∀ x y z, R x y → R y z → R x z)
    (a : Fin n → α) (p : Fin n → ℝ) (b : Fin m → α) (q : Fin m → ℝ)
    (h : Lift (fun i j => R (a i) (b j)) p q) :
    ∀ x, classMass R a p x = classMass R b q x := by
  obtain ⟨w, ⟨hw, hrow, hcol⟩, hsupp⟩ := h
  intro x
  have key : ∀ i, (if R (a i) x then p i else 0) = ∑ j, if R (a i) x then w i j else 0 := by
    intro i; by_cases h : R (a i) x <;> simp [h, ← hrow i]
  have key2 : ∀ j, (if R (b j) x then q j else 0) = ∑ i, if R (b j) x then w i j else 0 := by
    intro j; by_cases h : R (b j) x <;> simp [h, ← hcol j]
  unfold classMass
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_congr rfl (fun j _ => key2 j),
      Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  by_cases hax : R (a i) x <;> by_cases hbx : R (b j) x
  · simp [hax, hbx]
  · have hwij : w i j = 0 := by
      by_contra hne
      exact hbx (htrans _ _ _ (hsymm _ _ (hsupp i j (lt_of_le_of_ne (hw i j) (Ne.symm hne)))) hax)
    simp [hax, hbx, hwij]
  · have hwij : w i j = 0 := by
      by_contra hne
      exact hax (htrans _ _ _ (hsupp i j (lt_of_le_of_ne (hw i j) (Ne.symm hne))) hbx)
    simp [hax, hbx, hwij]
  · simp [hax, hbx]

/-- A single entry is `≤` its column/row sum, hence `0` when that sum is `0`. -/
theorem entry_zero_of_sum_zero {β : Type*} [Fintype β]
    (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) (b0 : β) (hsum : ∑ b, g b = 0) : g b0 = 0 :=
  le_antisymm (hsum ▸ Finset.single_le_sum (fun b _ => hg b) (Finset.mem_univ b0)) (hg b0)

/-- Lemma 26 (composition of couplings): a coupling of `p` and `q` and a
coupling of `q` and `r` compose into a coupling of `p` and `r`, and every
positive composite weight factors through a positive pair. The witness is
`glue₂`, `w i k = ∑_j w₁ i j · w₂ j k / q j`; `Lift.comp` and `Lift.trans`
state the same composition on liftings. -/
theorem coupling_glue {n m l : ℕ} {p : Fin n → ℝ} {q : Fin m → ℝ} {r : Fin l → ℝ}
    {w1 : Fin n → Fin m → ℝ} {w2 : Fin m → Fin l → ℝ}
    (h1 : IsCoupling p q w1) (h2 : IsCoupling q r w2) :
    ∃ w : Fin n → Fin l → ℝ, IsCoupling p r w ∧
      (∀ i k, 0 < w i k → ∃ j, 0 < w1 i j ∧ 0 < w2 j k) :=
  ⟨glue₂ q w1 w2, h1.glue h2, fun _ _ => glue₂_pos h1 h2⟩

end GradualProb.CouplingLemma


namespace GradualProb

open scoped BigOperators
open GradualProb.CouplingLemma

/-- Sums over the dependent concatenation index decompose into double sums.
Stated with the summand pre-composed with the index projections, so that use
sites can instantiate `g` explicitly and avoid dependent rewriting under the
binder. -/
theorem sum_sigma_proj {m : ℕ} {n : Fin m → ℕ} (g : (i : Fin m) → Fin (n i) → ℝ) :
    (∑ κ : Fin (∑ i, n i),
      g (finSigmaFinEquiv.symm κ).1 (finSigmaFinEquiv.symm κ).2)
      = ∑ i, ∑ k, g i k := by
  rw [Fintype.sum_equiv finSigmaFinEquiv.symm _ (fun s => g s.1 s.2) (fun κ => rfl),
    ← Finset.univ_sigma_univ, Finset.sum_sigma]

section MassOfSigma

variable {α : Type*}

/-- The weight of a predicate on a dependent concatenation of blocks, the
block `i` scaled by `a i`: the `a`-weighted sum of its weights on the blocks. -/
theorem massOf_sigmaFin (P : α → Prop) [DecidablePred P] {m : ℕ} {n : Fin m → ℕ}
    (val : ∀ i, Fin (n i) → α) (a : Fin m → ℝ) (w : ∀ i, Fin (n i) → ℝ) :
    massOf P (fun κ : Fin (∑ i, n i) => val _ (finSigmaFinEquiv.symm κ).2)
        (fun κ => a (finSigmaFinEquiv.symm κ).1 * w _ (finSigmaFinEquiv.symm κ).2)
      = ∑ i, a i * massOf P (val i) (w i) := by
  unfold massOf
  rw [sum_sigma_proj (fun i k => if P (val i k) then a i * w i k else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp

end MassOfSigma

end GradualProb
