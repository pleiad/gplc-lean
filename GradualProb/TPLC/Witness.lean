import GradualProb.TPLC.Evidence

/-!
# The witness construction

The article builds the meet of distribution types and the reordering initial
evidence from one construction, `W_f(D₁, D₂)` (Section 5.2, "Meet Operator"):
for a partial operator `f` on simple types, one entry for each pair `(i, j)` of
entries of the operands in the domain of `f`, with `f(σ_i, σ'_j)` as the type
of the entry, and as formula the coupling condition of Definition 3 between the
two operands, stated over the entries. The meet is `W_⊓` and the reordering
initial evidence is `W_{id₌}` (Definition 11); the tagged evidences that the
reduction rules compute (`emeetD`, `tagReorderD`) and the initial evidence of
an ascription in the elaboration (`tagMeetD`) are the same construction with
tags (`tagWitness`).

This module defines the construction once (`witness`, `tagWitness`) and
proves its entry API: the enumeration of the entries and its two provenance tags
(`witnessCell`, `witnessL`, `witnessR`, and `witnessTag` for either), the
solutions of the formula (`witness_C_iff`), definedness as the lifting of the carrier predicate
(`witness_sat_iff_symLift`), well-formedness (`goodD_witness_of_sat`),
tag-guided reductivity (`tagPrec_witness`) and, for the tagged form,
hereditary validity (`hvalid_tagWitness`) and the transport of marginals along
the tags (`tagWitness_left_marginal`). The instances are defined in
`TPLC/Definitions` (`meetD`, `emeetD`, `reorderD`, `tagReorderD`) and `TPLC/Meet`
(`tagMeetD`); their metatheory in `TPLC/Meet` and `TPLC/Reorder` derives from
this API what does not recurse on the simple-type operator.

## Representation

The domain of `f` is given as a predicate `P` on the pair of entry types,
separately from the entries: on the meet it is runtime consistency `EConsTy`
(Figure 12), which the `Option`-valued `meetTy` does not decide at arrows, and
on `id₌` it is equality. The types of the entries are given as a function on the
entries (`ty : Fin (liveK P D1 D2).card → FTy`) rather than as `f` applied to
the pair,
so that each instance can compute them by structural recursion inside the
`mutual` block of its simple-type operator (`meetDty`, `reorderDty`); that the
type of an entry is `f` of its pair is the lemma `meetD_ty_spec`
(`reorderD_ty_spec`) of the instance. As everywhere, formulas are sets of
solutions, so the operands' probability variables, which the article leaves
free in the formula of `W_f`, are existentially quantified (`witnessC`).
-/

namespace GradualProb.TPLC

open GradualProb.GPLC

open Classical

/-! ## The index set and its enumeration -/

/-- The index set `K` of `W_f(D1, D2)`: the pairs `(i, j)` of entries of the
operands in the domain of `f`, given as the predicate `P` on the two entry
types. Pairs are encoded as `Fin (D1.n * D2.n)` through `finProdFinEquiv`. -/
noncomputable def liveK (P : FTy → FTy → Prop) (D1 D2 : FDist) :
    Finset (Fin (D1.n * D2.n)) :=
  Finset.univ.filter fun k =>
    P (D1.ty (finProdFinEquiv.symm k).1) (D2.ty (finProdFinEquiv.symm k).2)

/-- Membership in the index set: the pair satisfies `P`. -/
theorem mem_liveK {P : FTy → FTy → Prop} {D1 D2 : FDist} {k : Fin (D1.n * D2.n)} :
    k ∈ liveK P D1 D2 ↔
      P (D1.ty (finProdFinEquiv.symm k).1) (D2.ty (finProdFinEquiv.symm k).2) := by
  simp [liveK, Finset.mem_filter]

/-- Enumeration of the index set by `Fin`, in increasing order. -/
noncomputable def liveEmb (P : FTy → FTy → Prop) (D1 D2 : FDist) :
    Fin (liveK P D1 D2).card → Fin (D1.n * D2.n) :=
  fun c => (liveK P D1 D2).orderEmbOfFin rfl c

/-- Every enumerated pair is in the index set. -/
theorem liveEmb_mem (P : FTy → FTy → Prop) (D1 D2 : FDist) (c : Fin (liveK P D1 D2).card) :
    liveEmb P D1 D2 c ∈ liveK P D1 D2 :=
  Finset.orderEmbOfFin_mem (liveK P D1 D2) rfl c

/-- Every pair of the index set is enumerated. -/
theorem liveEmb_exists {P : FTy → FTy → Prop} {D1 D2 : FDist} {k : Fin (D1.n * D2.n)}
    (hk : k ∈ liveK P D1 D2) : ∃ c, liveEmb P D1 D2 c = k := by
  have h := Finset.range_orderEmbOfFin (liveK P D1 D2) rfl
  have hk' : k ∈ Set.range ⇑((liveK P D1 D2).orderEmbOfFin rfl) := by
    rw [h]
    exact Finset.mem_coe.mpr hk
  exact hk'

/-- The enumeration of the index set is injective. -/
theorem liveEmb_inj {P : FTy → FTy → Prop} {D1 D2 : FDist} :
    Function.Injective (liveEmb P D1 D2) := fun _ _ h =>
  (Finset.orderEmbOfFin (liveK P D1 D2) rfl).injective h

/-! ## The entries and their provenance tags

An entry of `W_f(D1, D2)` is read as the pair of operand entries it enumerates;
the two components are its provenance tags, the `l` and `r` of the article's
tagged variable `ω = ⟨α, l, r⟩`. -/

/-- The pair of operand entries that an entry enumerates. -/
noncomputable def witnessCell (P : FTy → FTy → Prop) (D1 D2 : FDist)
    (c : Fin (liveK P D1 D2).card) : Fin D1.n × Fin D2.n :=
  finProdFinEquiv.symm (liveEmb P D1 D2 c)

/-- Left provenance tag of an entry: the index of the left operand's entry it
comes from. -/
noncomputable def witnessL (P : FTy → FTy → Prop) (D1 D2 : FDist)
    (c : Fin (liveK P D1 D2).card) : Fin D1.n :=
  (witnessCell P D1 D2 c).1

/-- Right provenance tag of an entry: the index of the right operand's entry it
comes from. -/
noncomputable def witnessR (P : FTy → FTy → Prop) (D1 D2 : FDist)
    (c : Fin (liveK P D1 D2).card) : Fin D2.n :=
  (witnessCell P D1 D2 c).2

/-- The provenance tag `π` of an entry: `witnessL` or `witnessR`. -/
noncomputable def witnessTag (P : FTy → FTy → Prop) (D1 D2 : FDist) :
    (π : Side) → Fin (liveK P D1 D2).card → Fin (π.pick D1 D2).n
  | .l => witnessL P D1 D2
  | .r => witnessR P D1 D2

/-- The operand entry that the tag `π` of an entry names. -/
theorem witnessTag_ty (P : FTy → FTy → Prop) (D1 D2 : FDist) (π : Side)
    (c : Fin (liveK P D1 D2).card) :
    (π.pick D1 D2).ty (witnessTag P D1 D2 π c)
      = π.pick (D1.ty (witnessL P D1 D2 c)) (D2.ty (witnessR P D1 D2 c)) := by
  cases π <;> rfl

/-- Every entry pairs operand entries in the domain of `f`. -/
theorem witnessCell_prop (P : FTy → FTy → Prop) (D1 D2 : FDist) (c : Fin (liveK P D1 D2).card) :
    P (D1.ty (witnessL P D1 D2 c)) (D2.ty (witnessR P D1 D2 c)) :=
  mem_liveK.mp (liveEmb_mem P D1 D2 c)

/-- The entries, read as pairs of operand entries, are distinct. -/
theorem witnessCell_injective (P : FTy → FTy → Prop) (D1 D2 : FDist) :
    Function.Injective (witnessCell P D1 D2) :=
  finProdFinEquiv.symm.injective.comp liveEmb_inj

/-- Every pair of operand entries in the domain of `f` is an entry. -/
theorem witnessCell_range {P : FTy → FTy → Prop} {D1 D2 : FDist} {i : Fin D1.n} {j : Fin D2.n}
    (h : P (D1.ty i) (D2.ty j)) : (i, j) ∈ Set.range (witnessCell P D1 D2) := by
  obtain ⟨c, hc⟩ := liveEmb_exists (P := P) (D1 := D1) (D2 := D2) (k := finProdFinEquiv (i, j))
    (mem_liveK.mpr (by rwa [Equiv.symm_apply_apply]))
  exact ⟨c, (congrArg finProdFinEquiv.symm hc).trans (Equiv.symm_apply_apply _ _)⟩

/-- Every pair of operand entries in the domain of `f` is an entry, through its
tags. -/
theorem witness_cell_exists {P : FTy → FTy → Prop} {D1 D2 : FDist} {i : Fin D1.n} {j : Fin D2.n}
    (h : P (D1.ty i) (D2.ty j)) : ∃ c, witnessL P D1 D2 c = i ∧ witnessR P D1 D2 c = j :=
  let ⟨c, hc⟩ := witnessCell_range h
  ⟨c, congrArg Prod.fst hc, congrArg Prod.snd hc⟩

/-- An entry is determined by its two tags. -/
theorem witness_cell_unique {P : FTy → FTy → Prop} {D1 D2 : FDist} {c c' : Fin (liveK P D1 D2).card}
    (h1 : witnessL P D1 D2 c = witnessL P D1 D2 c') (h2 : witnessR P D1 D2 c = witnessR P D1 D2 c') :
    c = c' :=
  witnessCell_injective P D1 D2 (Prod.ext h1 h2)

/-- A sum over the entries of a grid function that vanishes on the pairs outside
the domain of `f` is the full double grid sum. -/
theorem sum_witness_grid {P : FTy → FTy → Prop} {D1 D2 : FDist} (G : Fin D1.n → Fin D2.n → ℝ)
    (hdead : ∀ i j, ¬ P (D1.ty i) (D2.ty j) → G i j = 0) :
    (∑ c, G (witnessL P D1 D2 c) (witnessR P D1 D2 c)) = ∑ i, ∑ j, G i j :=
  sum_cells (witnessCell_injective P D1 D2) G fun i j hne =>
    witnessCell_range (of_not_not fun h => hne (hdead i j h))

/-! ## The construction -/

/-- The formula of `W_f(D1, D2)`: the coupling condition between the two
operands over the entries.

In the article the formula mentions the operands' probability variables
freely, conjoined with the operands' formulas. Here formulas are solution
sets, so the operands' solutions `pp`, `qq` are existentially quantified: a
weight vector `w` on the entries is a solution when some solutions of the two
operands are
its marginals, the push-forwards of `w` along the two provenance tags. -/
def witnessC (P : FTy → FTy → Prop) (D1 D2 : FDist) (w : Fin (liveK P D1 D2).card → ℝ) : Prop :=
  ∃ pp qq, D1.C pp ∧ D2.C qq ∧
    (∀ i, pushfwd (witnessL P D1 D2) w i = pp i) ∧
    (∀ j, pushfwd (witnessR P D1 D2) w j = qq j) ∧
    (∀ c, 0 ≤ w c)

/-- The witness construction `W_f(D1, D2)` of the article: one entry for each
pair of operand entries in the domain of `f` (the predicate `P`), with the types
`ty` of the entries, and the coupling formula `witnessC` over the entries. The
number of entries and the formula are those of the components, definitionally. -/
noncomputable def witness (P : FTy → FTy → Prop) (D1 D2 : FDist)
    (ty : Fin (liveK P D1 D2).card → FTy) : FDist :=
  ⟨(liveK P D1 D2).card, ty, witnessC P D1 D2⟩

/-- The entry count of the construction is the size of the index set. -/
@[simp] theorem witness_n (P : FTy → FTy → Prop) (D1 D2 : FDist)
    (ty : Fin (liveK P D1 D2).card → FTy) : (witness P D1 D2 ty).n = (liveK P D1 D2).card := rfl

/-- The entries of the construction are the given entry function. -/
@[simp] theorem witness_ty (P : FTy → FTy → Prop) (D1 D2 : FDist)
    (ty : Fin (liveK P D1 D2).card → FTy) : (witness P D1 D2 ty).ty = ty := rfl

/-- The solutions of the formula, without the existential: a weight vector on
the entries solves it iff its push-forwards along the two tags solve the operands and it
is nonnegative. -/
theorem witness_C_iff {P : FTy → FTy → Prop} {D1 D2 : FDist} {ty : Fin (liveK P D1 D2).card → FTy}
    (w : Fin (witness P D1 D2 ty).n → ℝ) :
    (witness P D1 D2 ty).C w ↔
      D1.C (pushfwd (witnessL P D1 D2) w) ∧ D2.C (pushfwd (witnessR P D1 D2) w) ∧ ∀ c, 0 ≤ w c := by
  constructor
  · rintro ⟨pp, qq, hpp, hqq, hm1, hm2, hnn⟩
    refine ⟨?_, ?_, hnn⟩
    · rwa [show pushfwd (witnessL P D1 D2) w = pp from funext hm1]
    · rwa [show pushfwd (witnessR P D1 D2) w = qq from funext hm2]
  · rintro ⟨h1, h2, hnn⟩
    exact ⟨_, _, h1, h2, fun _ => rfl, fun _ => rfl, hnn⟩

/-- The solutions of the formula are nonnegative. -/
theorem witness_C_nonneg {P : FTy → FTy → Prop} {D1 D2 : FDist}
    {ty : Fin (liveK P D1 D2).card → FTy} {w : Fin (witness P D1 D2 ty).n → ℝ}
    (hw : (witness P D1 D2 ty).C w) : ∀ c, 0 ≤ w c :=
  ((witness_C_iff w).1 hw).2.2

/-! ## Definedness is the lifting of the carrier predicate

The construction is total; the definedness of `W_f(D1, D2)` in the article
is the satisfiability of its formula. A solution of that formula is a weight
vector on the entries whose two push-forwards solve the operands; it relates
them by the lifting of `P` (Definition 3), because every entry is a pair in the
domain of `f` (`Lift.pushfwd_prod`). Conversely, a coupling supported on the
domain of `f` restricts to the entries (`IsCoupling.restrict_of_supp`). -/

/-- A solution of the formula gives the lifting of `P` between the operands:
its two push-forwards are related by the lifting of `P` on the entries. -/
theorem symLift_of_witness_sat {P : FTy → FTy → Prop} {D1 D2 : FDist}
    {ty : Fin (liveK P D1 D2).card → FTy} {w : Fin (witness P D1 D2 ty).n → ℝ}
    (hw : (witness P D1 D2 ty).C w) : SymLift (fun i j => P (D1.ty i) (D2.ty j)) D1.C D2.C :=
  let ⟨h1, h2, hnn⟩ := (witness_C_iff w).1 hw
  ⟨_, _, h1, h2, .pushfwd_prod (witnessCell P D1 D2) hnn (witnessCell_prop P D1 D2)⟩

/-- A coupling between solutions of the operands, supported on the domain of
`f` and read through the provenance tags, is a solution of the formula: the
restriction of the coupling to the entries (`IsCoupling.restrict_of_supp`). -/
theorem witness_C_of_coupling {P : FTy → FTy → Prop} {D1 D2 : FDist}
    {ty : Fin (liveK P D1 D2).card → FTy} {p : Fin D1.n → ℝ} {q : Fin D2.n → ℝ}
    {a : Fin D1.n → Fin D2.n → ℝ} (hp : D1.C p) (hq : D2.C q) (ha : IsCoupling p q a)
    (hs : Supp (fun i j => P (D1.ty i) (D2.ty j)) a) :
    (witness P D1 D2 ty).C (fun c => a (witnessL P D1 D2 c) (witnessR P D1 D2 c)) :=
  have ⟨h1, h2⟩ := ha.restrict_of_supp hs (witnessCell_injective P D1 D2)
    fun _ _ => witnessCell_range
  (witness_C_iff _).2 ⟨(congrArg D1.C h1).mpr hp, (congrArg D2.C h2).mpr hq,
    fun _ => ha.nonneg _ _⟩

/-- Solutions of the operands related by the lifting of `P` give a solution of
the formula. -/
theorem witness_sat_of_lift {P : FTy → FTy → Prop} {D1 D2 : FDist}
    {ty : Fin (liveK P D1 D2).card → FTy} {p : Fin D1.n → ℝ} {q : Fin D2.n → ℝ}
    (hp : D1.C p) (hq : D2.C q) (h : Lift (fun i j => P (D1.ty i) (D2.ty j)) p q) :
    ∃ w, (witness P D1 D2 ty).C w :=
  let ⟨_, hw, hs⟩ := h
  ⟨_, witness_C_of_coupling hp hq hw hs⟩

/-- A three-index weight `T` whose totals over the pairs of entries are a
weight vector `x` and whose totals over the first index are a coupling `ω`
of solutions of the operands supported on the domain of `f`, restricted to
the entries, couples `x` with the solution of the formula that `ω` restricts to
(`isCoupling_restrict_cells`). This is the step shared by the greatest lower
bound of the meet (Lemma 8) and of the reordering (Lemma 48): there `T`
glues two couplings through a shared solution (`glue₃`). -/
theorem witness_coupling_of_glue {P : FTy → FTy → Prop} {D1 D2 : FDist}
    {ty : Fin (liveK P D1 D2).card → FTy} {n : ℕ} {x : Fin n → ℝ}
    {p : Fin D1.n → ℝ} {q : Fin D2.n → ℝ} {ω : Fin D1.n → Fin D2.n → ℝ}
    (hp : D1.C p) (hq : D2.C q) (hω : IsCoupling p q ω)
    (hs : Supp (fun i j => P (D1.ty i) (D2.ty j)) ω)
    {T : Fin n → Fin D1.n → Fin D2.n → ℝ} (hT : ∀ i a b, 0 ≤ T i a b)
    (hrow : ∀ i, ∑ a, ∑ b, T i a b = x i) (hcol : ∀ a b, ∑ i, T i a b = ω a b) :
    ∃ w, (witness P D1 D2 ty).C w ∧
      IsCoupling x w (fun i c => T i (witnessL P D1 D2 c) (witnessR P D1 D2 c)) :=
  ⟨_, witness_C_of_coupling hp hq hω hs,
    (isCoupling_restrict_cells hT (witnessCell_injective P D1 D2) fun i a b h =>
      witnessCell_range (hs a b (hcol a b ▸ lt_of_lt_of_le h
        (Finset.single_le_sum (fun i _ => hT i a b) (Finset.mem_univ i))))).congr
      hrow fun _ => hcol _ _⟩

/-- The lifting of `P` between the operands gives a solution of the formula. -/
theorem witness_sat_of_symLift {P : FTy → FTy → Prop} {D1 D2 : FDist}
    {ty : Fin (liveK P D1 D2).card → FTy}
    (h : SymLift (fun i j => P (D1.ty i) (D2.ty j)) D1.C D2.C) :
    ∃ w, (witness P D1 D2 ty).C w :=
  let ⟨_, _, hp, hq, hl⟩ := h
  witness_sat_of_lift hp hq hl

/-- The formula of `W_f(D1, D2)` is satisfiable iff the operands are related
by the lifting of the domain of `f`. -/
theorem witness_sat_iff_symLift {P : FTy → FTy → Prop} {D1 D2 : FDist}
    {ty : Fin (liveK P D1 D2).card → FTy} :
    (∃ w, (witness P D1 D2 ty).C w) ↔ SymLift (fun i j => P (D1.ty i) (D2.ty j)) D1.C D2.C :=
  ⟨fun ⟨_, hw⟩ => symLift_of_witness_sat hw, witness_sat_of_symLift⟩

/-! ## Well-formedness

The satisfiability clause of well-formedness is the definedness of the
construction; the other clauses on the formula follow from the linearity of
the push-forward (`goodC_pushfwd`), and the entries are well-formed by
hypothesis (each instance proves it by recursion on its simple-type
operator). -/

/-- The formula whose solutions are the nonnegative weight vectors with
push-forwards along `f` and `g` that solve two well-formed formulas is
well-formed when it is satisfiable. This is the shape of the formula of
`W_f(D1, D2)`. -/
theorem goodC_pushfwd {n n1 n2 : ℕ} {C1 : (Fin n1 → ℝ) → Prop}
    {C2 : (Fin n2 → ℝ) → Prop} {C : (Fin n → ℝ) → Prop}
    (f : Fin n → Fin n1) (g : Fin n → Fin n2) (h1 : GoodC n1 C1) (h2 : GoodC n2 C2)
    (hC : ∀ w, C w ↔ C1 (pushfwd f w) ∧ C2 (pushfwd g w) ∧ ∀ c, 0 ≤ w c)
    (hsat : ∃ w, C w) : GoodC n C := by
  refine ⟨hsat, fun w hw => ((hC w).1 hw).2.2, ?_, ?_⟩
  · intro w hw
    rw [← sum_pushfwd f w]
    exact h1.mass _ ((hC w).1 hw).1
  · intro w w' hw hw' t ht0 ht1
    obtain ⟨hpp, hqq, hnn⟩ := (hC w).1 hw
    obtain ⟨hpp', hqq', hnn'⟩ := (hC w').1 hw'
    refine (hC _).2 ⟨?_, ?_, fun c =>
      add_nonneg (mul_nonneg ht0 (hnn c)) (mul_nonneg (sub_nonneg.2 ht1) (hnn' c))⟩
    · rw [pushfwd_mix]
      exact h1.convex _ _ hpp hpp' t ht0 ht1
    · rw [pushfwd_mix]
      exact h2.convex _ _ hqq hqq' t ht0 ht1

/-- `W_f(D1, D2)` is well-formed when the operands' formulas are, its entries
are, and its formula is satisfiable. -/
theorem goodD_witness_of_sat {P : FTy → FTy → Prop} {D1 D2 : FDist}
    {ty : Fin (liveK P D1 D2).card → FTy} (hg1 : Good D1) (hg2 : Good D2)
    (hty : ∀ c, GoodTy (ty c)) (hsat : ∃ w, (witness P D1 D2 ty).C w) :
    GoodD (witness P D1 D2 ty) :=
  .mk (goodC_pushfwd (witnessL P D1 D2) (witnessR P D1 D2) hg1 hg2 witness_C_iff hsat) hty

/-! ## Reductivity along the tags

`W_f(D1, D2)` is tag-guidedly reductive (`TagPrec`) into each operand along
the corresponding provenance tag as soon as each entry is below the operand
entry its tag names: the push-forward clause is the marginal clause of the
formula. Runtime precision follows by `eprecD_of_tagPrec`, since the solutions
are nonnegative. -/

/-- Tag-guided reductivity into the operand `π` along its provenance tag. -/
theorem tagPrec_witness (π : Side) {P : FTy → FTy → Prop} {D1 D2 : FDist}
    {ty : Fin (liveK P D1 D2).card → FTy}
    (h : ∀ c, EPrecTy (ty c) ((π.pick D1 D2).ty (witnessTag P D1 D2 π c))) :
    TagPrec (witness P D1 D2 ty) (π.pick D1 D2) (witnessTag P D1 D2 π) := by
  cases π
  · exact ⟨h, fun w hw => ((witness_C_iff w).1 hw).1⟩
  · exact ⟨h, fun w hw => ((witness_C_iff w).1 hw).2.1⟩

/-- `W_f(D1, D2)` is below its operand `π` in runtime precision when each
entry is below the entry of that operand its tag names. -/
theorem eprecD_witness (π : Side) {P : FTy → FTy → Prop} {D1 D2 : FDist}
    {ty : Fin (liveK P D1 D2).card → FTy}
    (h : ∀ c, EPrecTy (ty c) ((π.pick D1 D2).ty (witnessTag P D1 D2 π c))) :
    EPrecD (witness P D1 D2 ty) (π.pick D1 D2) :=
  eprecD_of_tagPrec (tagPrec_witness π h) fun _ => witness_C_nonneg

/-! ## The tagged construction

The evidences that the reduction rules and the elaboration compute are
`W_f(D1, D2)` with tags: the entry `(i, j)` carries the tag `l i` of the left
operand's entry and the tag `r j` of the right one's. For the initial evidence
of an ascription in the elaboration (`tagMeetD`) and the routing evidence of a
`let` (`tagReorderD`) the tags are
the entry indices themselves; for consistent transitivity (`emeetD`) they are
the tags of the operand evidences, so that the tags compose. -/

/-- `W_f(D1, D2)` as a tagged evidence: the number of entries and the formula of
`witness`, the tagged types `ty` of the entries, and as tags of the entry
`(i, j)` the tags `l i` and
`r j` of the operand entries. -/
noncomputable def tagWitness (P : FTy → FTy → Prop) (D1 D2 : FDist)
    (ty : Fin (liveK P D1 D2).card → TagTy) (l : Fin D1.n → ℕ) (r : Fin D2.n → ℕ) : TagD :=
  ⟨(liveK P D1 D2).card, ty, witnessC P D1 D2,
    fun c => l (witnessL P D1 D2 c), fun c => r (witnessR P D1 D2 c)⟩

/-- The erasure of the tagged construction is the construction on the erased
entries. -/
theorem tagWitness_toF (P : FTy → FTy → Prop) (D1 D2 : FDist)
    (ty : Fin (liveK P D1 D2).card → TagTy) (l : Fin D1.n → ℕ) (r : Fin D2.n → ℕ) :
    (tagWitness P D1 D2 ty l r).toF = witness P D1 D2 fun c => (ty c).toF := rfl

/-- A tagged entry whose erasure is defined is defined, and is the entry read
with the default `?`. -/
theorem some_getD_of_map_toF {o : Option TagTy} {t : FTy}
    (h : Option.map TagTy.toF o = some t) : o = some (o.getD .unk) := by
  cases o with
  | none => simp at h
  | some _ => rfl

/-- The tagged construction with the entry indices as tags is hereditarily
valid on both sides (Definition 9) as soon as its erasure is tag-guidedly
reductive along the two tags and every entry is hereditarily valid for the
pair of entries its tags name. -/
theorem hvalid_tagWitness {P : FTy → FTy → Prop} {D1 D2 : FDist}
    {ty : Fin (liveK P D1 D2).card → TagTy}
    (hL : TagPrec (tagWitness P D1 D2 ty Fin.val Fin.val).toF D1 (witnessL P D1 D2))
    (hR : TagPrec (tagWitness P D1 D2 ty Fin.val Fin.val).toF D2 (witnessR P D1 D2))
    (hcL : ∀ c, HVTag .l (ty c) (D1.ty (witnessL P D1 D2 c)))
    (hcR : ∀ c, HVTag .r (ty c) (D2.ty (witnessR P D1 D2 c))) :
    HValid .l (tagWitness P D1 D2 ty Fin.val Fin.val) D1 ∧
      HValid .r (tagWitness P D1 D2 ty Fin.val Fin.val) D2 :=
  ⟨.mk (fun c => (witnessL P D1 D2 c).isLt) hL hcL,
   .mk (fun c => (witnessR P D1 D2 c).isLt) hR hcR⟩

/-- Marginals along the left tags. If the left tags of the left operand send
each of its solutions to a solution of `E`, then the left tags of the tagged
construction (the left tags of the left operand at the left projection of each
entry) send each of its solutions to a solution of `E`: the left marginal
clause of the formula, followed by the push-forward along the operand's tags
(`pushfwd_comp`). -/
theorem tagWitness_left_marginal {P : FTy → FTy → Prop} {D1 D2 E : FDist}
    {ty : Fin (liveK P D1 D2).card → TagTy} {l : Fin D1.n → ℕ} {r : Fin D2.n → ℕ}
    {ω : Fin (tagWitness P D1 D2 ty l r).n → ℝ} (hω : (tagWitness P D1 D2 ty l r).toF.C ω)
    (hl : ∀ i, l i < E.n) (hpush : ∀ p, D1.C p → E.C (pushfwd (fun i => (⟨l i, hl i⟩ : Fin E.n)) p)) :
    E.C (pushfwd (fun c => (⟨l (witnessL P D1 D2 c), hl _⟩ : Fin E.n)) ω) :=
  (congrArg E.C (pushfwd_comp _ _ ω)).mp (hpush _ ((witness_C_iff ω).1 hω).1)

end GradualProb.TPLC
