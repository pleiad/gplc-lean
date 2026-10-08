import GradualProb.Coupling
import GradualProb.GPLC.Types

/-!
# Equality of static types

This module formalizes the coupling equality `=` of Section 4 on the types of
SPLC (`EqTy` on simple types, `EqD` on distribution types), proves it is an
equivalence relation (Lemma 17), and proves Lemma 2 (alternative characterization
of equality): the relation defined by the rules of `=ₛ` in Section 3 coincides
with the coupling equality on static types.

## Main results

* `EqTy.refl`, `EqD.refl`, `EqTy.symm`, `EqD.symm`, `EqTy.trans`, `EqD.trans`:
  Lemma 17 (equality is an equivalence): reflexive on static types, symmetric
  and transitive.
* `eqTy_iff_coupling`: Lemma 2, item 1, as the rules of `=ₛ` on simple types.
* `eqD_dist_iff_coupling`, `eqD_iff_coupling`: Lemma 2, item 2, as the rule of
  `=ₛ` on distribution types (equal class probability and coverage in both
  directions).
* `eqD_ofFn_iff`: `EqD` on the entry lists of two finite families is the
  lifting of `EqTy` to the families, with coverage in both directions.
* `eqRules_unique`, `eq_satisfies_rules`, `eq_iff_coupling`: Lemma 2, both
  items: any pair of relations satisfying the rules of `=ₛ` coincides with
  `EqTy`/`EqD` on static types.

## Reading guide

First the coupling equality and its equivalence properties; then the
class-probability reading of `=ₛ` on distribution types and its equivalence with `EqD`; last the
rules of `=ₛ` as a predicate on pairs of relations and their unique solution.
-/


namespace GradualProb.SPLC

open scoped BigOperators
open Classical
open GradualProb.CouplingLemma


/- The coupling equality `=` of Section 4.  The distribution rule asks for the
lifting (Definition 2, `Lift`) of equality to the two entry lists, whose
weights are the probabilities of the entries, indexed by position.  Since an
inductive cannot mention itself under the definition `Lift`, the lifted
relation is an explicit witness `R` on positions, contained in `EqTy`;
`EqD.intro` and `EqD.coup` state the lifting of `EqTy` itself.  The two
coverage premises of the rule ("every entry has an equal entry on the other
side") are stated with witness functions `fL`, `fR` instead of `∀ ∃`;
`EqD.intro` and `EqD.cov` convert from and to the existential form. -/
mutual
/-- Coupling equality on simple types. -/
inductive EqTy : Ty → Ty → Prop where
  | real : EqTy .real .real
  | bool : EqTy .bool .bool
  | arrow : ∀ {s1 d1 s2 d2}, EqTy s1 s2 → EqD d1 d2 →
              EqTy (.arrow s1 d1) (.arrow s2 d2)
/-- Coupling equality on distribution types: the lifting of equality to the
two entry lists (a coupling of their probabilities supported on equal simple
types), and coverage in both directions (every entry, whatever its
probability, has an equal entry on the other side). -/
inductive EqD : DTy → DTy → Prop where
  | dist : ∀ {es1 es2 : List (Ty × GProb)} (R : Fin es1.length → Fin es2.length → Prop)
             (fL : Fin es1.length → Fin es2.length)
             (fR : Fin es2.length → Fin es1.length),
             (∀ i j, R i j → EqTy (es1.get i).1 (es2.get j).1) →
             Lift R (fun i => pval (es1.get i).2) (fun j => pval (es2.get j).2) →
             (∀ i, EqTy (es1.get i).1 (es2.get (fL i)).1) →
             (∀ j, EqTy (es1.get (fR j)).1 (es2.get j).1) →
             EqD (.dist es1) (.dist es2)
end

/-- `τ =ₛ τ'`, the equality of static simple types (`EqTy`), as Section 3
writes it. -/
scoped infix:50 (name := eqTyStx) " =ₛ " => EqTy
/-- `T =ₛ T'`, the equality of static distribution types (`EqD`). -/
scoped infix:50 (name := eqDStx) " =ₛ " => EqD

/-- The two coverage premises of the distribution rule of `=`, as a separate
predicate: every entry of either type has an `EqTy`-equal entry in the other. -/
def CovD : DTy → DTy → Prop
  | .dist es1, .dist es2 =>
      (∀ i : Fin es1.length, ∃ j, EqTy (es1.get i).1 (es2.get j).1) ∧
      (∀ j : Fin es2.length, ∃ i, EqTy (es1.get i).1 (es2.get j).1)

/-- Introduction form of `EqD`: the lifting of `EqTy` itself, and coverages
in existential form. -/
theorem EqD.intro {es1 es2 : List (Ty × GProb)}
    (hl : Lift (fun i j => EqTy (es1.get i).1 (es2.get j).1)
      (fun i => pval (es1.get i).2) (fun j => pval (es2.get j).2))
    (hcov : CovD (.dist es1) (.dist es2)) : EqD (.dist es1) (.dist es2) := by
  choose fL hfL using hcov.1
  choose fR hfR using hcov.2
  exact .dist _ fL fR (fun _ _ h => h) hl hfL hfR

/-- The lifting premise of an `EqD`, stated on `EqTy`. -/
theorem EqD.coup {es1 es2 : List (Ty × GProb)} : EqD (.dist es1) (.dist es2) →
    Lift (fun i j => EqTy (es1.get i).1 (es2.get j).1)
      (fun i => pval (es1.get i).2) (fun j => pval (es2.get j).2)
  | .dist _ _ _ hR hl _ _ => hl.mono hR

/-- The coverage premises of an `EqD`, in existential form. -/
theorem EqD.cov : ∀ {T1 T2 : DTy}, EqD T1 T2 → CovD T1 T2
  | _, _, .dist _ fL fR _ _ hfL hfR =>
      ⟨fun i => ⟨fL i, hfL i⟩, fun j => ⟨fR j, hfR j⟩⟩

/-- Each entry of a static entry list has a concrete, nonnegative probability. -/
theorem entry_static_mem {es : List (Ty × GProb)} (h : IsStaticEntries es) :
    ∀ e ∈ es, ∃ r, e.2 = GProb.q r ∧ 0 ≤ r := fun e he =>
  let ⟨_, r, h1, h2, _⟩ := h e he; ⟨r, h1, h2⟩

/-- The simple type of each entry of a static entry list is static. -/
theorem entry_static_ty_mem {es : List (Ty × GProb)} (h : IsStaticEntries es) :
    ∀ e ∈ es, IsStaticTy e.1 := fun e he => (h e he).1

/-- `pval` of a static entry is nonnegative. -/
theorem pval_nonneg_mem {es : List (Ty × GProb)} (h : IsStaticEntries es) :
    ∀ e ∈ es, 0 ≤ pval e.2 := by
  intro e he
  obtain ⟨r, hr, hrnn⟩ := entry_static_mem h e he
  rw [hr]; exact hrnn

/-- `pval` of a static entry is at most `1`. -/
theorem pval_le_one_mem {es : List (Ty × GProb)} (h : IsStaticEntries es) :
    ∀ e ∈ es, pval e.2 ≤ 1 := by
  intro e he
  obtain ⟨-, r, hr, -, hr1⟩ := h e he
  rw [hr]; exact hr1

/- Lemma 17, reflexivity on static types (diagonal coupling, `Lift.refl`). -/
mutual
/-- Lemma 17 (equality is an equivalence), reflexivity on simple types: every
static simple type `τ` satisfies `τ =ₛ τ`. -/
theorem EqTy.refl : ∀ {t : Ty}, IsStaticTy t → t =ₛ t
  | _, .real => EqTy.real
  | _, .bool => EqTy.bool
  | _, .arrow hs hd => EqTy.arrow (EqTy.refl hs) (EqD.refl hd)
/-- Lemma 17 (equality is an equivalence), reflexivity on distribution types:
every static distribution type `T` satisfies `T =ₛ T`. -/
theorem EqD.refl : ∀ {T : DTy}, IsStaticDTy T → T =ₛ T
  | .dist es, .dist ht hp =>
      have he : IsStaticEntries es := fun e he => ⟨ht e he, hp e he⟩
      .dist (fun i j => i = j) id id
        (fun i _ hij => hij ▸ EqTy.refl (ht _ (List.get_mem es i)))
        (.refl (fun i => pval_nonneg_mem he _ (List.get_mem es i)) fun _ => rfl)
        (fun i => EqTy.refl (ht _ (List.get_mem es i)))
        (fun j => EqTy.refl (ht _ (List.get_mem es j)))
end

/- Lemma 17, symmetry (transpose the coupling, `Lift.symm`). -/
mutual
/-- Lemma 17 (equality is an equivalence), symmetry on simple types: if
`τ₁ =ₛ τ₂`, then `τ₂ =ₛ τ₁`. -/
theorem EqTy.symm : ∀ {s t : Ty}, s =ₛ t → t =ₛ s
  | _, _, .real => EqTy.real
  | _, _, .bool => EqTy.bool
  | _, _, .arrow hst hd => EqTy.arrow (EqTy.symm hst) (EqD.symm hd)
/-- Lemma 17 (equality is an equivalence), symmetry on distribution types: if
`T₁ =ₛ T₂`, then `T₂ =ₛ T₁`. -/
theorem EqD.symm : ∀ {T1 T2 : DTy}, T1 =ₛ T2 → T2 =ₛ T1
  | _, _, .dist R fL fR hR hl hfL hfR =>
      .dist (fun j i => R i j) fR fL (fun j i hij => EqTy.symm (hR i j hij)) hl.symm
        (fun j => EqTy.symm (hfR j))
        (fun i => EqTy.symm (hfL i))
end

/- Lemma 17, transitivity (compose the liftings, `Lift.comp`). -/
mutual
/-- Lemma 17 (equality is an equivalence), transitivity on simple types: if
`τ₁ =ₛ τ₂` and `τ₂ =ₛ τ₃`, then `τ₁ =ₛ τ₃`. -/
theorem EqTy.trans : ∀ {s t u : Ty}, s =ₛ t → t =ₛ u → s =ₛ u
  | _, _, _, .real, h2 => h2
  | _, _, _, .bool, h2 => h2
  | _, _, _, .arrow hst1 hd1, .arrow hst2 hd2 =>
      EqTy.arrow (EqTy.trans hst1 hst2) (EqD.trans hd1 hd2)
/-- Lemma 17 (equality is an equivalence), transitivity on distribution types:
if `T₁ =ₛ T₂` and `T₂ =ₛ T₃`, then `T₁ =ₛ T₃`. -/
theorem EqD.trans : ∀ {T1 T2 T3 : DTy}, T1 =ₛ T2 → T2 =ₛ T3 → T1 =ₛ T3
  | _, _, _, .dist R1 fL1 fR1 hR1 hl1 hfL1 hfR1, .dist R2 fL2 fR2 hR2 hl2 hfL2 hfR2 =>
      .dist (Relation.Comp R1 R2) (fun i => fL2 (fL1 i)) (fun k => fR1 (fR2 k))
        (fun i k ⟨j, hj1, hj2⟩ => EqTy.trans (hR1 i j hj1) (hR2 j k hj2))
        (hl1.comp hl2)
        (fun i => EqTy.trans (hfL1 i) (hfL2 (fL1 i)))
        (fun k => EqTy.trans (hfR1 (fR2 k)) (hfR2 k))
end

/-! ## The class-probability reading of `=ₛ` on distribution types -/

/-- Equal class probability on every simple type: for every `x`, the two types give
the same total probability to the entries `EqTy`-equal to `x` (`classMass`,
over the `Fin`-indexed presentation of the lists). -/
def MassEqD : DTy → DTy → Prop
  | .dist es1, .dist es2 => ∀ x,
      classMass EqTy (fun i => (es1.get i).1) (fun i => pval (es1.get i).2) x
        = classMass EqTy (fun j => (es2.get j).1) (fun j => pval (es2.get j).2) x

/-- Lemma 2 (alternative characterization of equality), item 2, core form: on
static distribution types, `EqD` holds iff the two types have equal class
probability and coverage in both directions.  The class probability ranges
over every simple type here; `massEqD_iff_supp` restricts it to the support. -/
theorem eqD_dist_iff_coupling {es1 es2 : List (Ty × GProb)}
    (h1 : IsStaticEntries es1) (h2 : IsStaticEntries es2) :
    EqD (.dist es1) (.dist es2) ↔
      (MassEqD (.dist es1) (.dist es2) ∧ CovD (.dist es1) (.dist es2)) := by
  constructor
  · intro h
    exact ⟨classMass_of_coupling (R := EqTy) (fun _ _ h => EqTy.symm h)
      (fun _ _ _ h1 h2 => EqTy.trans h1 h2) _ _ _ _ h.coup, h.cov⟩
  · rintro ⟨h, hcov⟩
    exact EqD.intro (coupling_of_classMass (R := EqTy)
      (fun _ _ h => EqTy.symm h) (fun _ _ _ h1 h2 => EqTy.trans h1 h2)
      (fun i => (es1.get i).1) (fun i => pval (es1.get i).2)
      (fun j => (es2.get j).1) (fun j => pval (es2.get j).2)
      (fun i => EqTy.refl (entry_static_ty_mem h1 (es1.get i) (List.get_mem es1 i)))
      (fun j => EqTy.refl (entry_static_ty_mem h2 (es2.get j) (List.get_mem es2 j)))
      (fun i => pval_nonneg_mem h1 (es1.get i) (List.get_mem es1 i))
      (fun j => pval_nonneg_mem h2 (es2.get j) (List.get_mem es2 j))
      h) hcov

/-- A list is the list of the family of its entries, mapped. -/
theorem map_eq_ofFn_get {α β : Type*} (g : α → β) (l : List α) :
    l.map g = List.ofFn fun i => g (l.get i) := by
  conv_lhs => rw [← List.ofFn_get l]
  exact List.map_ofFn

/-- Coupling equality of the entry lists of two finite families: the lifting
of `EqTy` to the families, with the probabilities of the entries as weights,
and coverage in both directions.  Every entry list is the list of a family
(`List.ofFn_get`, `map_eq_ofFn_get`), so this is the form in which the
constructions on liftings (`Lift.smul`, `Lift.append`, `Lift.sigmaFin`) give
equalities of distribution types. -/
theorem eqD_ofFn_iff {n n' : ℕ} {e : Fin n → Ty × GProb} {e' : Fin n' → Ty × GProb} :
    EqD (.dist (List.ofFn e)) (.dist (List.ofFn e')) ↔
      Lift (fun i j => EqTy (e i).1 (e' j).1) (fun i => pval (e i).2) (fun j => pval (e' j).2) ∧
      (∀ i, ∃ j, EqTy (e i).1 (e' j).1) ∧ (∀ j, ∃ i, EqTy (e i).1 (e' j).1) := by
  have hn : (List.ofFn e).length = n := List.length_ofFn
  have hn' : (List.ofFn e').length = n' := List.length_ofFn
  constructor
  · intro h
    refine ⟨?_, fun i => ?_, fun j => ?_⟩
    · simpa using h.coup.reindex (finCongr hn.symm) (finCongr hn'.symm)
    · obtain ⟨j, hj⟩ := h.cov.1 (Fin.cast hn.symm i)
      exact ⟨Fin.cast hn' j, by simpa using hj⟩
    · obtain ⟨i, hi⟩ := h.cov.2 (Fin.cast hn'.symm j)
      exact ⟨Fin.cast hn i, by simpa using hi⟩
  · rintro ⟨hl, hcovL, hcovR⟩
    refine EqD.intro ?_ ⟨fun i => ?_, fun j => ?_⟩
    · simpa using hl.reindex (finCongr hn) (finCongr hn')
    · obtain ⟨j, hj⟩ := hcovL (Fin.cast hn i)
      exact ⟨Fin.cast hn'.symm j, by simpa using hj⟩
    · obtain ⟨i, hi⟩ := hcovR (Fin.cast hn' j)
      exact ⟨Fin.cast hn.symm i, by simpa using hi⟩

/-- Coupling equality of two `List.ofFn` lists with the same probabilities, by
the diagonal coupling (`IsCoupling.diag`); the coverage premises are taken as
hypotheses. -/
theorem eqD_ofFn_diag {N : ℕ} (a b : Fin N → Ty) (wt : Fin N → ℝ)
    (hnn : ∀ k, 0 ≤ wt k) (heq : ∀ k, 0 < wt k → EqTy (a k) (b k))
    (hcovL : ∀ k, ∃ l, EqTy (a k) (b l))
    (hcovR : ∀ l, ∃ k, EqTy (a k) (b l)) :
    EqD (.dist (List.ofFn fun k => (a k, GProb.q (wt k))))
         (.dist (List.ofFn fun k => (b k, GProb.q (wt k)))) := by
  refine eqD_ofFn_iff.2 ⟨⟨_, .diag hnn, fun k l hpos => ?_⟩, hcovL, hcovR⟩
  obtain ⟨rfl, hk⟩ := pos_of_ite_pos hpos
  exact heq k hk


/-- Lemma 2 (alternative characterization of equality), item 1: on simple types the
coupling equality satisfies exactly the rules of `=ₛ` (base type with the same
base type, arrow with arrow componentwise). -/
theorem eqTy_iff_coupling {τ1 τ2 : Ty} : τ1 =ₛ τ2 ↔
    ((τ1 = .real ∧ τ2 = .real) ∨ (τ1 = .bool ∧ τ2 = .bool) ∨
      ∃ s1 d1 s2 d2, τ1 = .arrow s1 d1 ∧ τ2 = .arrow s2 d2 ∧
        s1 =ₛ s2 ∧ d1 =ₛ d2) := by
  constructor
  · intro h
    cases h with
    | real => exact Or.inl ⟨rfl, rfl⟩
    | bool => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | arrow hs hd => exact Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl, hs, hd⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨s1, d1, s2, d2, rfl, rfl, hs, hd⟩)
    · exact .real
    · exact .bool
    · exact .arrow hs hd

/-- The first premise of the distribution rule of `=ₛ` (Section 3), quantified
over the support of the two types: the class of every entry of positive
probability, on either side, has the same probability in both types. -/
def MassEqSuppD : DTy → DTy → Prop
  | .dist es1, .dist es2 =>
      let cm1 := classMass EqTy (fun i => (es1.get i).1) (fun i => pval (es1.get i).2)
      let cm2 := classMass EqTy (fun j => (es2.get j).1) (fun j => pval (es2.get j).2)
      (∀ i, 0 < pval (es1.get i).2 → cm1 (es1.get i).1 = cm2 (es1.get i).1) ∧
      (∀ j, 0 < pval (es2.get j).2 → cm1 (es2.get j).1 = cm2 (es2.get j).1)

/-- A class of positive probability contains an entry of positive probability. -/
theorem exists_pos_of_classMass_pos {n : ℕ} {a : Fin n → Ty} {p : Fin n → ℝ} {x : Ty}
    (hpos : 0 < classMass EqTy a p x) : ∃ i, EqTy (a i) x ∧ 0 < p i :=
  massOf_pos (P := fun y => EqTy y x) hpos

/-- On static types, equal class probability over the support (`MassEqSuppD`,
as in the article) is equivalent to equal class probability over every type
(`MassEqD`). -/
theorem massEqD_iff_supp {es1 es2 : List (Ty × GProb)}
    (h1 : IsStaticEntries es1) (h2 : IsStaticEntries es2) :
    MassEqD (.dist es1) (.dist es2) ↔ MassEqSuppD (.dist es1) (.dist es2) := by
  have hsymm : ∀ x y, EqTy x y → EqTy y x := fun _ _ h => EqTy.symm h
  have htrans : ∀ x y z, EqTy x y → EqTy y z → EqTy x z :=
    fun _ _ _ h1 h2 => EqTy.trans h1 h2
  have hp1 : ∀ i, 0 ≤ pval (es1.get i).2 :=
    fun i => pval_nonneg_mem h1 _ (List.get_mem es1 i)
  have hp2 : ∀ j, 0 ≤ pval (es2.get j).2 :=
    fun j => pval_nonneg_mem h2 _ (List.get_mem es2 j)
  constructor
  · intro h
    exact ⟨fun i _ => h _, fun j _ => h _⟩
  · rintro ⟨hL, hR⟩ x
    set cm1 := classMass EqTy (fun i => (es1.get i).1) (fun i => pval (es1.get i).2)
      with hcm1
    set cm2 := classMass EqTy (fun j => (es2.get j).1) (fun j => pval (es2.get j).2)
      with hcm2
    by_cases hx1 : 0 < cm1 x
    · obtain ⟨i, hi, hpi⟩ := exists_pos_of_classMass_pos hx1
      have e1 : cm1 x = cm1 (es1.get i).1 :=
        classMass_congr hsymm htrans _ _ (hsymm _ _ hi)
      have e2 : cm2 x = cm2 (es1.get i).1 :=
        classMass_congr hsymm htrans _ _ (hsymm _ _ hi)
      rw [e1, e2]; exact hL i hpi
    · have hz1 : cm1 x = 0 := eq_zero_of_nonneg_of_not_pos (classMass_nonneg _ _ hp1 x) hx1
      by_cases hx2 : 0 < cm2 x
      · obtain ⟨j, hj, hpj⟩ := exists_pos_of_classMass_pos hx2
        have e1 : cm1 x = cm1 (es2.get j).1 :=
          classMass_congr hsymm htrans _ _ (hsymm _ _ hj)
        have e2 : cm2 x = cm2 (es2.get j).1 :=
          classMass_congr hsymm htrans _ _ (hsymm _ _ hj)
        rw [e1, e2]; exact hR j hpj
      · have hz2 : cm2 x = 0 := eq_zero_of_nonneg_of_not_pos (classMass_nonneg _ _ hp2 x) hx2
        rw [hz1, hz2]

/-- Lemma 2 (alternative characterization of equality), item 2: on static
distribution types, `EqD` holds iff the premises of the distribution rule of
`=ₛ` hold (equal class probability on the support, coverage in both directions). -/
theorem eqD_iff_coupling {T1 T2 : DTy} (h1 : IsStaticDTy T1) (h2 : IsStaticDTy T2) :
    T1 =ₛ T2 ↔ (MassEqSuppD T1 T2 ∧ CovD T1 T2) := by
  cases T1 with
  | dist es1 =>
    cases T2 with
    | dist es2 =>
      rw [eqD_dist_iff_coupling h1.entries h2.entries,
        massEqD_iff_supp h1.entries h2.entries]


/-!
## The rules of `=ₛ` define exactly the coupling equality

The article defines `=ₛ` (Section 3) by four rules.  The rule for
distribution types uses `=ₛ` inside its own premises: the class probability
`T(τ) = Σ { pᵢ | τᵢ =ₛ τ }` and the two coverage premises.  The occurrence in
the class probability is not positive, so the rules cannot be an `inductive`; they
determine a relation because every premise mentions only simple types of
smaller depth.

`EqRules R RD` says that the pair `(R, RD)` satisfies the four rules of `=ₛ`
as equivalences, on static types.  `eqRules_unique` proves that any such
pair coincides with `EqTy`/`EqD` on static types, and `eq_satisfies_rules` that
`EqTy`/`EqD` satisfies the rules (`eqTy_iff_coupling`, `eqD_iff_coupling`).
Together: the relation the rules of Section 3 define is `EqTy`/`EqD`, which is
the relation every Lean statement uses where the article writes `=ₛ`.
-/


/-! ### Depth of a type -/

mutual
/-- Nesting depth of a simple type. -/
def tyDepth : Ty → ℕ
  | .arrow s d => max (tyDepth s) (dDepth d) + 1
  | _ => 0
/-- Nesting depth of a distribution type: one more than its entries. -/
def dDepth : DTy → ℕ
  | .dist es => esDepth es + 1
/-- Maximum depth of the simple types of an entry list. -/
def esDepth : List (Ty × GProb) → ℕ
  | [] => 0
  | (t, _) :: es => max (tyDepth t) (esDepth es)
end

/-- Every entry of a list has depth at most the list's depth. -/
theorem esDepth_get : ∀ (es : List (Ty × GProb)) (i : Fin es.length),
    tyDepth (es.get i).1 ≤ esDepth es
  | [], i => absurd i.isLt (by simp)
  | (t, p) :: es, ⟨0, _⟩ => by simp [esDepth]
  | (t, p) :: es, ⟨n + 1, h⟩ => by
      have := esDepth_get es ⟨n, by simpa using h⟩
      simp only [esDepth, List.get_eq_getElem, List.getElem_cons_succ] at this ⊢
      exact le_trans this (le_max_right _ _)

/-- Every entry of a distribution type has depth smaller than the type. -/
theorem dist_entry_depth_lt (es : List (Ty × GProb)) (i : Fin es.length) :
    tyDepth (es.get i).1 < dDepth (.dist es) := by
  have := esDepth_get es i
  simp only [dDepth]; omega

/-! ### The rule of `=ₛ` on distribution types, parametric in the entry relation -/

/-- The premises of the distribution rule of `=ₛ` (Section 3), with `R` in
place of `=ₛ` on the entries: equal class probability on the support of either
type,
and coverage in both directions. -/
def EqRuleD (R : Ty → Ty → Prop) : DTy → DTy → Prop
  | .dist es1, .dist es2 =>
      let cm1 := classMass R (fun i => (es1.get i).1) (fun i => pval (es1.get i).2)
      let cm2 := classMass R (fun j => (es2.get j).1) (fun j => pval (es2.get j).2)
      ((∀ i, 0 < pval (es1.get i).2 → cm1 (es1.get i).1 = cm2 (es1.get i).1) ∧
        (∀ j, 0 < pval (es2.get j).2 → cm1 (es2.get j).1 = cm2 (es2.get j).1)) ∧
      ((∀ i : Fin es1.length, ∃ j, R (es1.get i).1 (es2.get j).1) ∧
        (∀ j : Fin es2.length, ∃ i, R (es1.get i).1 (es2.get j).1))

/-- With `R = EqTy`, the premises are those of `eqD_iff_coupling`. -/
theorem eqRuleD_eq_iff (T1 T2 : DTy) :
    EqRuleD EqTy T1 T2 ↔ (MassEqSuppD T1 T2 ∧ CovD T1 T2) := by
  cases T1; cases T2; rfl

/-- The rule only reads `R` on pairs of entries of the two types. -/
theorem eqRuleD_congr {R R' : Ty → Ty → Prop} {es1 es2 : List (Ty × GProb)}
    (h : ∀ x y, (x ∈ (es1 ++ es2).map Prod.fst) → (y ∈ (es1 ++ es2).map Prod.fst) →
      (R x y ↔ R' x y)) :
    EqRuleD R (.dist es1) (.dist es2) ↔ EqRuleD R' (.dist es1) (.dist es2) := by
  have m1 : ∀ i : Fin es1.length, (es1.get i).1 ∈ (es1 ++ es2).map Prod.fst := fun i =>
    List.mem_map.2 ⟨es1.get i, List.mem_append_left _ (List.get_mem _ _), rfl⟩
  have m2 : ∀ j : Fin es2.length, (es2.get j).1 ∈ (es1 ++ es2).map Prod.fst := fun j =>
    List.mem_map.2 ⟨es2.get j, List.mem_append_right _ (List.get_mem _ _), rfl⟩
  have cm : ∀ {n} (f : Fin n → Ty) (w : Fin n → ℝ) (x : Ty),
      (∀ k, f k ∈ (es1 ++ es2).map Prod.fst) → x ∈ (es1 ++ es2).map Prod.fst →
      classMass R f w x = classMass R' f w x := by
    intro n f w x hf hx
    unfold classMass
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : R (f k) x
    · rw [if_pos hk, if_pos ((h _ _ (hf k) hx).1 hk)]
    · rw [if_neg hk, if_neg (fun h' => hk ((h _ _ (hf k) hx).2 h'))]
  simp only [EqRuleD]
  refine and_congr (and_congr ?_ ?_) (and_congr ?_ ?_)
  · refine forall_congr' (fun i => imp_congr_right (fun _ => ?_))
    rw [cm _ _ _ m1 (m1 i), cm _ _ _ m2 (m1 i)]
  · refine forall_congr' (fun j => imp_congr_right (fun _ => ?_))
    rw [cm _ _ _ m1 (m2 j), cm _ _ _ m2 (m2 j)]
  · exact forall_congr' (fun i => exists_congr (fun j => h _ _ (m1 i) (m2 j)))
  · exact forall_congr' (fun j => exists_congr (fun i => h _ _ (m1 i) (m2 j)))

/-! ### The rules of `=ₛ` and their unique solution -/

/-- `(R, RD)` satisfies the four rules of `=ₛ` (Section 3), read as
equivalences, on static types. -/
structure EqRules (R : Ty → Ty → Prop) (RD : DTy → DTy → Prop) : Prop where
  ty : ∀ τ1 τ2, IsStaticTy τ1 → IsStaticTy τ2 →
    (R τ1 τ2 ↔ ((τ1 = .real ∧ τ2 = .real) ∨ (τ1 = .bool ∧ τ2 = .bool) ∨
      ∃ s1 d1 s2 d2, τ1 = .arrow s1 d1 ∧ τ2 = .arrow s2 d2 ∧ R s1 s2 ∧ RD d1 d2))
  d : ∀ T1 T2, IsStaticDTy T1 → IsStaticDTy T2 → (RD T1 T2 ↔ EqRuleD R T1 T2)

/-- `EqTy`/`EqD` satisfies the rules of `=ₛ` (`eqTy_iff_coupling` and
`eqD_iff_coupling`). -/
theorem eq_satisfies_rules : EqRules EqTy EqD where
  ty _ _ _ _ := eqTy_iff_coupling
  d T1 T2 h1 h2 := by rw [eqD_iff_coupling h1 h2, eqRuleD_eq_iff]

/-- The rules of `=ₛ` have one solution on static types: any pair of
relations satisfying them coincides with `EqTy`/`EqD`.  By induction on the
depth: every premise of a rule mentions only types of smaller depth. -/
theorem eqRules_unique {R : Ty → Ty → Prop} {RD : DTy → DTy → Prop}
    (hR : EqRules R RD) :
    (∀ τ1 τ2, IsStaticTy τ1 → IsStaticTy τ2 → (R τ1 τ2 ↔ EqTy τ1 τ2)) ∧
    (∀ T1 T2, IsStaticDTy T1 → IsStaticDTy T2 → (RD T1 T2 ↔ EqD T1 T2)) := by
  -- `P n`: agreement on all static types of depth below `n`.
  have key : ∀ n,
      (∀ τ1 τ2, IsStaticTy τ1 → IsStaticTy τ2 → tyDepth τ1 < n → tyDepth τ2 < n →
        (R τ1 τ2 ↔ EqTy τ1 τ2)) ∧
      (∀ T1 T2, IsStaticDTy T1 → IsStaticDTy T2 → dDepth T1 < n → dDepth T2 < n →
        (RD T1 T2 ↔ EqD T1 T2)) := by
    intro n
    induction n with
    | zero => exact ⟨fun _ _ _ _ h => absurd h (Nat.not_lt_zero _),
                     fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ n ih =>
      obtain ⟨ihT, ihD⟩ := ih
      -- distribution types of depth ≤ n: entries have depth < n
      have hD : ∀ T1 T2, IsStaticDTy T1 → IsStaticDTy T2 → dDepth T1 < n + 1 →
          dDepth T2 < n + 1 → (RD T1 T2 ↔ EqD T1 T2) := by
        intro T1 T2 h1 h2 d1 d2
        cases T1 with
        | dist es1 =>
        cases T2 with
        | dist es2 =>
        have he1 := h1.entries
        have he2 := h2.entries
        rw [hR.d _ _ h1 h2, (eq_satisfies_rules).d _ _ h1 h2]
        apply eqRuleD_congr
        intro x y hx hy
        have hmem : ∀ z, z ∈ (es1 ++ es2).map Prod.fst → IsStaticTy z ∧ tyDepth z < n := by
          intro z hz
          obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
          rcases List.mem_append.1 he with he | he
          · obtain ⟨i, rfl⟩ := List.get_of_mem he
            exact ⟨isStaticEntries_get_ty he1 i,
              by have := dist_entry_depth_lt es1 i; omega⟩
          · obtain ⟨j, rfl⟩ := List.get_of_mem he
            exact ⟨isStaticEntries_get_ty he2 j,
              by have := dist_entry_depth_lt es2 j; omega⟩
        exact ihT x y (hmem x hx).1 (hmem y hy).1 (hmem x hx).2 (hmem y hy).2
      refine ⟨?_, hD⟩
      intro τ1 τ2 h1 h2 d1 d2
      rw [hR.ty _ _ h1 h2, (eq_satisfies_rules).ty _ _ h1 h2]
      refine or_congr Iff.rfl (or_congr Iff.rfl ?_)
      constructor
      · rintro ⟨s1, e1, s2, e2, rfl, rfl, hs, hd⟩
        cases h1 with
        | arrow hs1 hd1 =>
        cases h2 with
        | arrow hs2 hd2 =>
        simp only [tyDepth] at d1 d2
        exact ⟨s1, e1, s2, e2, rfl, rfl,
          (ihT _ _ hs1 hs2 (by omega) (by omega)).1 hs,
          (hD _ _ hd1 hd2 (by omega) (by omega)).1 hd⟩
      · rintro ⟨s1, e1, s2, e2, rfl, rfl, hs, hd⟩
        cases h1 with
        | arrow hs1 hd1 =>
        cases h2 with
        | arrow hs2 hd2 =>
        simp only [tyDepth] at d1 d2
        exact ⟨s1, e1, s2, e2, rfl, rfl,
          (ihT _ _ hs1 hs2 (by omega) (by omega)).2 hs,
          (hD _ _ hd1 hd2 (by omega) (by omega)).2 hd⟩
  refine ⟨fun τ1 τ2 h1 h2 => ?_, fun T1 T2 h1 h2 => ?_⟩
  · exact (key (max (tyDepth τ1) (tyDepth τ2) + 1)).1 τ1 τ2 h1 h2
      (by omega) (by omega)
  · exact (key (max (dDepth T1) (dDepth T2) + 1)).2 T1 T2 h1 h2
      (by omega) (by omega)

/-- Lemma 2 (alternative characterization of equality), both items.  For any
relations `=ₛ` on static simple and distribution types satisfying the rules of Section 3, `=ₛ`
coincides with the coupling equality `=` of Section 4 (`EqTy`/`EqD`). -/
theorem eq_iff_coupling {R : Ty → Ty → Prop} {RD : DTy → DTy → Prop}
    (hR : EqRules R RD) :
    (∀ τ1 τ2, IsStaticTy τ1 → IsStaticTy τ2 → (R τ1 τ2 ↔ EqTy τ1 τ2)) ∧
    (∀ T1 T2, IsStaticDTy T1 → IsStaticDTy T2 → (RD T1 T2 ↔ EqD T1 T2)) :=
  eqRules_unique hR

end GradualProb.SPLC
