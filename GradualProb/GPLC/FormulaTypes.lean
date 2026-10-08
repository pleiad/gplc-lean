import GradualProb.Coupling

/-!
# Formula types

Formula types (Figure 5), the types the type system of GPLC manipulates, with
the relations and operators defined on them: well-formedness (Definition 5),
inductive consistency (Definition 4) and inductive type precision (Figure 8),
the coverage-free runtime relations of Figure 12 used by TPLC, and the type
operators of Figure 6 (scaled union for probabilistic choice, convex hull for
the conditional and for choice at an unknown probability, weighted union for
`let`, singleton types, `dom`/`cod`).

## Main results

* `cons_prec_ty`, `cons_prec_d`: Lemma 24 (consistency precision), for the
  relations on formula types; `econs_eprec_ty`, `econs_eprec_d`: its form for
  the runtime relations.
* `prec_choose`, `prec_choose_unk`, `prec_chooseU`, `prec_let`, `prec_point`,
  `domcod_mono`: Lemma 25 (monotonicity of the type operators), used by the
  static gradual guarantee (Theorem 2).
* `goodD_choose`, `goodD_chooseU`, `goodD_let`, `goodD_point`, `goodD_topF`:
  the type operators preserve well-formedness (used by Lemma 4).
* `PrecTy.refl`/`PrecD.refl`, `PrecTy.trans`/`PrecD.trans`,
  `EPrecTy.refl`/`EPrecD.refl`, `EPrecTy.trans`/`EPrecD.trans`,
  `ConsTy.refl`/`ConsD.refl`: reflexivity and transitivity.
* `FDist.ext`: extensionality of formula distribution types through a cast on
  the number of entries.

## Reading guide

Carriers and well-formedness come first, then precision and consistency on
formula types, the runtime relations `EPrec*`/`ECons*`, the transfer lemmas,
and finally the operators with their monotonicity and well-formedness lemmas.
-/


namespace GradualProb.GPLC

open scoped BigOperators
open GradualProb.CouplingLemma

/-! ## Carriers -/

mutual
/-- Formula simple types: gradual simple types whose arrow codomains are
formula distribution types. -/
inductive FTy : Type where
  | real : FTy
  | bool : FTy
  | unk  : FTy
  | arrow : FTy → FDist → FTy
/-- A formula distribution type `[φ] {{σ_i^{p_i}}}_{i∈I}`: the number of
entries `n`, the entry simple types, and the closing formula `φ` represented by
its set of solutions, a predicate `C : (Fin n → ℝ) → Prop` on the vector of
entry probabilities. The grammar of formulas, tagged variables and their
freshness have no counterpart: conjunction, the equations of the type operators,
the marginal equations of the meet and the guarded implication of the `let`
reduction are operations on solution sets, and the probability variables of an
operand that the article keeps free in a result formula are existentially
quantified in the result's solution set.

`FDist` is a `structure` so that `D.n`, `D.ty` and `D.C` are projections: a
type built by a definition of the form `⟨n, ty, C⟩` has these three components
definitionally. Being recursive (through `FTy`), it has no definitional
eta, and a definition that pattern-matches on it does not reduce on a
variable; the operators on distribution types are therefore written as
`⟨…, f D, …⟩` with projections, and only their entry function `f` (the one
component that recurses on the entries) is defined by pattern matching. -/
structure FDist : Type where
  /-- The number of entries. -/
  n : ℕ
  /-- The entry simple types. -/
  ty : Fin n → FTy
  /-- The solution set of the closing formula. -/
  C : (Fin n → ℝ) → Prop
end

/-- Extensionality of `FDist` through a cast on the number of entries. -/
theorem FDist.ext {D1 D2 : FDist} (hn : D1.n = D2.n)
    (ht : ∀ i, D1.ty i = D2.ty (Fin.cast hn i))
    (hC : ∀ p : Fin D2.n → ℝ, D1.C (fun i => p (Fin.cast hn i)) ↔ D2.C p) :
    D1 = D2 := by
  cases D1 with | mk n1 t1 C1 =>
  cases D2 with | mk n2 t2 C2 =>
  simp only [FDist.n] at hn
  subst hn
  have ht' : t1 = t2 := funext (fun i => by simpa using ht i)
  subst ht'
  have hC' : C1 = C2 := by
    funext p; have := hC p; simpa using this
  subst hC'
  rfl

/-! ## Well-formedness -/

/-- The conditions of Definition 5 on the closing formula of a distribution
type: it is satisfiable, every solution is nonnegative (the article's solutions
range over `[0,1]`) and sums to `1` (the field `mass`), and the solution set is
convex. The
condition that every tagged variable occurs in the formula has no counterpart,
since formulas are solution sets over the entry probabilities. -/
structure GoodC (n : ℕ) (C : (Fin n → ℝ) → Prop) : Prop where
  sat : ∃ p, C p
  nonneg : ∀ p, C p → ∀ i, 0 ≤ p i
  mass : ∀ p, C p → (∑ i, p i) = 1
  convex : ∀ p q, C p → C q → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    C (fun i => t * p i + (1 - t) * q i)

/-- The closing formula of `D` satisfies the conditions of Definition 5. -/
def Good (D : FDist) : Prop := GoodC D.n D.C

/- Definition 5 (type well-formedness), for formula simple and distribution
types: `Good` at every distribution type, including arrow codomains. -/
mutual
/-- Definition 5 (type and environment well-formedness), formula simple types:
well-formed formula simple types. -/
inductive GoodTy : FTy → Prop where
  | real : GoodTy .real
  | bool : GoodTy .bool
  | unk  : GoodTy .unk
  | arrow : ∀ {s D}, GoodTy s → GoodD D → GoodTy (.arrow s D)
/-- Definition 5 (type and environment well-formedness), formula distribution
types: the closing formula is `Good` and every entry type is well-formed. -/
inductive GoodD : FDist → Prop where
  | mk : ∀ {D : FDist}, GoodC D.n D.C → (∀ i, GoodTy (D.ty i)) → GoodD D
end

/-- The closing formula of a well-formed distribution type is `Good`. -/
theorem GoodD.good {D : FDist} : GoodD D → Good D
  | .mk h _ => h

/-- A good type has at least one entry. -/
theorem Good.pos {D : FDist} (h : Good D) : 0 < D.n := by
  by_contra hn
  push_neg at hn
  have h0 : D.n = 0 := Nat.le_zero.mp hn
  obtain ⟨p, hp⟩ := h.sat
  have hm := h.mass p hp
  have hE : IsEmpty (Fin D.n) := by rw [h0]; infer_instance
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hm
  norm_num at hm

/-! ## Precision and consistency on formula types -/

/- Type precision on formula types, inductively (Figure 8). -/
mutual
/-- Type precision `⊑` of Figure 8, formula simple types. It is sound for
Definition 6 (type precision) by Lemma 5. -/
inductive PrecTy : FTy → FTy → Prop where
  | real : PrecTy .real .real
  | bool : PrecTy .bool .bool
  | unk  : ∀ {s}, PrecTy s .unk
  | arrow : ∀ {s1 D1 s2 D2}, PrecTy s1 s2 → PrecD D1 D2 →
      PrecTy (.arrow s1 D1) (.arrow s2 D2)
/-- Type precision `⊑` of Figure 8, formula distribution types: the
distribution rule of Figure 8. Every solution of the left formula is
related to some solution of the right one by the lifting of precision
(`SymLiftAll`), and the two coverage clauses give every entry of either side a
precise partner on the other. Since an inductive cannot mention itself under
the definition `SymLiftAll`, the lifted relation is an explicit witness `R` on
the entries, contained in `PrecTy`; and the existentials of the coverage
clauses are the witness functions `fL`, `fR`. `PrecD.intro`, `PrecD.covL`,
`PrecD.covR` and `PrecD.coup` state the rule on `PrecTy` itself, with the
coverages in existential form. -/
inductive PrecD : FDist → FDist → Prop where
  | mk : ∀ {D1 D2 : FDist} (R : Fin D1.n → Fin D2.n → Prop)
      (fL : Fin D1.n → Fin D2.n) (fR : Fin D2.n → Fin D1.n),
      (∀ i j, R i j → PrecTy (D1.ty i) (D2.ty j)) →
      SymLiftAll R D1.C D2.C →
      (∀ i, PrecTy (D1.ty i) (D2.ty (fL i))) →
      (∀ j, PrecTy (D1.ty (fR j)) (D2.ty j)) →
      PrecD D1 D2
end

/-- `σ ⊑ τ`, type precision on formula simple types (Figure 8). The article
writes `⊑` for eight relations; Lean overloads the symbol for the ones whose
arguments have different types (`PrecTy`, `PrecD`, `PrecP`, `PrecCtx`, the
term precision `GPLC.PrecV`/`GPLC.PrecT`, the closed term precision of TPLC, and
the precision of configurations `TPLC.DConfPrec`) and gives a distinct notation
to the others (runtime precision `⊑̇`, the term precision of TPLC in context
`Γ ⊑ Γ' ⊢ m ⊑ m'`, the tag-aware
precision `σ ⊑ τ ⊢[π] ε ⊑̇ ε'`, and `⊑ᴬᴳᵀ`). -/
scoped infix:50 (name := precTyStx) " ⊑ " => PrecTy
/-- `D ⊑ D'`, type precision on formula distribution types (Figure 8). -/
scoped infix:50 (name := precDStx) " ⊑ " => PrecD

/- Definition 4 (type consistency, inductively). -/
mutual
/-- Definition 4 (type consistency, inductively), formula simple types:
consistency `∼`. -/
inductive ConsTy : FTy → FTy → Prop where
  | real : ConsTy .real .real
  | bool : ConsTy .bool .bool
  | unkL : ∀ {t}, ConsTy .unk t
  | unkR : ∀ {t}, ConsTy t .unk
  | arrow : ∀ {s1 D1 s2 D2}, ConsTy s1 s2 → ConsD D1 D2 →
      ConsTy (.arrow s1 D1) (.arrow s2 D2)
/-- Definition 4 (type consistency, inductively), formula distribution types:
the lifting of consistency to the two symbolic distributions (`SymLift`: a
coupling of a solution of each formula whose positive cells relate consistent
entries), plus the two coverage clauses. As in `PrecD`, the lifted relation is
an explicit witness `R` contained in `ConsTy`, and the coverage existentials
are the witness functions `fL`, `fR`. `ConsD.intro`, `ConsD.coup` and
`ConsD.cov` state the rule on `ConsTy` itself. -/
inductive ConsD : FDist → FDist → Prop where
  | mk : ∀ {D1 D2 : FDist} (R : Fin D1.n → Fin D2.n → Prop)
      (fL : Fin D1.n → Fin D2.n) (fR : Fin D2.n → Fin D1.n),
      (∀ i j, R i j → ConsTy (D1.ty i) (D2.ty j)) →
      SymLift R D1.C D2.C →
      (∀ i, ConsTy (D1.ty i) (D2.ty (fL i))) →
      (∀ j, ConsTy (D1.ty (fR j)) (D2.ty j)) →
      ConsD D1 D2
end

/-- `σ ∼ τ`, type consistency on formula simple types (Definition 4). -/
scoped infix:50 (name := consTyStx) " ∼ " => ConsTy
/-- `D ∼ D'`, type consistency on formula distribution types (Definition 4). -/
scoped infix:50 (name := consDStx) " ∼ " => ConsD

/-- Introduction form: the lifting of `PrecTy` itself, coverages in
existential form (the function witnesses are chosen inside). -/
theorem PrecD.intro {D1 D2 : FDist}
    (hcovL : ∀ i, ∃ j, PrecTy (D1.ty i) (D2.ty j))
    (hcovR : ∀ j, ∃ i, PrecTy (D1.ty i) (D2.ty j))
    (h : SymLiftAll (fun i j => PrecTy (D1.ty i) (D2.ty j)) D1.C D2.C) :
    PrecD D1 D2 := by
  choose fL hfL using hcovL
  choose fR hfR using hcovR
  exact .mk _ fL fR (fun _ _ hij => hij) h hfL hfR

/-- Left coverage of a precision, in existential form. -/
theorem PrecD.covL {D1 D2 : FDist} : PrecD D1 D2 →
    ∀ i, ∃ j, PrecTy (D1.ty i) (D2.ty j)
  | .mk _ fL _ _ _ hfL _, i => ⟨fL i, hfL i⟩

/-- Right coverage of a precision, in existential form. -/
theorem PrecD.covR {D1 D2 : FDist} : PrecD D1 D2 →
    ∀ j, ∃ i, PrecTy (D1.ty i) (D2.ty j)
  | .mk _ _ fR _ _ _ hfR, j => ⟨fR j, hfR j⟩

/-- The lifting clause of a precision, stated on `PrecTy`. -/
theorem PrecD.coup {D1 D2 : FDist} : PrecD D1 D2 →
    SymLiftAll (fun i j => PrecTy (D1.ty i) (D2.ty j)) D1.C D2.C
  | .mk _ _ _ hR hl _ _ => hl.mono hR

/-- The two coverage clauses of consistency (Definition 4) as a separate
predicate: every entry of either side has a consistent partner on the other. -/
def ConsCovD (D1 D2 : FDist) : Prop :=
  (∀ i, ∃ j, ConsTy (D1.ty i) (D2.ty j)) ∧
  (∀ j, ∃ i, ConsTy (D1.ty i) (D2.ty j))

/-- Introduction form of `ConsD`: the lifting of `ConsTy` itself, coverages in
existential form (the function witnesses are chosen inside). -/
theorem ConsD.intro {D1 D2 : FDist}
    (hl : SymLift (fun i j => ConsTy (D1.ty i) (D2.ty j)) D1.C D2.C)
    (hcov : ConsCovD D1 D2) : ConsD D1 D2 := by
  choose fL hfL using hcov.1
  choose fR hfR using hcov.2
  exact .mk _ fL fR (fun _ _ hij => hij) hl hfL hfR

/-- The lifting clause of a consistency, stated on `ConsTy`. -/
theorem ConsD.coup {D1 D2 : FDist} : ConsD D1 D2 →
    SymLift (fun i j => ConsTy (D1.ty i) (D2.ty j)) D1.C D2.C
  | .mk _ _ _ hR hl _ _ => hl.mono hR

/-- The coverage clauses of a consistency, in existential form. -/
theorem ConsD.cov {D1 D2 : FDist} : ConsD D1 D2 → ConsCovD D1 D2
  | .mk _ fL fR _ _ hcovL hcovR =>
      ⟨fun i => ⟨fL i, hcovL i⟩, fun j => ⟨fR j, hcovR j⟩⟩

/-! ## The runtime relations

The relations that TPLC applies to runtime objects (evidences, the domain of the
meet and of reordering, the comparison of evidences in term precision) are the
coverage-free relations of Figure 12: the distribution clause keeps the
lifting and drops the two coverage clauses. Every other clause is the
corresponding clause of `PrecTy`/`ConsTy`. -/

mutual
/-- Runtime precision (Figure 12), on simple types. -/
inductive EPrecTy : FTy → FTy → Prop where
  | real : EPrecTy .real .real
  | bool : EPrecTy .bool .bool
  | unk  : ∀ {s}, EPrecTy s .unk
  | arrow : ∀ {s1 D1 s2 D2}, EPrecTy s1 s2 → EPrecD D1 D2 →
      EPrecTy (.arrow s1 D1) (.arrow s2 D2)
/-- Runtime precision (Figure 12), on distribution types: the lifting
clause of `PrecD`, with the relation `R` as an explicit witness, and no coverage
clauses. -/
inductive EPrecD : FDist → FDist → Prop where
  | mk : ∀ {D1 D2 : FDist} (R : Fin D1.n → Fin D2.n → Prop),
      (∀ i j, R i j → EPrecTy (D1.ty i) (D2.ty j)) →
      SymLiftAll R D1.C D2.C →
      EPrecD D1 D2
end

/-- `σ ⊑̇ τ`, runtime precision on formula simple types (Figure 12). The
token is `⊑` followed by the combining dot above (U+0307), the article's
`\dot\sqsubseteq`. -/
scoped infix:50 (name := ePrecTyStx) " ⊑̇ " => EPrecTy
/-- `D ⊑̇ D'`, runtime precision on formula distribution types (Figure 12). -/
scoped infix:50 (name := ePrecDStx) " ⊑̇ " => EPrecD

/-- Introduction form of `EPrecD`: the lifting of `EPrecTy` itself. -/
theorem EPrecD.intro {D1 D2 : FDist}
    (h : SymLiftAll (fun i j => EPrecTy (D1.ty i) (D2.ty j)) D1.C D2.C) :
    EPrecD D1 D2 :=
  .mk _ (fun _ _ hij => hij) h

/-- The lifting clause of `EPrecD`, stated on `EPrecTy`. -/
theorem EPrecD.coup {D1 D2 : FDist} : EPrecD D1 D2 →
    SymLiftAll (fun i j => EPrecTy (D1.ty i) (D2.ty j)) D1.C D2.C
  | .mk _ hR hl => hl.mono hR

/-! Precision on formula types implies runtime precision (forget coverage). -/
mutual
/-- If `σ ⊑ τ` on formula simple types, then `σ` is below `τ` for runtime
precision. -/
theorem eprecTy_of_precTy : ∀ {σ τ : FTy}, PrecTy σ τ → EPrecTy σ τ
  | _, _, .real => .real
  | _, _, .bool => .bool
  | _, _, .unk => .unk
  | _, _, .arrow hs hD => .arrow (eprecTy_of_precTy hs) (eprecD_of_precD hD)
/-- If `D₁ ⊑ D₂` on formula distribution types, then `D₁` is below `D₂` for
runtime precision. -/
theorem eprecD_of_precD : ∀ {D1 D2 : FDist}, PrecD D1 D2 → EPrecD D1 D2
  | _, _, .mk R _ _ hR hl _ _ =>
      .mk R (fun i j hij => eprecTy_of_precTy (hR i j hij)) hl
end

mutual
/-- Runtime consistency (Figure 12), on simple types. By Lemma 34, it is
the definedness of the meet (`TPLC.meetD_sat_iff_econsD`). -/
inductive EConsTy : FTy → FTy → Prop where
  | real : EConsTy .real .real
  | bool : EConsTy .bool .bool
  | unkL : ∀ {t}, EConsTy .unk t
  | unkR : ∀ {t}, EConsTy t .unk
  | arrow : ∀ {s1 D1 s2 D2}, EConsTy s1 s2 → EConsD D1 D2 →
      EConsTy (.arrow s1 D1) (.arrow s2 D2)
/-- Runtime consistency (Figure 12), on distribution types: the lifting
clause of `ConsD` (a coupling of a solution of each formula whose positive
cells relate consistent entries), with the relation `R` as an explicit witness,
and no coverage clauses. An entry to which the coupling gives probability `0`
needs no partner. -/
inductive EConsD : FDist → FDist → Prop where
  | mk : ∀ {D1 D2 : FDist} (R : Fin D1.n → Fin D2.n → Prop),
      (∀ i j, R i j → EConsTy (D1.ty i) (D2.ty j)) →
      SymLift R D1.C D2.C →
      EConsD D1 D2
end

/-- `σ ∼̇ τ`, runtime consistency on formula simple types (Figure 12). The
token is `∼` followed by the combining dot above (U+0307), the article's
`\dot\sim`. -/
scoped infix:50 (name := eConsTyStx) " ∼̇ " => EConsTy
/-- `D ∼̇ D'`, runtime consistency on formula distribution types (Figure 12). -/
scoped infix:50 (name := eConsDStx) " ∼̇ " => EConsD

/-- Introduction form of `EConsD`: the lifting of `EConsTy` itself. -/
theorem EConsD.intro {D1 D2 : FDist}
    (h : SymLift (fun i j => EConsTy (D1.ty i) (D2.ty j)) D1.C D2.C) :
    EConsD D1 D2 :=
  .mk _ (fun _ _ hij => hij) h

/-- The lifting clause of a runtime consistency, stated on `EConsTy`. -/
theorem EConsD.coup {D1 D2 : FDist} : EConsD D1 D2 →
    SymLift (fun i j => EConsTy (D1.ty i) (D2.ty j)) D1.C D2.C
  | .mk _ hR hl => hl.mono hR

/-! Consistency (Definition 4) implies runtime consistency (forget coverage). -/
mutual
/-- If `σ ∼ τ` on formula simple types, then `σ` and `τ` are runtime
consistent. -/
theorem econsTy_of_consTy : ∀ {σ τ : FTy}, ConsTy σ τ → EConsTy σ τ
  | _, _, .real => .real
  | _, _, .bool => .bool
  | _, _, .unkL => .unkL
  | _, _, .unkR => .unkR
  | _, _, .arrow hs hD => .arrow (econsTy_of_consTy hs) (econsD_of_consD hD)
/-- Lemma 31 (equality defined), with `cons_of_eq_d`, `realizesD_lift` and
`TPLC.meetD_sat_iff_econsD`: if `D₁ ∼ D₂` on formula distribution types, then
`D₁` and `D₂` are runtime consistent. -/
theorem econsD_of_consD : ∀ {D1 D2 : FDist}, ConsD D1 D2 → EConsD D1 D2
  | _, _, .mk R _ _ hR hl _ _ =>
      .mk R (fun i j hij => econsTy_of_consTy (hR i j hij)) hl
end

/-! Lemma 24 (consistency precision), for the runtime relations: runtime
consistency is preserved when both sides are replaced by types less precise for
runtime precision. This is what transports the definedness of evidence
combination along precision. -/
mutual
/-- Lemma 24 (consistency precision), runtime relations on simple types:
if `σ₁` and `σ₂` are runtime consistent and each is below `σ₁'`, `σ₂'` for
runtime precision, then `σ₁'` and `σ₂'` are runtime consistent. -/
theorem econs_eprec_ty : ∀ {σ1 σ2 σ1' σ2' : FTy},
    σ1 ∼̇ σ2 → σ1 ⊑̇ σ1' → σ2 ⊑̇ σ2' → σ1' ∼̇ σ2'
  | _, _, _, _, _, .unk, _ => .unkL
  | _, _, _, _, _, .real, .unk => .unkR
  | _, _, _, _, _, .bool, .unk => .unkR
  | _, _, _, _, _, .arrow _ _, .unk => .unkR
  | _, _, _, _, hc, .real, .real => hc
  | _, _, _, _, hc, .real, .bool => nomatch hc
  | _, _, _, _, hc, .real, .arrow _ _ => nomatch hc
  | _, _, _, _, hc, .bool, .bool => hc
  | _, _, _, _, hc, .bool, .real => nomatch hc
  | _, _, _, _, hc, .bool, .arrow _ _ => nomatch hc
  | _, _, _, _, hc, .arrow _ _, .real => nomatch hc
  | _, _, _, _, hc, .arrow _ _, .bool => nomatch hc
  | _, _, _, _, hc, .arrow hs1 hd1, .arrow hs2 hd2 => by
      cases hc with
      | arrow hcs hcd =>
        exact .arrow (econs_eprec_ty hcs hs1 hs2) (econs_eprec_d hcd hd1 hd2)
/-- Lemma 24 (consistency precision), runtime relations on distribution
types: if `D₁` and `D₂` are runtime consistent and each is below `D₁'`, `D₂'`
for runtime precision, then `D₁'` and `D₂'` are runtime consistent. -/
theorem econs_eprec_d : ∀ {D1 D2 D1' D2' : FDist},
    D1 ∼̇ D2 → D1 ⊑̇ D1' → D2 ⊑̇ D2' → D1' ∼̇ D2'
  | _, _, _, _, .mk R hR hl, .mk R1 hR1 hc1, .mk R2 hR2 hc2 =>
      .mk (fun i' j' => ∃ i j, R1 i i' ∧ R i j ∧ R2 j j')
        (fun i' j' ⟨i, j, h1, h, h2⟩ => econs_eprec_ty (hR i j h) (hR1 i i' h1) (hR2 j j' h2))
        ((hl.comp_left hc1 (T := fun i' j => ∃ i, R1 i i' ∧ R i j)
            fun i _ _ h1 h => ⟨i, h1, h⟩).comp_right hc2
          fun _ j _ ⟨i, h1, h⟩ h2 => ⟨i, j, h1, h, h2⟩)
end

/-! Reflexivity (over well-formed types) and transitivity of runtime
precision. -/

mutual
/-- Runtime precision is reflexive on well-formed formula simple types. -/
theorem EPrecTy.refl : ∀ {t : FTy}, GoodTy t → EPrecTy t t
  | _, .real => .real
  | _, .bool => .bool
  | _, .unk => .unk
  | _, .arrow hs hD => .arrow (EPrecTy.refl hs) (EPrecD.refl hD)
/-- Runtime precision is reflexive on well-formed formula distribution types. -/
theorem EPrecD.refl : ∀ {D : FDist}, GoodD D → EPrecD D D
  | D, .mk hC hty =>
      .mk (fun i j => i = j) (by rintro i j rfl; exact EPrecTy.refl (hty i))
        (.refl hC.nonneg fun _ => rfl)
end

mutual
/-- Runtime precision on formula simple types is transitive. -/
theorem EPrecTy.trans : ∀ {a b c : FTy}, EPrecTy a b → EPrecTy b c → EPrecTy a c
  | _, _, _, .real, h => h
  | _, _, _, .bool, h => h
  | _, _, _, .unk, h => by cases h; exact .unk
  | _, _, _, .arrow hs1 hd1, h => by
      cases h with
      | arrow hs2 hd2 => exact .arrow (EPrecTy.trans hs1 hs2) (EPrecD.trans hd1 hd2)
      | unk => exact .unk
/-- Runtime precision on formula distribution types is transitive. -/
theorem EPrecD.trans : ∀ {A B C : FDist}, EPrecD A B → EPrecD B C → EPrecD A C
  | _, _, _, .mk RAB hABty hAB, .mk RBC hBCty hBC =>
      .mk (Relation.Comp RAB RBC)
        (fun a c ⟨b, hab, hbc⟩ => EPrecTy.trans (hABty a b hab) (hBCty b c hbc))
        (hAB.trans hBC fun _ b _ hab hbc => ⟨b, hab, hbc⟩)
end

/-- Satisfiability transports to the less precise side: the coupling clause
of runtime precision maps every solution of the left formula to a solution of
the right one. -/
theorem eprecD_sat {D1 D2 : FDist} (h : EPrecD D1 D2) (hs : ∃ p, D1.C p) :
    ∃ q, D2.C q := by
  obtain ⟨p, hp⟩ := hs
  obtain ⟨q, hq, -⟩ := h.coup p hp
  exact ⟨q, hq⟩

/-! ## Reflexivity of precision (over well-formed types) -/

mutual
/-- `σ ⊑ σ` for every well-formed formula simple type `σ`. -/
theorem PrecTy.refl : ∀ {t : FTy}, GoodTy t → PrecTy t t
  | _, .real => .real
  | _, .bool => .bool
  | _, .unk => .unk
  | _, .arrow hs hD => .arrow (PrecTy.refl hs) (PrecD.refl hD)
/-- `D ⊑ D` for every well-formed formula distribution type `D`. -/
theorem PrecD.refl : ∀ {D : FDist}, GoodD D → PrecD D D
  | D, .mk hC hty =>
      .mk (fun i j => i = j) id id (by rintro i j rfl; exact PrecTy.refl (hty i))
        (.refl hC.nonneg fun _ => rfl)
        (fun i => PrecTy.refl (hty i)) (fun j => PrecTy.refl (hty j))
end

/-! ## Transitivity of precision

The liftings compose (`SymLiftAll.trans`, which glues the two couplings along
their shared middle marginal), and the coverage witnesses compose as
functions. -/

mutual
/-- Precision on formula simple types is transitive. -/
theorem PrecTy.trans : ∀ {a b c : FTy}, PrecTy a b → PrecTy b c → PrecTy a c
  | _, _, _, .real, h => h
  | _, _, _, .bool, h => h
  | _, _, _, .unk, h => by cases h; exact .unk
  | _, _, _, .arrow hs1 hd1, h => by
      cases h with
      | arrow hs2 hd2 => exact .arrow (PrecTy.trans hs1 hs2) (PrecD.trans hd1 hd2)
      | unk => exact .unk
/-- Precision on formula distribution types is transitive. -/
theorem PrecD.trans : ∀ {A B C : FDist}, PrecD A B → PrecD B C → PrecD A C
  | _, _, _, .mk RAB fab gab hABty hAB habL habR, .mk RBC fbc gbc hBCty hBC hbcL hbcR =>
      .mk (Relation.Comp RAB RBC) (fun a => fbc (fab a)) (fun c => gab (gbc c))
        (fun a c ⟨b, hab, hbc⟩ => PrecTy.trans (hABty a b hab) (hBCty b c hbc))
        (hAB.trans hBC fun _ b _ hab hbc => ⟨b, hab, hbc⟩)
        (fun a => PrecTy.trans (habL a) (hbcL (fab a)))
        (fun c => PrecTy.trans (habR (gbc c)) (hbcR c))
end

/-! ## The top type `⌈{{?^?}}⌉` and `dom`/`cod` -/

/-- The lifting `⌈{{?^?}}⌉`: one entry of type `?` with probability `1`. It
is `cod(?)` and the greatest formula distribution type for precision. -/
@[reducible] def topF : FDist := .mk 1 (fun _ => .unk) (fun p => p 0 = 1)

/-- The closing formula of `topF` is `Good`. -/
theorem goodC_topF : Good topF := by
  refine ⟨⟨fun _ => 1, rfl⟩, ?_, ?_, ?_⟩
  · intro p hp i
    have : i = 0 := Subsingleton.elim i 0
    rw [this, show p 0 = 1 from hp]
    norm_num
  · intro p hp
    show (∑ i : Fin 1, p i) = 1
    rw [Fin.sum_univ_one]
    exact hp
  · intro p q hp hq t _ _
    show t * p 0 + (1 - t) * q 0 = 1
    rw [show p 0 = 1 from hp, show q 0 = 1 from hq]
    ring

/-- `topF` is a well-formed formula distribution type. -/
theorem goodD_topF : GoodD topF :=
  GoodD.mk goodC_topF (fun _ => GoodTy.unk)

/-- Every good formula type is below `topF`. -/
theorem prec_top {D : FDist} (h : Good D) : PrecD D topF := by
  refine PrecD.mk (fun _ _ => True) (fun _ => 0) (fun _ => ⟨0, h.pos⟩)
    (fun i j _ => PrecTy.unk) ?_ (fun _ => PrecTy.unk) (fun _ => PrecTy.unk)
  intro p hp
  exact ⟨fun _ => 1, rfl, fun i _ => p i, ⟨fun i _ => h.nonneg p hp i, fun i => by simp,
    fun j => by simpa using h.mass p hp⟩, fun _ _ _ => trivial⟩

/-- The partial functions `dom`/`cod` of Figure 6, as a relation:
`DomCod σ s D` means `dom(σ) = s` and `cod(σ) = D`, with `dom(?) = ?` and
`cod(?) = ⌈{{?^?}}⌉`. -/
inductive DomCod : FTy → FTy → FDist → Prop where
  | arrow : ∀ {s D}, DomCod (.arrow s D) s D
  | unk : DomCod .unk .unk topF

/-- Lemma 25 (monotonicity of the type operators), `dom`/`cod`: if `σ ⊑ σ'`
with `σ` well-formed and `dom(σ) = s`, `cod(σ) = D`, then `dom(σ') = s'` and
`cod(σ') = D'` with `s ⊑ s'` and `D ⊑ D'`. -/
theorem domcod_mono : ∀ {σ σ' s : FTy} {D : FDist}, σ ⊑ σ' → DomCod σ s D →
    GoodTy σ → ∃ s' D', DomCod σ' s' D' ∧ s ⊑ s' ∧ D ⊑ D'
  | _, _, _, _, .unk, .arrow, hg => by
      cases hg with
      | arrow _ hD => exact ⟨.unk, topF, .unk, .unk, prec_top hD.good⟩
  | _, _, _, _, .arrow hs hD, .arrow, _ => ⟨_, _, .arrow, hs, hD⟩
  | _, _, _, _, .unk, .unk, _ => ⟨.unk, topF, .unk, .unk, prec_top goodC_topF⟩

/-! ## Lemma 24 (consistency precision) -/

/- Lemma 24 (consistency precision), for consistency and precision on
formula types: replacing both sides by less precise types preserves consistency. -/
mutual
/-- Lemma 24 (consistency precision), simple types: if `σ₁ ∼ σ₂`,
`σ₁ ⊑ σ₁'` and `σ₂ ⊑ σ₂'`, then `σ₁' ∼ σ₂'`. -/
theorem cons_prec_ty : ∀ {σ1 σ2 σ1' σ2' : FTy},
    σ1 ∼ σ2 → σ1 ⊑ σ1' → σ2 ⊑ σ2' → σ1' ∼ σ2'
  | _, _, _, _, _, .unk, _ => .unkL
  | _, _, _, _, _, .real, .unk => .unkR
  | _, _, _, _, _, .bool, .unk => .unkR
  | _, _, _, _, _, .arrow _ _, .unk => .unkR
  | _, _, _, _, hc, .real, .real => hc
  | _, _, _, _, hc, .real, .bool => nomatch hc
  | _, _, _, _, hc, .real, .arrow _ _ => nomatch hc
  | _, _, _, _, hc, .bool, .bool => hc
  | _, _, _, _, hc, .bool, .real => nomatch hc
  | _, _, _, _, hc, .bool, .arrow _ _ => nomatch hc
  | _, _, _, _, hc, .arrow _ _, .real => nomatch hc
  | _, _, _, _, hc, .arrow _ _, .bool => nomatch hc
  | _, _, _, _, hc, .arrow hs1 hd1, .arrow hs2 hd2 => by
      cases hc with
      | arrow hcs hcd =>
        exact .arrow (cons_prec_ty hcs hs1 hs2) (cons_prec_d hcd hd1 hd2)
/-- Lemma 24 (consistency precision), distribution types: if `D₁ ∼ D₂`,
`D₁ ⊑ D₁'` and `D₂ ⊑ D₂'`, then `D₁' ∼ D₂'`. -/
theorem cons_prec_d : ∀ {D1 D2 D1' D2' : FDist},
    D1 ∼ D2 → D1 ⊑ D1' → D2 ⊑ D2' → D1' ∼ D2'
  | _, _, _, _, .mk R cL cR hR hl hcL hcR,
      .mk R1 f1L f1R hR1 hc1 hf1L hf1R, .mk R2 f2L f2R hR2 hc2 hf2L hf2R =>
      .mk (fun i' j' => ∃ i j, R1 i i' ∧ R i j ∧ R2 j j')
        (fun i' => f2L (cL (f1R i'))) (fun j' => f1L (cR (f2R j')))
        (fun i' j' ⟨i, j, h1, h, h2⟩ => cons_prec_ty (hR i j h) (hR1 i i' h1) (hR2 j j' h2))
        ((hl.comp_left hc1 (T := fun i' j => ∃ i, R1 i i' ∧ R i j)
            fun i _ _ h1 h => ⟨i, h1, h⟩).comp_right hc2
          fun _ j _ ⟨i, h1, h⟩ h2 => ⟨i, j, h1, h, h2⟩)
        (fun i' => cons_prec_ty (hcL (f1R i')) (hf1R i') (hf2L (cL (f1R i'))))
        (fun j' => cons_prec_ty (hcR (f2R j')) (hf1L (cR (f2R j'))) (hf2R j'))
end

/-! ## The probabilistic-choice operator -/

/-- The result type of a probabilistic choice with known probability `a`
(Figure 6): the entries of the two branch types are concatenated, and a solution
is `a · p` followed by `(1 − a) · q` for solutions `p`, `q` of the branches. The
branch solutions, which the article keeps as variables of the result formula, are
existentially quantified. -/
def chooseSem (a : ℝ) (D1 D2 : FDist) : FDist :=
  .mk (D1.n + D2.n) (Fin.append D1.ty D2.ty)
    (fun x => ∃ p q, D1.C p ∧ D2.C q ∧
      x = Fin.append (fun i => a * p i) (fun j => (1 - a) * q j))

/-- The result type of a probabilistic choice with unknown probability, and of
the conditional: the convex hull `D₁ ⊕_? D₂` of Figure 6, as `chooseSem` with
the probability `a ∈ [0,1]` existentially quantified. -/
def chooseSemU (D1 D2 : FDist) : FDist :=
  .mk (D1.n + D2.n) (Fin.append D1.ty D2.ty)
    (fun x => ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ ∃ p q, D1.C p ∧ D2.C q ∧
      x = Fin.append (fun i => a * p i) (fun j => (1 - a) * q j))

/-- The entry types of `chooseSem a D₁ D₂`. -/
@[simp] theorem chooseSem_ty (a : ℝ) (D1 D2 : FDist) :
    (chooseSem a D1 D2).ty = Fin.append D1.ty D2.ty := rfl

/-- The entry types of `chooseSemU D₁ D₂`. -/
@[simp] theorem chooseSemU_ty (D1 D2 : FDist) :
    (chooseSemU D1 D2).ty = Fin.append D1.ty D2.ty := rfl

/-- The cells of `D₁ ⊕_a D₂`: those of `D₁` followed by those of `D₂`. -/
@[simp] theorem chooseSem_n (a : ℝ) (D1 D2 : FDist) :
    (chooseSem a D1 D2).n = D1.n + D2.n := rfl

/-- The cells of `D₁ ⊕_? D₂`: those of `D₁` followed by those of `D₂`. -/
@[simp] theorem chooseSemU_n (D1 D2 : FDist) :
    (chooseSemU D1 D2).n = D1.n + D2.n := rfl

/-- A left cell of `D₁ ⊕_a D₂` carries the entry of `D₁`. -/
@[simp] theorem chooseSem_ty_castAdd (a : ℝ) (D1 D2 : FDist) (i : Fin D1.n) :
    (chooseSem a D1 D2).ty (Fin.castAdd D2.n i) = D1.ty i := Fin.append_left _ _ _

/-- A right cell of `D₁ ⊕_a D₂` carries the entry of `D₂`. -/
@[simp] theorem chooseSem_ty_natAdd (a : ℝ) (D1 D2 : FDist) (j : Fin D2.n) :
    (chooseSem a D1 D2).ty (Fin.natAdd D1.n j) = D2.ty j := Fin.append_right _ _ _

/-- A left cell of `D₁ ⊕_? D₂` carries the entry of `D₁`. -/
@[simp] theorem chooseSemU_ty_castAdd (D1 D2 : FDist) (i : Fin D1.n) :
    (chooseSemU D1 D2).ty (Fin.castAdd D2.n i) = D1.ty i := Fin.append_left _ _ _

/-- A right cell of `D₁ ⊕_? D₂` carries the entry of `D₂`. -/
@[simp] theorem chooseSemU_ty_natAdd (D1 D2 : FDist) (j : Fin D2.n) :
    (chooseSemU D1 D2).ty (Fin.natAdd D1.n j) = D2.ty j := Fin.append_right _ _ _

/-! ## Monotonicity of probabilistic choice -/

/-- Lemma 25 (monotonicity of the type operators), choice with a known
probability `a`: if `D₁ ⊑ D₁'` and `D₂ ⊑ D₂'`, then `D₁ ⊕_a D₂ ⊑ D₁' ⊕_a D₂'`. -/
theorem prec_choose {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {D1 D1' D2 D2' : FDist}
    (h1 : D1 ⊑ D1') (h2 : D2 ⊑ D2') :
    chooseSem a D1 D2 ⊑ chooseSem a D1' D2' := by
  refine PrecD.intro (cov_append h1.covL h2.covL)
    (cov_append (P := fun σ' σ => PrecTy σ σ') h1.covR h2.covR) ?_
  rintro x ⟨p, q, hp, hq, rfl⟩
  obtain ⟨p', hp', hl1⟩ := h1.coup p hp
  obtain ⟨q', hq', hl2⟩ := h2.coup q hq
  exact ⟨_, ⟨p', q', hp', hq', rfl⟩, (hl1.smul ha0).append (hl2.smul (sub_nonneg.2 ha1))
    (fun _ _ h => by simpa using h) (fun _ _ h => by simpa using h)⟩

/-- Lemma 25 (monotonicity of the type operators), choice when the probability
becomes `?` (`a ⊑ ?`): if `D₁ ⊑ D₁'` and `D₂ ⊑ D₂'`, then
`D₁ ⊕_a D₂ ⊑ D₁' ⊕_? D₂'`. -/
theorem prec_choose_unk {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {D1 D1' D2 D2' : FDist} (h1 : D1 ⊑ D1') (h2 : D2 ⊑ D2') :
    chooseSem a D1 D2 ⊑ chooseSemU D1' D2' := by
  refine PrecD.intro (cov_append h1.covL h2.covL)
    (cov_append (P := fun σ' σ => PrecTy σ σ') h1.covR h2.covR) ?_
  rintro x ⟨p, q, hp, hq, rfl⟩
  obtain ⟨p', hp', hl1⟩ := h1.coup p hp
  obtain ⟨q', hq', hl2⟩ := h2.coup q hq
  exact ⟨_, ⟨a, ha0, ha1, p', q', hp', hq', rfl⟩,
    (hl1.smul ha0).append (hl2.smul (sub_nonneg.2 ha1))
    (fun _ _ h => by simpa using h) (fun _ _ h => by simpa using h)⟩

/-- Lemma 25 (monotonicity of the type operators), choice with unknown
probabilities on both sides (`? ⊑ ?`), and the convex hull of the conditional:
if `D₁ ⊑ D₁'` and `D₂ ⊑ D₂'`, then `D₁ ⊕_? D₂ ⊑ D₁' ⊕_? D₂'`. -/
theorem prec_chooseU {D1 D1' D2 D2' : FDist}
    (h1 : D1 ⊑ D1') (h2 : D2 ⊑ D2') :
    chooseSemU D1 D2 ⊑ chooseSemU D1' D2' := by
  refine PrecD.intro (cov_append h1.covL h2.covL)
    (cov_append (P := fun σ' σ => PrecTy σ σ') h1.covR h2.covR) ?_
  rintro x ⟨aa, haa0, haa1, p, q, hp, hq, rfl⟩
  obtain ⟨p', hp', hl1⟩ := h1.coup p hp
  obtain ⟨q', hq', hl2⟩ := h2.coup q hq
  exact ⟨_, ⟨aa, haa0, haa1, p', q', hp', hq', rfl⟩,
    (hl1.smul haa0).append (hl2.smul (sub_nonneg.2 haa1))
    (fun _ _ h => by simpa using h) (fun _ _ h => by simpa using h)⟩

/-! ## The `let` operator -/

/-- The result type of the exhaustive `let` (Figure 6), the weighted union
`∑_i p_i · F_i`: the entries are the dependent concatenation of the entries of
the branch types `F i`, one per bound term entry, and a solution is
`x(i,k) = pᵢ · bᵢ(k)` for a solution `p` of the bound term and solutions `bᵢ` of
the branches, all existentially quantified. -/
@[reducible] noncomputable def letSem (D : FDist) (F : Fin D.n → FDist) : FDist :=
  .mk (∑ i, (F i).n)
    (fun k => (F (finSigmaFinEquiv.symm k).1).ty (finSigmaFinEquiv.symm k).2)
    (fun x => ∃ p, D.C p ∧ ∃ b : (i : Fin D.n) → Fin (F i).n → ℝ,
      (∀ i, (F i).C (b i)) ∧
      ∀ k, x k = p (finSigmaFinEquiv.symm k).1 * b _ (finSigmaFinEquiv.symm k).2)

/-- The cells of `letSem D F`: the cells of every `F i`, side by side. -/
@[simp] theorem letSem_n (D : FDist) (F : Fin D.n → FDist) :
    (letSem D F).n = ∑ i, (F i).n := rfl

/-! ## Singleton types -/

/-- The singleton type `[ω = 1] {{σ^ω}}` of Figure 6: one entry with
probability `1` (`topF` is `pointF .unk`). -/
@[reducible] def pointF (σ : FTy) : FDist := .mk 1 (fun _ => σ) (fun p => p 0 = 1)

/-- A singleton type has one cell. -/
@[simp] theorem pointF_n (σ : FTy) : (pointF σ).n = 1 := rfl

/-- The entry of a singleton type is its simple type. -/
@[simp] theorem pointF_ty (σ : FTy) (i : Fin (pointF σ).n) : (pointF σ).ty i = σ := rfl

/-- The solutions of a singleton type put probability `1` on its cell. -/
@[simp] theorem pointF_C (σ : FTy) (p : Fin (pointF σ).n → ℝ) :
    (pointF σ).C p ↔ p 0 = 1 := Iff.rfl

/-- The closing formula of a singleton type is `Good`. -/
theorem goodC_point (σ : FTy) : Good (pointF σ) := goodC_topF

/-- The singleton type of a well-formed simple type is well-formed. -/
theorem goodD_point {σ : FTy} (h : GoodTy σ) : GoodD (pointF σ) :=
  GoodD.mk (goodC_point σ) (fun _ => h)

/-- Lemma 25 (monotonicity of the type operators), singleton types: if
`σ ⊑ σ'`, then `[ω = 1] {{σ^ω}} ⊑ [ω = 1] {{σ'^ω}}`. -/
theorem prec_point {σ σ' : FTy} (h : σ ⊑ σ') :
    pointF σ ⊑ pointF σ' := by
  refine PrecD.intro (fun _ => ⟨0, h⟩) (fun _ => ⟨0, h⟩) ?_
  exact fun p hp => ⟨fun _ => 1, rfl, .point hp rfl h⟩

/-! ## Auxiliary accessors -/

/-- Entry types of a hereditarily good type are good. -/
theorem GoodD.tys {D : FDist} : GoodD D → ∀ i, GoodTy (D.ty i)
  | .mk _ h => h


/-! ## Finite convex mixing

`GoodC.convex` is binary; the `let` monotonicity and goodness proofs mix
finitely many solutions, so we extend it to finite convex combinations
(`convexC_sum`), to weighted sums of solutions (`convexC_wsum`,
`GoodC.exists_mix`) and to
mixtures of two *scaled* solutions (`GoodC.scaled_mix`, the common shape
`t·(α₁·p₁) + (1−t)·(α₂·p₂) = α·P`). -/

/-- Binary convexity extends to finite convex combinations. -/
theorem convexC_sum {n : ℕ} {C : (Fin n → ℝ) → Prop}
    (hconv : ∀ p q, C p → C q → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      C (fun i => t * p i + (1 - t) * q i)) :
    ∀ {m : ℕ} (w : Fin m → ℝ) (z : Fin m → Fin n → ℝ),
      (∀ k, 0 ≤ w k) → (∑ k, w k) = 1 → (∀ k, C (z k)) →
      C (fun i => ∑ k, w k * z k i) := by
  intro m
  induction m with
  | zero =>
    intro w z _ hsum _
    simp at hsum
  | succ m ih =>
    intro w z hw hsum hz
    rw [Fin.sum_univ_succ] at hsum
    by_cases h1 : w 0 = 1
    · have htail0 : ∑ k : Fin m, w (Fin.succ k) = 0 := by rw [h1] at hsum; linarith
      have htail : ∀ k : Fin m, w (Fin.succ k) = 0 := by
        intro k
        have hle : w (Fin.succ k) ≤ ∑ k : Fin m, w (Fin.succ k) :=
          Finset.single_le_sum (fun k _ => hw (Fin.succ k)) (Finset.mem_univ k)
        have := hw (Fin.succ k)
        linarith [hle.trans_eq htail0]
      have heq : (fun i => ∑ k, w k * z k i) = z 0 := by
        funext i
        rw [Fin.sum_univ_succ, h1]
        simp [htail]
      rw [heq]
      exact hz 0
    · have htnn : 0 ≤ ∑ k : Fin m, w (Fin.succ k) :=
        Finset.sum_nonneg (fun k _ => hw (Fin.succ k))
      have hw0le : w 0 ≤ 1 := by linarith
      have hpos : 0 < 1 - w 0 := by
        rcases lt_or_eq_of_le hw0le with h | h
        · linarith
        · exact absurd h h1
      have hsum' : ∑ k : Fin m, w (Fin.succ k) / (1 - w 0) = 1 := by
        rw [← Finset.sum_div, show ∑ k : Fin m, w (Fin.succ k) = 1 - w 0 by linarith]
        exact div_self hpos.ne'
      have htailC := ih (fun k => w (Fin.succ k) / (1 - w 0)) (fun k => z (Fin.succ k))
        (fun k => div_nonneg (hw _) hpos.le) hsum' (fun k => hz _)
      have hres := hconv (z 0) _ (hz 0) htailC (w 0) (hw 0) hw0le
      have heq : (fun i => ∑ k, w k * z k i) =
          (fun i => w 0 * z 0 i + (1 - w 0) * ∑ k : Fin m,
            (w (Fin.succ k) / (1 - w 0)) * z (Fin.succ k) i) := by
        funext i
        rw [Fin.sum_univ_succ, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_)
        field_simp
      rw [heq]
      exact hres

/-- A weighted sum of points of a convex set is its total weight times a point
`g`, which lies in the set when the total weight is positive. Only the points of
positive weight are required to lie in the set. -/
theorem convexC_wsum {n : ℕ} {C : (Fin n → ℝ) → Prop}
    (hconv : ∀ p q, C p → C q → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      C (fun i => t * p i + (1 - t) * q i))
    {m : ℕ} {u : Fin m → ℝ} {c : Fin m → Fin n → ℝ} (hu : ∀ k, 0 ≤ u k)
    (hc : ∀ k, 0 < u k → C (c k)) :
    ∃ g, (0 < ∑ k, u k → C g) ∧ ∀ l, ∑ k, u k * c k l = (∑ k, u k) * g l := by
  by_cases hpos : 0 < ∑ k, u k
  · -- the normalized weights are a convex combination of the points of positive weight
    obtain ⟨k₀, hk₀⟩ := exists_pos_of_sum_pos hpos
    refine ⟨_, fun _ => convexC_sum hconv (fun k => (∑ k, u k)⁻¹ * u k)
      (fun k => if 0 < u k then c k else c k₀)
      (fun k => mul_nonneg (inv_nonneg.2 hpos.le) (hu k))
      (by rw [← Finset.mul_sum, inv_mul_cancel₀ hpos.ne'])
      (fun k => by beta_reduce; split_ifs with h; exacts [hc k h, hc k₀ hk₀]), fun l => ?_⟩
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    beta_reduce
    by_cases h : 0 < u k
    · rw [if_pos h]; field_simp
    · rw [eq_zero_of_nonneg_of_not_pos (hu k) h]; simp
  · -- every weight is zero
    have h0 : ∑ k, u k = 0 :=
      eq_zero_of_nonneg_of_not_pos (Finset.sum_nonneg fun k _ => hu k) hpos
    refine ⟨fun _ => 0, fun h => absurd h hpos, fun l => ?_⟩
    rw [h0, zero_mul]
    exact Finset.sum_eq_zero fun k _ => by rw [entry_zero_of_sum_zero u hu k h0, zero_mul]

/-- A weighted sum of points of a nonempty convex set is its total weight times
a point of the set. Only the points of positive weight are required to lie in
the set. -/
theorem convexC_wsum_of_sat {n : ℕ} {C : (Fin n → ℝ) → Prop}
    (hconv : ∀ p q, C p → C q → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      C (fun i => t * p i + (1 - t) * q i)) (hsat : ∃ z, C z)
    {m : ℕ} {u : Fin m → ℝ} {c : Fin m → Fin n → ℝ} (hu : ∀ k, 0 ≤ u k)
    (hc : ∀ k, 0 < u k → C (c k)) :
    ∃ g, C g ∧ ∀ l, ∑ k, u k * c k l = (∑ k, u k) * g l := by
  obtain ⟨g, hg, he⟩ := convexC_wsum hconv hu hc
  by_cases hpos : 0 < ∑ k, u k
  · exact ⟨g, hg hpos, he⟩
  · obtain ⟨z, hz⟩ := hsat
    refine ⟨z, hz, fun l => ?_⟩
    rw [he l, eq_zero_of_nonneg_of_not_pos (Finset.sum_nonneg fun k _ => hu k) hpos,
      zero_mul, zero_mul]

/-- The two-point case of `convexC_wsum`: `α₁ · p₁ + α₂ · p₂ = (α₁ + α₂) · g`,
with `g` in the convex set when `α₁ + α₂` is positive. -/
theorem convexC_wsum₂ {n : ℕ} {C : (Fin n → ℝ) → Prop}
    (hconv : ∀ p q, C p → C q → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      C (fun i => t * p i + (1 - t) * q i))
    {α₁ α₂ : ℝ} {p₁ p₂ : Fin n → ℝ} (h₁ : 0 ≤ α₁) (h₂ : 0 ≤ α₂)
    (hp₁ : 0 < α₁ → C p₁) (hp₂ : 0 < α₂ → C p₂) :
    ∃ g, (0 < α₁ + α₂ → C g) ∧ ∀ l, α₁ * p₁ l + α₂ * p₂ l = (α₁ + α₂) * g l := by
  simpa [Fin.sum_univ_two] using convexC_wsum hconv (u := ![α₁, α₂]) (c := ![p₁, p₂])
    (Fin.forall_fin_two.2 ⟨h₁, h₂⟩) (Fin.forall_fin_two.2 ⟨hp₁, hp₂⟩)

/-- A weighted sum of solutions of a good constraint is its total weight times
a solution: their convex mixture when the total weight is positive, any
solution otherwise. -/
theorem GoodC.exists_mix {n : ℕ} {C : (Fin n → ℝ) → Prop} (hC : GoodC n C) {m : ℕ}
    {t : Fin m → ℝ} (ht : ∀ i, 0 ≤ t i) {c : Fin m → Fin n → ℝ} (hc : ∀ i, C (c i)) :
    ∃ cm, C cm ∧ ∀ l, ∑ i, t i * c i l = (∑ i, t i) * cm l :=
  convexC_wsum_of_sat hC.convex hC.sat ht fun i _ => hc i

/-- Mixing two *scaled* solutions: `t·(α₁·p₁) + (1−t)·(α₂·p₂) = α·P` with
`α = t·α₁ + (1−t)·α₂` and `P` a solution (`GoodC.exists_mix` with the two
weights `t·α₁` and `(1−t)·α₂`). The common step of the operator convexity
proofs. -/
theorem GoodC.scaled_mix {n : ℕ} {C : (Fin n → ℝ) → Prop} (hC : GoodC n C)
    {p₁ p₂ : Fin n → ℝ} (hp₁ : C p₁) (hp₂ : C p₂)
    {t α₁ α₂ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂) :
    ∃ P, C P ∧ ∀ k, t * (α₁ * p₁ k) + (1 - t) * (α₂ * p₂ k)
      = (t * α₁ + (1 - t) * α₂) * P k := by
  obtain ⟨P, hP, h⟩ := hC.exists_mix (t := ![t * α₁, (1 - t) * α₂]) (c := ![p₁, p₂])
    (fun i => by
      fin_cases i
      · exact mul_nonneg ht0 hα₁
      · exact mul_nonneg (sub_nonneg.2 ht1) hα₂)
    (fun i => by fin_cases i <;> assumption)
  refine ⟨P, hP, fun k => ?_⟩
  have hk := h k
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hk
  rw [← hk]; ring

/-! ## Preservation of well-formedness by the operators -/

/-- The choice operator (known probability) preserves well-formedness of the
closing formula. -/
theorem goodC_choose {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {D1 D2 : FDist}
    (h1 : Good D1) (h2 : Good D2) : Good (chooseSem a D1 D2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := h1.sat
    obtain ⟨q, hq⟩ := h2.sat
    exact ⟨_, p, q, hp, hq, rfl⟩
  · rintro x ⟨p, q, hp, hq, rfl⟩ κ
    induction κ using Fin.addCases with
    | left i =>
      simpa using mul_nonneg ha0 (h1.nonneg p hp i)
    | right j =>
      simpa using
        mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a) (h2.nonneg q hq j)
  · rintro x ⟨p, q, hp, hq, rfl⟩
    show (∑ κ : Fin (D1.n + D2.n),
      Fin.append (fun i => a * p i) (fun j => (1 - a) * q j) κ) = 1
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [← Finset.mul_sum, ← Finset.mul_sum, h1.mass p hp, h2.mass q hq]
    ring
  · rintro x x' ⟨p, q, hp, hq, rfl⟩ ⟨p', q', hp', hq', rfl⟩ t ht0 ht1
    refine ⟨fun i => t * p i + (1 - t) * p' i, fun j => t * q j + (1 - t) * q' j,
      h1.convex p p' hp hp' t ht0 ht1, h2.convex q q' hq hq' t ht0 ht1, ?_⟩
    funext κ
    induction κ using Fin.addCases with
    | left i => simp only [Fin.append_left]; ring
    | right j => simp only [Fin.append_right]; ring

/-- The choice operator (unknown probability) preserves well-formedness of the
closing formula: a solution of `D₁ ⊕_? D₂` is a solution of `D₁ ⊕_a D₂` for
some `a ∈ [0,1]`, and two of them mix by `GoodC.scaled_mix`. -/
theorem goodC_chooseU {D1 D2 : FDist} (h1 : Good D1) (h2 : Good D2) :
    Good (chooseSemU D1 D2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := h1.sat
    obtain ⟨q, hq⟩ := h2.sat
    exact ⟨_, 1, zero_le_one, le_refl 1, p, q, hp, hq, rfl⟩
  · rintro x ⟨a, ha0, ha1, hx⟩
    exact (goodC_choose ha0 ha1 h1 h2).nonneg x hx
  · rintro x ⟨a, ha0, ha1, hx⟩
    exact (goodC_choose ha0 ha1 h1 h2).mass x hx
  · rintro x x' ⟨a1, ha10, ha11, p, q, hp, hq, rfl⟩
      ⟨a2, ha20, ha21, p', q', hp', hq', rfl⟩ t ht0 ht1
    obtain ⟨P, hP, hPe⟩ := h1.scaled_mix (α₁ := a1) (α₂ := a2) hp hp' ht0 ht1 ha10 ha20
    obtain ⟨Q, hQ, hQe⟩ := h2.scaled_mix (α₁ := 1 - a1) (α₂ := 1 - a2) hq hq' ht0 ht1
      (by linarith) (by linarith)
    refine ⟨t * a1 + (1 - t) * a2,
      add_nonneg (mul_nonneg ht0 ha10) (mul_nonneg (by linarith) ha20),
      by nlinarith, P, Q, hP, hQ, ?_⟩
    funext κ
    induction κ using Fin.addCases with
    | left i =>
      simpa using hPe i
    | right j =>
      simp only [Fin.append_right]
      rw [show (1:ℝ) - (t * a1 + (1 - t) * a2)
        = t * (1 - a1) + (1 - t) * (1 - a2) by ring]
      exact hQe j


/-- The choice operator with a known probability `a ∈ [0,1]` preserves
well-formedness of formula distribution types. -/
theorem goodD_choose {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {D1 D2 : FDist}
    (h1 : GoodD D1) (h2 : GoodD D2) : GoodD (chooseSem a D1 D2) := by
  refine GoodD.mk (goodC_choose ha0 ha1 h1.good h2.good) ?_
  intro κ
  induction κ using Fin.addCases with
  | left i => simpa using h1.tys i
  | right j => simpa using h2.tys j

/-- The convex hull `D₁ ⊕_? D₂` of well-formed formula distribution types is
well-formed. -/
theorem goodD_chooseU {D1 D2 : FDist} (h1 : GoodD D1) (h2 : GoodD D2) :
    GoodD (chooseSemU D1 D2) := by
  refine GoodD.mk (goodC_chooseU h1.good h2.good) ?_
  intro κ
  induction κ using Fin.addCases with
  | left i => simpa using h1.tys i
  | right j => simpa using h2.tys j


/-- The entry types of a `let` result at a packed index. -/
theorem letSem_ty_mk {D : FDist} {F : Fin D.n → FDist} (i : Fin D.n)
    (k : Fin (F i).n) : (letSem D F).ty (finSigmaFinEquiv ⟨i, k⟩) = (F i).ty k := by
  simp only [letSem, FDist.ty]
  rw [Equiv.symm_apply_apply]

/-- The `let` operator preserves well-formedness of the closing formula. -/
theorem goodC_let {D : FDist} {F : Fin D.n → FDist}
    (hD : Good D) (hF : ∀ i, Good (F i)) : Good (letSem D F) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hD.sat
    choose b hb using fun i => (hF i).sat
    exact ⟨_, p, hp, b, hb, fun κ => rfl⟩
  · rintro x ⟨p, hp, b, hb, hx⟩ κ
    rw [hx κ]
    exact mul_nonneg (hD.nonneg p hp _) ((hF _).nonneg _ (hb _) _)
  · rintro x ⟨p, hp, b, hb, hx⟩
    rw [Finset.sum_congr rfl (fun κ _ => hx κ),
      sum_sigma_proj (fun i k => p i * b i k)]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
      rw [← Finset.mul_sum, (hF i).mass _ (hb i), mul_one])]
    exact hD.mass p hp
  · rintro x x' ⟨p, hp, b, hb, hx⟩ ⟨p', hp', b', hb', hx'⟩ t ht0 ht1
    have key : ∀ i, ∃ B, (F i).C B ∧ ∀ k,
        t * (p i * b i k) + (1 - t) * (p' i * b' i k)
          = (t * p i + (1 - t) * p' i) * B k :=
      fun i => (hF i).scaled_mix (hb i) (hb' i) ht0 ht1 (hD.nonneg p hp i) (hD.nonneg p' hp' i)
    choose B hBC hBe using key
    refine ⟨fun i => t * p i + (1 - t) * p' i,
      hD.convex p p' hp hp' t ht0 ht1, B, hBC, ?_⟩
    intro κ
    show t * x κ + (1 - t) * x' κ = _
    rw [hx κ, hx' κ]
    exact hBe _ _

/-- The `let` operator preserves well-formedness: if `D` and every branch type
`F i` are well-formed, then so is `∑_i p_i · F_i`. -/
theorem goodD_let {D : FDist} {F : Fin D.n → FDist}
    (hD : GoodD D) (hF : ∀ i, GoodD (F i)) : GoodD (letSem D F) :=
  GoodD.mk (goodC_let hD.good (fun i => (hF i).good)) (fun _ => (hF _).tys _)


/-! ## Monotonicity of `let` -/

/-- Lemma 25 (monotonicity of the type operators), `let`: if the bound term
types are related, every `PrecTy`-related pair of bound term entries has related
branch types (in the `let` case of the static gradual guarantee this is the
induction hypothesis together with typing determinism), and the closing
formulas of the right branch types are `Good`, then the `let` result types are
related.

The lifting is the product `Lift.sigmaFin` of the coupling `u` of the bound
term with the liftings of the branches, one for every pair of entries that `u`
relates. Its right weights are the `u`-weighted sums of the transported branch
solutions, which are `q j` times a solution of `F' j` (`GoodC.exists_mix`). -/
theorem prec_let {D D' : FDist} {F : Fin D.n → FDist} {F' : Fin D'.n → FDist}
    (hD : D ⊑ D')
    (hF : ∀ i j, D.ty i ⊑ D'.ty j → F i ⊑ F' j)
    (hG : ∀ j, Good (F' j)) :
    letSem D F ⊑ letSem D' F' := by
  obtain ⟨R, fL, fR, hR, hc, hfL, hfR⟩ := hD
  refine PrecD.intro
    (cov_sigmaFin (a := fun i => (F i).ty) (b := fun j => (F' j).ty) fL
      fun i => (hF _ _ (hfL i)).covL)
    (cov_sigmaFin (P := fun σ' σ => PrecTy σ σ') (a := fun j => (F' j).ty)
      (b := fun i => (F i).ty) fR fun j => (hF _ _ (hfR j)).covR) ?_
  rintro x ⟨p, hp, b, hb, hx⟩
  obtain rfl : x = _ := funext hx
  obtain ⟨q, hq, u, hu, hs⟩ := hc p hp
  -- the branch solution `b i` transported to a solution `c i j` of `F' j`, on
  -- every related pair of entries
  have key : ∀ i j, ∃ c, (F' j).C c ∧
      (R i j → Lift (fun k l => PrecTy ((F i).ty k) ((F' j).ty l)) (b i) c) := by
    intro i j
    by_cases hij : R i j
    · obtain ⟨c, hcC, hl⟩ := (hF i j (hR i j hij)).coup (b i) (hb i)
      exact ⟨c, hcC, fun _ => hl⟩
    · obtain ⟨c, hcC⟩ := (hG j).sat
      exact ⟨c, hcC, fun h => absurd h hij⟩
  choose c hcC hcl using key
  -- the solution of the block `j`: the `u`-weighted mixture of the `c i j`
  choose cm hcmC hcm using fun j =>
    (hG j).exists_mix (fun i => hu.nonneg i j) fun i => hcC i j
  have hq' : (fun κ' : Fin (∑ j, (F' j).n) => q (finSigmaFinEquiv.symm κ').1 *
        cm _ (finSigmaFinEquiv.symm κ').2)
      = fun κ' => ∑ i, u i (finSigmaFinEquiv.symm κ').1 * c i _ (finSigmaFinEquiv.symm κ').2 :=
    funext fun κ' => by rw [hcm, hu.col]
  refine ⟨_, ⟨q, hq, cm, hcmC, fun _ => rfl⟩, ?_⟩
  rw [hq']
  exact Lift.sigmaFin hu hs hcl fun i j k l _ h => by rw [letSem_ty_mk, letSem_ty_mk]; exact h

/-! ## Reflexivity of annotation consistency -/

mutual
/-- Annotation consistency (`ConsTy`, Definition 4) is reflexive on
well-formed types. -/
theorem ConsTy.refl : ∀ {t : FTy}, GoodTy t → ConsTy t t
  | _, .real => .real
  | _, .bool => .bool
  | _, .unk => .unkL
  | _, .arrow hs hD => .arrow (ConsTy.refl hs) (ConsD.refl hD)
/-- Annotation consistency (`ConsD`) is reflexive on well-formed distribution
types. -/
theorem ConsD.refl : ∀ {D : FDist}, GoodD D → ConsD D D
  | _, .mk hC hty => by
      obtain ⟨p, hp⟩ := hC.sat
      exact .mk (fun i j => i = j) id id (by rintro i j rfl; exact ConsTy.refl (hty i))
        (.refl hp (hC.nonneg p hp) fun _ => rfl)
        (fun i => ConsTy.refl (hty i)) (fun j => ConsTy.refl (hty j))
end

end GradualProb.GPLC

