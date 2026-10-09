import GradualProb.TPLC.Meet

/-!
# Reordering initial evidence

This module develops the metatheory of the reordering initial evidence `∥`
(Definition 11), defined in `TPLC/Definitions` as `reorderTy`/`reorderD`
together with its tagged form `tagReorderTy`/`tagReorderD`. Definedness of
`∥` is the reordering relation `=ʳ` of Definition 10 (`EReordTy`/`EReordD`),
and `∥` is a well-formed lower bound of its operands in runtime precision
(Lemma 10). Its tagged form is hereditarily valid, which certifies the
routing evidences of rules (Dlet) and (D::μ) (Lemma 40). Reordering implies
runtime consistency (Lemma 45), and a lower bound of the left operand of `∥`
is below `∥` when the left operand refines to the right one (Lemma 48). The
module also proves the properties of the refinement relation `RefTy`/`RefDist`
used by type safety and the dynamic gradual guarantee, and the backward
simple-type direction of Lemma 34.

## Main results

* `reord_reorderTy_isSome`, `reorderD_sat_iff_ereordD`: Lemma 10 (initial
  evidence for reordering), definedness.
* `eprec_reorderTy`, `eprec_reorderD` (for the operand that `π` picks),
  `goodD_reorderD`: Lemma 10, `∥` is a well-formed lower
  bound of both operands.
* `goodTy_reorderTy`, `hvtag_tagReorderTy`, `hvalid_tagReorderD`,
  `hvalidFor_tagReorderD`: Lemma 40 (validity of the routing evidence), item 1;
  `hvalidFor_dascD_evidence`: item 2.
* `econsTy_of_ereordTy`, `econsD_of_ereordD`: Lemma 45 (reordering
  consistency).
* `eprec_reorderD_glb`, `eprec_reorderD_glb_tags`: Lemma 48 (greatest lower
  bound of reordering).
* `cons_of_meetTy_good`: Lemma 34 (consistency is definedness), simple types,
  backward direction.

## Reading guide

`∥` is the witness construction `W_{id₌}` of `TPLC/Witness`, so its entry API
(the provenance tags `reorderDL`/`reorderDR`, the solutions of its formula,
definedness, well-formedness and reductivity at distribution types) is the
instance of the generic one at the carrier predicate `Eq`, exactly as the
meet's is at `EConsTy`; what this module proves is what recurses on the
simple-type operator `reorderTy`. The carrier and definedness come first, then
reductivity and well-formedness of `∥`. The tagged layer follows (hereditary
validity, validity of the routing evidences), then the lemmas that obtain the
definedness of `∥` from a single coupling or from refinement, the greatest
lower bound of `∥` (Lemma 48), and Lemma 45.
-/

namespace GradualProb.TPLC

open GradualProb.GPLC

open Classical

/-! ## The carrier of `∥`

The entries of `reorderD D1 D2` are indexed by an enumeration of the pairs of
equal operand entries (`liveK Eq`), the entries of the distribution clause of
Definition 11. `reorderCell` reads an entry as its pair and `reorderDL`/`reorderDR`
are the two components; the reading is injective and reaches every pair of
equal entries. All of it is the entry API of `TPLC/Witness` at `Eq`. -/

/-- The entries of `∥`, read as pairs of operand entries, are distinct. -/
theorem reorderCell_injective (D1 D2 : FDist) : Function.Injective (reorderCell D1 D2) :=
  witnessCell_injective Eq D1 D2

/-- Every pair of equal entries is an entry of `∥`. -/
theorem reorderCell_range {D1 D2 : FDist} {i : Fin D1.n} {j : Fin D2.n}
    (h : D1.ty i = D2.ty j) : (i, j) ∈ Set.range (reorderCell D1 D2) :=
  witnessCell_range h

/-- An entry of `reorderD` pairs equal operand entries. -/
theorem reorderD_cell_eq (D1 D2 : FDist) (c : Fin (reorderD D1 D2).n) :
    D1.ty (reorderDL D1 D2 c) = D2.ty (reorderDR D1 D2 c) :=
  witnessCell_prop Eq D1 D2 c

/-- The type of an entry of `∥` is the simple reordering evidence of the operand
entries named by its tags. -/
theorem reorderD_ty' (D1 D2 : FDist) (c : Fin (reorderD D1 D2).n) :
    (reorderD D1 D2).ty c
      = (reorderTy (D1.ty (reorderDL D1 D2 c)) (D2.ty (reorderDR D1 D2 c))).getD .unk := by
  cases D1; cases D2; rfl

/-- The solutions of the formula of `∥`, without the existential: a weight
vector on the entries solves it iff its push-forwards along the two tags solve the
operands and it is nonnegative. -/
theorem reorderD_C_iff (D1 D2 : FDist) (w : Fin (reorderD D1 D2).n → ℝ) :
    (reorderD D1 D2).C w ↔
      D1.C (pushfwd (reorderDL D1 D2) w) ∧ D2.C (pushfwd (reorderDR D1 D2) w) ∧ ∀ c, 0 ≤ w c :=
  witness_C_iff w

/-- The solutions of the formula of `∥` are nonnegative. -/
theorem reorderD_C_nonneg {D1 D2 : FDist} {w : Fin (reorderD D1 D2).n → ℝ}
    (hw : (reorderD D1 D2).C w) : ∀ c, 0 ≤ w c :=
  witness_C_nonneg hw

/-! ## Definedness of `∥` at simple types -/

/-- Equal well-formed types are related by reordering. The carrier of `∥` is
equality of entries; this bridges it to the structural relation the proofs
recurse on. -/
theorem ereordTy_of_eq {σ τ : FTy} (hg : GoodTy σ) (h : σ = τ) : EReordTy σ τ :=
  h ▸ EReordTy.refl hg

/-- `∥` is defined on every pair of equal simple types. -/
theorem reorderTy_self_isSome : ∀ (σ : FTy), (reorderTy σ σ).isSome
  | .real => rfl
  | .bool => rfl
  | .unk => rfl
  | .arrow s _ => by
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (reorderTy_self_isSome s)
      simp only [reorderTy, hm, Option.isSome_some]

/-- `∥` is defined on equal simple types (the form used at the entries of the
carrier). -/
theorem reorderTy_eq_isSome {σ τ : FTy} (h : σ = τ) : (reorderTy σ τ).isSome := by
  subst h; exact reorderTy_self_isSome σ

/-- Lemma 10 (initial evidence for reordering), definedness at simple types:
if `σ =ʳ τ` then `σ ∥ τ` is defined. The arrow case uses the symmetry of
`EReordTy`, since the relation is contravariant in domains and `∥` is
covariant. -/
theorem reord_reorderTy_isSome : ∀ {σ τ : FTy}, σ =ʳ τ → (σ ∥ τ).isSome
  | _, _, .real => rfl
  | _, _, .bool => rfl
  | _, _, .unk => rfl
  | _, _, .arrow hs _ => by
      obtain ⟨s, hs_eq⟩ := Option.isSome_iff_exists.mp
        (reord_reorderTy_isSome (EReordTy.symm hs))
      simp only [reorderTy, hs_eq, Option.isSome_some]

/-- An entry of `reorderD` pairs `=ʳ`-related operand entries, for a well-formed
left operand. -/
theorem reorderD_cell_live {D1 D2 : FDist} (hg1 : GoodD D1)
    (c : Fin (reorderD D1 D2).n) :
    EReordTy (D1.ty (reorderDL D1 D2 c)) (D2.ty (reorderDR D1 D2 c)) :=
  ereordTy_of_eq (hg1.tys _) (reorderD_cell_eq D1 D2 c)

/-- The type of an entry of `∥`, as a `some`: the simple reordering evidence of
the two equal entries the entry comes from is defined, and it is the type of
the entry. -/
theorem reorderD_ty_spec (D1 D2 : FDist) (c : Fin (reorderD D1 D2).n) :
    reorderTy (D1.ty (reorderDL D1 D2 c)) (D2.ty (reorderDR D1 D2 c))
      = some ((reorderD D1 D2).ty c) := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (reorderTy_eq_isSome (reorderD_cell_eq D1 D2 c))
  rw [reorderD_ty', hm, Option.getD_some]

/-! ## Definedness of `∥` at distribution types

`reorderD` is total; the definedness of `D1 ∥ D2` in the article is the
satisfiability of its formula, which is the lifting of the carrier predicate,
equality of entries, between the operands (`witness_sat_iff_symLift`), that
is, `D1 =ʳ D2`. -/

/-- A solution of the formula of `D1 ∥ D2` gives `D1 =ʳ D2`: its two
push-forwards are related by the lifting of equality of entries. -/
theorem ereordD_of_reorderD_sat {D1 D2 : FDist} {w : Fin (reorderD D1 D2).n → ℝ}
    (hw : (reorderD D1 D2).C w) : EReordD D1 D2 :=
  .mk (symLift_of_witness_sat hw)

/-- A coupling between solutions of the operands, supported on equal entries
and read through the provenance tags, is a solution of the formula of `∥`:
the restriction of the coupling to the carrier. -/
theorem reorderD_C_of_coupling {D1 D2 : FDist} {p : Fin D1.n → ℝ}
    {q : Fin D2.n → ℝ} {a : Fin D1.n → Fin D2.n → ℝ}
    (hp : D1.C p) (hq : D2.C q) (ha : IsCoupling p q a)
    (hs : Supp (fun i j => D1.ty i = D2.ty j) a) :
    (reorderD D1 D2).C (fun c => a (reorderDL D1 D2 c) (reorderDR D1 D2 c)) :=
  witness_C_of_coupling hp hq ha hs

/-- `D1 =ʳ D2` gives a solution of the formula of `D1 ∥ D2`: the restriction
of the coupling to the carrier. -/
theorem reorderD_sat_of_ereordD {D1 D2 : FDist} (h : EReordD D1 D2) :
    ∃ w, (reorderD D1 D2).C w :=
  witness_sat_of_symLift h.coup

/-- Lemma 10 (initial evidence for reordering), definedness at distribution
types: the formula of `D1 ∥ D2` is satisfiable iff `D1 =ʳ D2` (`EReordD`,
Definition 10). -/
theorem reorderD_sat_iff_ereordD {D1 D2 : FDist} :
    (∃ w, (D1 ∥ D2).C w) ↔ D1 =ʳ D2 :=
  ⟨fun ⟨_, hw⟩ => ereordD_of_reorderD_sat hw, reorderD_sat_of_ereordD⟩

/-! ## Reductivity of `∥` (Lemma 10)

`∥` is below both operands in runtime precision; the results are stated once
for the operand that `π` picks. At distribution types it is tag-guidedly
reductive (`TagPrec`) along the provenance tag `π` (`reorderDL` or `reorderDR`,
through `tagPrec_witness`, with the simple-type case at each entry),
and runtime precision follows by `eprecD_of_tagPrec`. Composed with Lemma 8 by
transitivity of runtime precision, this lets an evidence for a reordering
compose with an evidence for a consistency. -/

mutual
/-- Lemma 10 (initial evidence for reordering), simple types: `σ ∥ τ` is below
each of `σ` and `τ` (`π` picks the operand). -/
theorem eprec_reorderTy (π : Side) : ∀ {σ τ m : FTy}, GoodTy σ → GoodTy τ →
    σ =ʳ τ → σ ∥ τ = some m → m ⊑̇ π.pick σ τ
  | .real, .real, _, _, _, _, hm => by cases hm; rw [Side.pick_self]; exact .real
  | .bool, .bool, _, _, _, _, hm => by cases hm; rw [Side.pick_self]; exact .bool
  | .unk, .unk, _, _, _, _, hm => by cases hm; rw [Side.pick_self]; exact .unk
  | .real, .bool, _, _, _, _, hm | .real, .unk, _, _, _, _, hm
  | .real, .arrow _ _, _, _, _, _, hm | .bool, .real, _, _, _, _, hm
  | .bool, .unk, _, _, _, _, hm | .bool, .arrow _ _, _, _, _, _, hm
  | .unk, .real, _, _, _, _, hm | .unk, .bool, _, _, _, _, hm
  | .unk, .arrow _ _, _, _, _, _, hm | .arrow _ _, .real, _, _, _, _, hm
  | .arrow _ _, .bool, _, _, _, _, hm | .arrow _ _, .unk, _, _, _, _, hm => nomatch hm
  | .arrow s1 E1, .arrow s2 E2, m, hgσ, hgτ, hc, hm => by
      cases hgσ with
      | arrow hgs1 hgE1 =>
      cases hgτ with
      | arrow hgs2 hgE2 =>
      cases hc with
      | arrow hcs hcE =>
        cases hs : reorderTy s1 s2 with
        | none =>
            rw [reorderTy.eq_def] at hm
            simp only [hs] at hm
            exact (nomatch hm)
        | some s =>
            rw [reorderTy.eq_def] at hm
            simp only [hs, Option.some.injEq] at hm
            subst hm
            rw [Side.pick_app π FTy.arrow]
            exact .arrow (eprec_reorderTy π hgs1 hgs2 (EReordTy.symm hcs) hs)
              (eprecD_of_tagPrec (tagPrec_reorderD π hgE1 hgE2) fun _ => reorderD_C_nonneg)
  termination_by structural σ τ m hg1 hg2 hc hm => σ
/-- `∥` is tag-guidedly reductive into its operand `π` along the provenance
tag `π`: every entry of the carrier pairs equal entries, so its type is below
the entry of that operand, and the push-forward along the tag is a marginal clause
of the formula of `∥`. -/
theorem tagPrec_reorderD (π : Side) {D1 D2 : FDist} (hg1 : GoodD D1) (hg2 : GoodD D2) :
    TagPrec (reorderD D1 D2) (π.pick D1 D2) (witnessTag Eq D1 D2 π) :=
  match D1, D2, hg1, hg2 with
  | .mk _ _ _, .mk _ _ _, hg1, hg2 =>
      tagPrec_witness π fun c => by
        rw [witnessTag_ty]
        exact eprec_reorderTy π (hg1.tys _) (hg2.tys _) (reorderD_cell_live hg1 c)
          (reorderD_ty_spec _ _ c)
  termination_by structural D1
end

/-- Lemma 10 (initial evidence for reordering), distribution types: `D1 ∥ D2`
is below each of `D1` and `D2`. -/
theorem eprec_reorderD (π : Side) {D1 D2 : FDist} (hg1 : GoodD D1) (hg2 : GoodD D2) :
    D1 ∥ D2 ⊑̇ π.pick D1 D2 :=
  eprecD_of_tagPrec (tagPrec_reorderD π hg1 hg2) fun _ => reorderD_C_nonneg

/-! ## Well-formedness of `∥` -/

mutual
/-- Lemma 40 (validity of the routing evidence), item 1, simple types: `σ ∥ τ`
is well-formed when `σ`, `τ` are well-formed and `σ =ʳ τ`. -/
theorem goodTy_reorderTy : ∀ {σ τ m : FTy}, GoodTy σ → GoodTy τ → σ =ʳ τ →
    σ ∥ τ = some m → GoodTy m
  | _, _, m, _, _, .real, hm => by
      obtain rfl : FTy.real = m := Option.some.inj hm
      exact .real
  | _, _, m, _, _, .bool, hm => by
      obtain rfl : FTy.bool = m := Option.some.inj hm
      exact .bool
  | _, _, m, _, _, .unk, hm => by
      obtain rfl : FTy.unk = m := Option.some.inj hm
      exact .unk
  | _, _, m, hg1, hg2, .arrow hs hD, hm => by
      cases hg1 with
      | arrow hgs1 hgD1 =>
        cases hg2 with
        | arrow hgs2 hgD2 =>
          obtain ⟨sm, hsm⟩ := Option.isSome_iff_exists.mp
            (reord_reorderTy_isSome (EReordTy.symm hs))
          simp only [reorderTy, hsm, Option.some.injEq] at hm
          subst hm
          exact .arrow (goodTy_reorderTy hgs1 hgs2 (EReordTy.symm hs) hsm)
            (goodD_reorderD_sat hgD1 hgD2 (reorderD_sat_of_ereordD hD))
  termination_by structural σ τ m hg1 hg2 hr hm => σ
/-- `D1 ∥ D2` is well-formed when `D1`, `D2` are well-formed and its formula is
satisfiable. -/
theorem goodD_reorderD_sat : ∀ {D1 D2 : FDist}, GoodD D1 → GoodD D2 →
    (∃ w, (reorderD D1 D2).C w) → GoodD (reorderD D1 D2)
  | .mk _ _ _, .mk _ _ _, hg1, hg2, hsat =>
      goodD_witness_of_sat hg1.good hg2.good
        (fun c => goodTy_reorderTy (hg1.tys _) (hg2.tys _) (reorderD_cell_live hg1 c)
          (reorderD_ty_spec _ _ c))
        hsat
  termination_by structural D1 D2 hg1 hg2 hsat => D1
end

/-- Lemma 10 (initial evidence for reordering), well-formedness: `D1 ∥ D2` is
well-formed when `D1`, `D2` are well-formed and `D1 =ʳ D2`. -/
theorem goodD_reorderD {D1 D2 : FDist} (hg1 : GoodD D1) (hg2 : GoodD D2)
    (hR : D1 =ʳ D2) : GoodD (D1 ∥ D2) :=
  goodD_reorderD_sat hg1 hg2 (reorderD_sat_of_ereordD hR)

/-! ## Validity of the tagged `∥`

Along the provenance tags `∥` is tag-guidedly reductive into both operands
(`tagPrec_reorderD`). The tagged form `tagReorderD` is
hereditarily valid on both sides, which certifies the routing evidences
`μ′ ∥ μ` of rule (Dlet) and `(μ′ ∥ μ) ∘ ξ` of rule (D::μ). -/

mutual
/-- Erasing the tags of `tagReorderTy` gives `reorderTy`. -/
theorem tagReorderTy_toF : ∀ (t1 t2 : FTy),
    Option.map TagTy.toF (tagReorderTy t1 t2) = reorderTy t1 t2
  | .real, .real => rfl
  | .real, .bool => rfl
  | .real, .unk => rfl
  | .real, .arrow _ _ => rfl
  | .bool, .real => rfl
  | .bool, .bool => rfl
  | .bool, .unk => rfl
  | .bool, .arrow _ _ => rfl
  | .unk, .real => rfl
  | .unk, .bool => rfl
  | .unk, .unk => rfl
  | .unk, .arrow _ _ => rfl
  | .arrow _ _, .real => rfl
  | .arrow _ _, .bool => rfl
  | .arrow _ _, .unk => rfl
  | .arrow s1 d1, .arrow s2 d2 => by
      have hs := tagReorderTy_toF s1 s2
      have hd := tagReorderD_toF d1 d2
      cases hm : tagReorderTy s1 s2 with
      | none =>
          rw [hm] at hs
          simp only [tagReorderTy, reorderTy, hm, ← hs, Option.map_none]
      | some s =>
          rw [hm] at hs
          simp only [tagReorderTy, reorderTy, hm, ← hs, Option.map_some]
          show some (FTy.arrow s.toF (tagReorderD d1 d2).toF)
            = some (FTy.arrow s.toF (reorderD d1 d2))
          rw [hd]
/-- Erasing the tags of `tagReorderD` gives `reorderD`. -/
@[simp] theorem tagReorderD_toF : ∀ (D1 D2 : FDist),
    (tagReorderD D1 D2).toF = reorderD D1 D2
  | .mk n1 ty1 C1, .mk n2 ty2 C2 => by
      show witness Eq _ _ _ = witness Eq _ _ _
      congr 1
      funext c
      show ((tagReorderTy (ty1 _) (ty2 _)).getD .unk).toF = (reorderTy (ty1 _) (ty2 _)).getD .unk
      rw [toF_getD_unk, tagReorderTy_toF]
end

/-! ### The entries of the tagged `∥` -/

/-- The simple evidence of an entry of `tagReorderD D1 D2` is the tagged
reordering evidence of the operand entries named by its tags. -/
theorem tagReorderD_ty' (D1 D2 : FDist) (c : Fin (tagReorderD D1 D2).n) :
    (tagReorderD D1 D2).ty c
      = (tagReorderTy (D1.ty (reorderDL D1 D2 c)) (D2.ty (reorderDR D1 D2 c))).getD .unk := by
  cases D1; cases D2; rfl

/-- The simple evidence of an entry of `tagReorderD`, as a `some`. -/
theorem tagReorderD_ty_spec (D1 D2 : FDist) (c : Fin (tagReorderD D1 D2).n) :
    tagReorderTy (D1.ty (reorderDL D1 D2 c)) (D2.ty (reorderDR D1 D2 c))
      = some ((tagReorderD D1 D2).ty c) := by
  rw [tagReorderD_ty']
  exact some_getD_of_map_toF ((tagReorderTy_toF _ _).trans (reorderD_ty_spec D1 D2 c))

/-- The erasure of the simple evidence of an entry of `tagReorderD D1 D2` is the
type of the same entry of `reorderD D1 D2`. -/
theorem tagReorderD_ty_toF (D1 D2 : FDist) (c : Fin (tagReorderD D1 D2).n) :
    ((tagReorderD D1 D2).ty c).toF = (reorderD D1 D2).ty c := by
  rw [tagReorderD_ty', toF_getD_unk, tagReorderTy_toF, reorderD_ty']

/-! ### Hereditary validity of the tagged `∥` -/

mutual
/-- Lemma 40 (validity of the routing evidence), item 1, simple types: on
well-formed simple types related by reordering, the tagged `∥` is defined and
hereditarily valid on both sides. The arrow case uses symmetry for the
contravariant domains. -/
theorem hvtag_tagReorderTy : ∀ {σ1 σ2 : FTy}, GoodTy σ1 → GoodTy σ2 →
    σ1 =ʳ σ2 →
    ∃ e, σ1 ∥ᵗ σ2 = some e ∧ e ⊩[.l] σ1 ∧ e ⊩[.r] σ2
  | _, _, _, _, .real => ⟨.real, rfl, .real, .real⟩
  | _, _, _, _, .bool => ⟨.bool, rfl, .bool, .bool⟩
  | _, _, _, _, .unk => ⟨.unk, rfl, .unk, .unk⟩
  | _, _, hg1, hg2, .arrow hds hdD => by
      cases hg1 with
      | arrow hgs1 hgD1 =>
        cases hg2 with
        | arrow hgs2 hgD2 =>
          obtain ⟨es, hes, hL, hR⟩ :=
            hvtag_tagReorderTy hgs1 hgs2 (EReordTy.symm hds)
          refine ⟨.arrow es (tagReorderD _ _), ?_,
            .arrow hL (hvalid_tagReorderD hgD1 hgD2).1,
            .arrow hR (hvalid_tagReorderD hgD1 hgD2).2⟩
          simp only [tagReorderTy, hes]
          rfl
/-- Lemma 40 (validity of the routing evidence), item 1, distribution types: the
tagged `∥` of two well-formed distribution types is hereditarily valid on both
sides: every entry of the carrier pairs equal entries. -/
theorem hvalid_tagReorderD : ∀ {D1 D2 : FDist}, GoodD D1 → GoodD D2 →
    D1 ∥ᵗ D2 ⊩[.l] D1 ∧ D1 ∥ᵗ D2 ⊩[.r] D2
  | .mk _ _ _, .mk _ _ _, hg1, hg2 =>
      hvalid_tagWitness
        (tagPrec_of_eq (tagReorderD_toF _ _) (tagPrec_reorderD .l hg1 hg2))
        (tagPrec_of_eq (tagReorderD_toF _ _) (tagPrec_reorderD .r hg1 hg2))
        (fun c =>
          let ⟨_, he, hL, _⟩ :=
            hvtag_tagReorderTy (hg1.tys _) (hg2.tys _) (reorderD_cell_live hg1 c)
          (congrArg (HVTag .l · _)
            (Option.some.inj (he.symm.trans (tagReorderD_ty_spec _ _ c)))).mp hL)
        (fun c =>
          let ⟨_, he, _, hR⟩ :=
            hvtag_tagReorderTy (hg1.tys _) (hg2.tys _) (reorderD_cell_live hg1 c)
          (congrArg (HVTag .r · _)
            (Option.some.inj (he.symm.trans (tagReorderD_ty_spec _ _ c)))).mp hR)
end

/-! ### Validity of the routing evidences -/

/-- Lemma 40 (validity of the routing evidence), item 1: the routing evidence
`μ′ ∥ μ` of rule (Dlet) is hereditarily valid for `μ′ ∼̇ μ`. -/
theorem hvalidFor_tagReorderD {D1 D2 : FDist} (hg1 : GoodD D1) (hg2 : GoodD D2) :
    D1 ∥ᵗ D2 ⊩ D1 ∼̇ D2 :=
  ⟨(hvalid_tagReorderD hg1 hg2).1, (hvalid_tagReorderD hg1 hg2).2⟩

/-- The erasure of the tagged `∥` of well-formed types related by reordering
is well-formed. -/
theorem goodD_tagReorderD_toF {D1 D2 : FDist} (hg1 : GoodD D1) (hg2 : GoodD D2)
    (hd : EReordD D1 D2) : GoodD (tagReorderD D1 D2).toF := by
  rw [tagReorderD_toF]
  exact goodD_reorderD hg1 hg2 hd

/-- Lemma 40 (validity of the routing evidence), item 2: the routing evidence
`(μ′ ∥ μ) ∘ ξ` of rule (D::μ) is hereditarily valid for `μ′ ∼̇ μ₃` whenever
the term's evidence `ξ` is hereditarily right-valid for `μ₃`: the validity of
the tagged `∥` composed through the tagged meet (`hvalidFor_emeetD`). -/
theorem hvalidFor_dascD_evidence {D1 D2 D3 : FDist} {ξ : TagD}
    (hg1 : GoodD D1) (hg2 : GoodD D2) (hrd : D1 =ʳ D2)
    (hξ : ξ ⊩[.r] D3) (hgξ : GoodD ξ.toF) :
    (D1 ∥ᵗ D2) ∘ ξ ⊩ D1 ∼̇ D3 :=
  hvalidFor_emeetD (hvalidFor_tagReorderD hg1 hg2).1 hξ
    (goodD_tagReorderD_toF hg1 hg2 hrd) hgξ

/-! ## Definedness of `∥` from a coupling

Type safety and the dynamic gradual guarantee obtain the definedness of `∥`
from a single coupling supported on equal entries, as refinement
(`RefDist`) provides at each solution, and its well-formedness from that
satisfiability alone. -/

/-- A coupling between solutions of `D1` and `D2` supported on equal entries
gives a solution of the formula of `D1 ∥ D2`. -/
theorem reorderD_sat_of_coupling {D1 D2 : FDist} {p : Fin D1.n → ℝ} {q : Fin D2.n → ℝ}
    (hp : D1.C p) (hq : D2.C q) (h : Lift (fun i j => D1.ty i = D2.ty j) p q) :
    ∃ w', (reorderD D1 D2).C w' :=
  witness_sat_of_lift hp hq h

/-- The formula of the tagged `∥` is that of `∥`, so satisfiability
transfers directly. -/
theorem reorderD_sat_of_tagReorderD_sat {D1 D2 : FDist}
    (h : ∃ w, (tagReorderD D1 D2).toF.C w) : ∃ w, (reorderD D1 D2).C w := h

/-- The erasure of the tagged `∥` of well-formed types is well-formed when
the formula of `∥` is satisfiable. -/
theorem goodD_tagReorderD_sat {D1 D2 : FDist} (hg1 : GoodD D1) (hg2 : GoodD D2)
    (hsat : ∃ w, (reorderD D1 D2).C w) : GoodD (tagReorderD D1 D2).toF := by
  rw [tagReorderD_toF]
  exact goodD_reorderD_sat hg1 hg2 hsat

/-! ## Refinement

The refinement relation `RefTy`/`RefDist` is defined in `TPLC/Definitions`.
This section proves its reflexivity and that it gives the definedness of
`∥`. -/

mutual
/-- Refinement is reflexive on well-formed types: the diagonal coupling at
each solution. -/
theorem RefTy.refl : ∀ {σ : FTy}, GoodTy σ → RefTy σ σ
  | _, .real => .real
  | _, .bool => .bool
  | _, .unk => .unk
  | _, .arrow hs hD => .arrow (RefTy.refl hs) (RefDist.refl hD)
  termination_by structural σ hg => hg
/-- Refinement is reflexive on well-formed distribution types. -/
theorem RefDist.refl : ∀ {D : FDist}, GoodD D → RefDist D D
  | D, .mk hC hty => by
      exact RefDist.intro (.refl hC.nonneg fun _ => rfl)
  termination_by structural D hg => hg
end

/-- Refinement gives the definedness of `∥`: if `D1` has a solution, it is
coupled with a solution of `D2` on equal entries, and that coupling gives a
solution of the formula of `D1 ∥ D2`. -/
theorem reorderD_sat_of_refDist {D1 D2 : FDist}
    (hsat : ∃ p, D1.C p) (h : RefDist D1 D2) : ∃ w, (reorderD D1 D2).C w := by
  obtain ⟨p, hp⟩ := hsat
  obtain ⟨q, hq, hl⟩ := h.coup p hp
  exact reorderD_sat_of_coupling hp hq hl

/-! ## Greatest lower bound of `∥`

    X ⊑̇ P   and   RefDist P Q   ⟹   X ⊑̇ P ∥ Q

Lemma 48 (greatest lower bound of reordering), the counterpart of Lemma 8,
item 3, for `∥`, used by the dynamic gradual guarantee. The two couplings are
chained (`u : X → P` from precision, `v : P → Q` from refinement) with the
three-index weight of their composition through the solution `p` of `P`
(`glue₃`),

    T i a b  :=  u i a · v a b / p a ,

so that `∑_b T i a b = u i a` and `∑_i T i a b = v a b`. The restriction of
`v` to the carrier solves the formula of `∥` and the restriction of `T`
couples `x` with it (`witness_coupling_of_glue`, the same step as in the
greatest lower bound of the meet), and the support condition is the
simple-type statement. -/

/-- The coupling part of the greatest-lower-bound property of `∥`: the
coupling it produces sends each entry of `X` only to entries of `∥` whose left
tag (`reorderDL`) is related to it by the input coupling `R1`. The precision
of the entries is added in `eprec_reorderD_glb` and
`eprec_reorderD_glb_tags`. -/
theorem eprec_reorderD_glb_core : ∀ {X P Q : FDist}
    {R1 : Fin X.n → Fin P.n → Prop},
    SymLiftAll R1 X.C P.C → RefDist P Q →
    SymLiftAll (fun i c => R1 i (reorderDL P Q c)) X.C (reorderD P Q).C
  | _, P, Q, _, hc1, .mk hc2 => by
      intro x hx
      obtain ⟨p, hp, u, hu, hsu⟩ := hc1 x hx
      obtain ⟨q, hq, v, hv, hsv⟩ := hc2 p hp
      -- the restriction of `v` to the carrier solves the formula of `∥`, and
      -- the three-index weight, restricted to the carrier, couples `x` with it
      obtain ⟨w, hw, hc⟩ := witness_coupling_of_glue (ty := reorderDty P Q)
        (T := glue₃ p u v) hp hq hv hsv (glue₃_nonneg hu hv)
        (fun i => (Finset.sum_congr rfl fun a _ => sum_glue₃_right hu hv i a).trans (hu.row i))
        (sum_glue₃_left hu hv)
      exact ⟨w, hw, _, hc, fun i _ h => hsu i _ (glue₃_pos hu hv h).1⟩

mutual
/-- Greatest lower bound of `∥`, simple types: if `X ⊑̇ P` and `P` refines to
`Q`, then `X` is below `P ∥ Q`. -/
theorem eprec_reorderTy_glb : ∀ {X P Q m : FTy}, GoodTy P →
    EPrecTy X P → RefTy P Q → reorderTy P Q = some m → EPrecTy X m
  | _, _, _, _, _, h1, .real, hm => by
      simp only [reorderTy, Option.some.injEq] at hm
      exact hm ▸ h1
  | _, _, _, _, _, h1, .bool, hm => by
      simp only [reorderTy, Option.some.injEq] at hm
      exact hm ▸ h1
  | _, _, _, _, _, h1, .unk, hm => by
      simp only [reorderTy, Option.some.injEq] at hm
      exact hm ▸ h1
  | _, .arrow sP DP, .arrow sQ DQ, m, hg, h1, .arrow hs hD, hm => by
      cases hg with
      | arrow hgs hgD =>
        cases h1 with
        | arrow hs1 hD1 =>
          cases hms : reorderTy sP sQ with
          | none =>
              simp only [reorderTy, hms] at hm
              exact nomatch hm
          | some s =>
              simp only [reorderTy, hms, Option.some.injEq] at hm
              exact hm ▸ .arrow (eprec_reorderTy_glb hgs hs1 hs hms)
                (eprec_reorderD_glb hgD hD1 hD)
  termination_by structural X P Q m hg h1 h2 hm => P
/-- Lemma 48 (greatest lower bound of reordering): if `X ⊑̇ P` and `P` refines
to `Q`, then `X` is below `P ∥ Q`. -/
theorem eprec_reorderD_glb : ∀ {X P Q : FDist}, GoodD P →
    X ⊑̇ P → RefDist P Q → X ⊑̇ P ∥ Q
  | X, .mk nP tyP CP, .mk nQ tyQ CQ, hg, .mk R1 hR1 hc1, hQ =>
      .intro ((eprec_reorderD_glb_core hc1 hQ).mono fun i c hL =>
        eprec_reorderTy_glb (hg.tys _) (hR1 i _ hL)
          (by rw [← reorderD_cell_eq _ _ c]; exact RefTy.refl (hg.tys _))
          (reorderD_ty_spec _ _ c))
  termination_by structural X P Q hg h1 h2 => P
end

/-- Lemma 48 (greatest lower bound of reordering), tag-aware form of
`eprec_reorderD_glb`: the coupling it produces sends each entry of `X` only to
entries of `∥` whose left tag (`reorderDL`, the runtime operand) is related to it
by the input coupling `R1`. The routed cases of the dynamic gradual guarantee
instantiate `R1` with the relation between values given by the induction
hypothesis. -/
theorem eprec_reorderD_glb_tags : ∀ {X P Q : FDist}
    {R1 : Fin X.n → Fin P.n → Prop}, GoodD P →
    (∀ i a, R1 i a → X.ty i ⊑̇ P.ty a) →
    SymLiftAll R1 X.C P.C → RefDist P Q →
    SymLiftAll (fun i c => X.ty i ⊑̇ (P ∥ Q).ty c ∧ R1 i (reorderDL P Q c))
      X.C (P ∥ Q).C
  | X, .mk nP tyP CP, .mk nQ tyQ CQ, R1, hg, hR1, hc1, hQ =>
      (eprec_reorderD_glb_core hc1 hQ).mono fun i c hL =>
        ⟨eprec_reorderTy_glb (hg.tys _) (hR1 i _ hL)
          (by rw [← reorderD_cell_eq _ _ c]; exact RefTy.refl (hg.tys _))
          (reorderD_ty_spec _ _ c), hL⟩

/-! ## Reordering implies runtime consistency (Lemma 45)

On well-formed types, `∥` is a well-formed common lower bound of the two
types (Lemma 10), and a common lower bound witnesses runtime consistency
(`consTy_of_common_lb`/`consD_of_common_lb`, `TPLC/Meet`). -/

/-- Lemma 45 (reordering consistency), simple types: on well-formed types,
`σ =ʳ τ` implies `σ ∼̇ τ` in the runtime relation. -/
theorem econsTy_of_ereordTy {σ τ : FTy} (h1 : GoodTy σ) (h2 : GoodTy τ)
    (h : σ =ʳ τ) : σ ∼̇ τ := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (reord_reorderTy_isSome h)
  exact consTy_of_common_lb (goodTy_reorderTy h1 h2 h hm)
    (eprec_reorderTy .l h1 h2 h hm) (eprec_reorderTy .r h1 h2 h hm)

/-- Lemma 45 (reordering consistency), distribution types: on well-formed
types, `D1 =ʳ D2` implies `D1 ∼̇ D2` in the runtime relation. -/
theorem econsD_of_ereordD {D1 D2 : FDist} (h1 : GoodD D1) (h2 : GoodD D2)
    (h : D1 =ʳ D2) : D1 ∼̇ D2 :=
  consD_of_common_lb (goodD_reorderD h1 h2 h) (eprec_reorderD .l h1 h2)
    (eprec_reorderD .r h1 h2)

/-- Lemma 34 (consistency is definedness), simple types, backward direction:
if the meet of two well-formed types is defined (a `some` of a well-formed
type), the types are runtime-consistent. -/
theorem cons_of_meetTy_good {σ τ m : FTy} (h1 : GoodTy σ) (h2 : GoodTy τ)
    (hm : σ ⊓ τ = some m) (hg : GoodTy m) : σ ∼̇ τ :=
  consTy_of_common_lb hg (eprec_meetTy .l h1 h2 hm) (eprec_meetTy .r h1 h2 hm)

end GradualProb.TPLC
