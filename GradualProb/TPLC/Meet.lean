import GradualProb.TPLC.Definitions

/-!
# The meet operator and consistent transitivity

This module develops the metatheory of the meet `⊓` of TPLC (Section 5.2,
"Meet Operator"), defined in `TPLC/Definitions` as `meetTy`/`meetD` together
with its tagged form `emeetTy`/`emeetD`. Consistent transitivity `ε₁ ∘ ε₂` is
the meet of the two evidences. The module proves that definedness of the meet
is runtime consistency (Lemma 34), that the meet is the greatest lower bound
of its operands in runtime precision (Lemma 8) and is valid (Lemma 35), that
consistent transitivity builds evidence (Lemma 9) and preserves validity
(Lemma 37). The computation of Example 6 is checked in `TPLC/MeetExample`.

## Main results

* `meetD_sat_iff_econsD`: Lemma 34 (consistency is definedness), distribution
  types; the simple-type halves are `cons_meetTy_isSome` (`TPLC/Definitions`)
  and `cons_of_meetTy_good` (`TPLC/Reorder`).
* `eprec_meetTy`, `eprec_meetD`: Lemma 8 (reductivity of the meet
  operator), items 1 and 2, for the operand that `π` picks.
* `eprec_meetTy_glb`, `eprec_meetD_glb`: Lemma 8, item 3.
* `transTy_invariant`, `transD_invariant`: Lemma 9 (evidence from consistent
  transitivity).
* `hemeetTy_valid`, `hemeetD_valid` (along either tag), `hetransTy_invariant`,
  `hvalidFor_emeetD`: Lemma 37 (consistent transitivity preserves validity).
* `hvtag_tagMeetTy`, `goodTy_meetTy`, `hvalid_tagMeetD`, `goodD_meetD`:
  Lemma 35 (validity of the meet).
* `consTy_of_common_lb`, `consD_of_common_lb`: Lemma 8, item 3, definedness:
  a well-formed common lower bound witnesses runtime consistency.

## Reading guide

The meet is the witness construction `W_⊓` of `TPLC/Witness`, so its entry API
(the provenance tags `meetDL`/`meetDR`, the solutions of its formula,
definedness, well-formedness and reductivity at distribution types) is the
instance of the generic one at the carrier predicate `EConsTy`; what this
module proves is what recurses on the simple meet. The carrier and
definedness come first, then well-formedness, reductivity and Lemma 9. The
tagged layer follows: hereditary validity of the tagged meet, the per-entry
facts that rule (D::μ) consumes, and the tagged meet of two types
(`tagMeetTy`/`tagMeetD`) used by elaboration. The last sections are the
common-lower-bound lemmas and the greatest lower bound.
-/

namespace GradualProb.TPLC

open GradualProb.GPLC

open Classical

/-! ## The carrier of the meet

The entries of `meetD D1 D2` are indexed by an enumeration of the pairs of
operand entries that are runtime-consistent (`liveK EConsTy`). `meetCell` reads
an entry as its pair and `meetDL`/`meetDR` are the two components; the reading is
injective (`meetCell_injective`) and reaches every consistent pair
(`meetCell_range`). `sum_meetD_grid` moves sums between the carrier and the
full grid of pairs. All of it is the entry API of `TPLC/Witness` at `EConsTy`. -/

/-- The entries of the meet, read as pairs of operand entries, are distinct. -/
theorem meetCell_injective (D1 D2 : FDist) : Function.Injective (meetCell D1 D2) :=
  witnessCell_injective EConsTy D1 D2

/-- Every runtime-consistent pair of entries is an entry of the meet. -/
theorem meetCell_range {D1 D2 : FDist} {i : Fin D1.n} {j : Fin D2.n}
    (h : EConsTy (D1.ty i) (D2.ty j)) : (i, j) ∈ Set.range (meetCell D1 D2) :=
  witnessCell_range h

/-- Every runtime-consistent pair of entries is an entry of the meet, through its
tags. -/
theorem meetD_cell_exists {D1 D2 : FDist} {i : Fin D1.n} {j : Fin D2.n}
    (h : EConsTy (D1.ty i) (D2.ty j)) :
    ∃ c, meetDL D1 D2 c = i ∧ meetDR D1 D2 c = j :=
  witness_cell_exists h

/-- An entry of the meet is determined by its two tags. -/
theorem meetD_cell_unique {D1 D2 : FDist} {c c' : Fin (meetD D1 D2).n}
    (h1 : meetDL D1 D2 c = meetDL D1 D2 c') (h2 : meetDR D1 D2 c = meetDR D1 D2 c') :
    c = c' :=
  witness_cell_unique h1 h2

/-- A sum over the carrier of the meet of a grid function that vanishes on
inconsistent pairs is the full double grid sum. -/
theorem sum_meetD_grid {D1 D2 : FDist} (G : Fin D1.n → Fin D2.n → ℝ)
    (hdead : ∀ i j, ¬ EConsTy (D1.ty i) (D2.ty j) → G i j = 0) :
    (∑ c, G (meetDL D1 D2 c) (meetDR D1 D2 c)) = ∑ i, ∑ j, G i j :=
  sum_witness_grid G hdead

/-- The type of an entry of the meet, as a `some`: the simple meet of the two
operand entries the entry comes from is defined, and it is the type of the
entry. -/
theorem meetD_ty_spec (D1 D2 : FDist) (c : Fin (meetD D1 D2).n) :
    meetTy (D1.ty (meetDL D1 D2 c)) (D2.ty (meetDR D1 D2 c)) = some ((meetD D1 D2).ty c) := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (cons_meetTy_isSome (meetCell_cons D1 D2 c))
  rw [meetD_ty', hm, Option.getD_some]

/-- The solutions of the meet's formula, without the existential: a weight
vector on the entries solves it iff its push-forwards along the two tags solve the operands
and it is nonnegative. -/
theorem meetD_C_iff (D1 D2 : FDist) (w : Fin (meetD D1 D2).n → ℝ) :
    (meetD D1 D2).C w ↔
      D1.C (pushfwd (meetDL D1 D2) w) ∧ D2.C (pushfwd (meetDR D1 D2) w) ∧ ∀ c, 0 ≤ w c :=
  witness_C_iff w

/-- The solutions of the meet's formula are nonnegative. -/
theorem meetD_C_nonneg {D1 D2 : FDist} {w : Fin (meetD D1 D2).n → ℝ}
    (hw : (meetD D1 D2).C w) : ∀ c, 0 ≤ w c :=
  witness_C_nonneg hw

/-! ## Definedness of the distribution meet is runtime consistency

`meetD` is total; the definedness of `D1 ⊓ D2` in the article is the
satisfiability of its formula, which is the lifting of the carrier predicate
`EConsTy` between the operands (`witness_sat_iff_symLift`), that is, runtime
consistency `EConsD` (Figure 12). -/

/-- A solution of the meet's formula gives runtime consistency of the
operands: its two push-forwards are related by the lifting of `EConsTy`. -/
theorem econsD_of_meetD_sat {D1 D2 : FDist} {w : Fin (meetD D1 D2).n → ℝ}
    (hw : (meetD D1 D2).C w) : EConsD D1 D2 :=
  .intro (symLift_of_witness_sat hw)

/-- A coupling between solutions of the operands, supported on consistent
pairs and read through the provenance tags, is a solution of the meet's
formula: the restriction of the coupling to the carrier. -/
theorem meetD_C_of_coupling {D1 D2 : FDist} {p : Fin D1.n → ℝ}
    {qs : Fin D2.n → ℝ} {a : Fin D1.n → Fin D2.n → ℝ}
    (hp : D1.C p) (hq : D2.C qs) (ha : IsCoupling p qs a)
    (hs : Supp (fun i j => EConsTy (D1.ty i) (D2.ty j)) a) :
    (meetD D1 D2).C (fun c => a (meetDL D1 D2 c) (meetDR D1 D2 c)) :=
  witness_C_of_coupling hp hq ha hs

/-- Runtime consistency gives a solution of the meet's formula: the
restriction of the consistency coupling to the carrier. -/
theorem meetD_sat_of_econsD {D1 D2 : FDist} (h : EConsD D1 D2) :
    ∃ w, (meetD D1 D2).C w :=
  witness_sat_of_symLift h.coup

/-- Lemma 34 (consistency is definedness), distribution types: the formula of
`D1 ⊓ D2` is satisfiable iff `D1` and `D2` are runtime-consistent
(`EConsD`). -/
theorem meetD_sat_iff_econsD {D1 D2 : FDist} :
    (∃ w, (D1 ⊓ D2).C w) ↔ D1 ∼̇ D2 :=
  ⟨fun ⟨_, hw⟩ => econsD_of_meetD_sat hw, meetD_sat_of_econsD⟩

/-! ## Well-formedness of the meet

The meet of well-formed, runtime-consistent operands is well-formed
(`GoodTy`/`GoodD`). The satisfiability clause is `meetD_sat_of_econsD`, the
other clauses on the formula are those of the witness construction
(`goodD_witness_of_sat`), and every entry of the carrier is a consistent pair
(`meetCell_cons`), so the entries recurse directly. -/

mutual
/-- Lemma 35 (validity of the meet), simple types: the simple meet of
well-formed, runtime-consistent types is well-formed. -/
theorem goodTy_meetTy : ∀ {σ τ m : FTy}, GoodTy σ → GoodTy τ → σ ∼̇ τ →
    σ ⊓ τ = some m → GoodTy m
  | _, _, m, _, _, .real, hm => by
      obtain rfl : FTy.real = m := Option.some.inj hm
      exact .real
  | _, _, m, _, _, .bool, hm => by
      obtain rfl : FTy.bool = m := Option.some.inj hm
      exact .bool
  | _, τ, m, _, hg2, .unkL, hm => by
      obtain rfl : τ = m := Option.some.inj hm
      exact hg2
  | σ, _, m, hg1, _, .unkR, hm => by
      rw [meetTy_unk_right] at hm
      obtain rfl : σ = m := Option.some.inj hm
      exact hg1
  | _, _, m, hg1, hg2, .arrow hs hD, hm => by
      cases hg1 with
      | arrow hgs1 hgD1 =>
        cases hg2 with
        | arrow hgs2 hgD2 =>
          obtain ⟨sm, hsm⟩ := Option.isSome_iff_exists.mp (cons_meetTy_isSome hs)
          simp only [meetTy, hsm, Option.some.injEq] at hm
          subst hm
          exact .arrow (goodTy_meetTy hgs1 hgs2 hs hsm)
            (goodD_meetD_sat hgD1 hgD2 (meetD_sat_of_econsD hD))
  termination_by structural σ τ m hg1 hg2 hc hm => σ
/-- The distribution meet of well-formed operands is well-formed as soon as its
formula is satisfiable, since the carrier already consists of consistent
pairs. -/
theorem goodD_meetD_sat : ∀ {D1 D2 : FDist}, GoodD D1 → GoodD D2 →
    (∃ w, (meetD D1 D2).C w) → GoodD (meetD D1 D2)
  | .mk _ _ _, .mk _ _ _, hg1, hg2, hsat =>
      goodD_witness_of_sat hg1.good hg2.good
        (fun c => goodTy_meetTy (hg1.tys _) (hg2.tys _) (meetCell_cons _ _ c) (meetD_ty_spec _ _ c))
        hsat
  termination_by structural D1 D2 hg1 hg2 hsat => D1
end

/-- Lemma 35 (validity of the meet), distribution types: the distribution meet
of well-formed, runtime-consistent types is well-formed. -/
theorem goodD_meetD {D1 D2 : FDist} (hg1 : GoodD D1) (hg2 : GoodD D2)
    (hM : D1 ∼̇ D2) : GoodD (D1 ⊓ D2) :=
  goodD_meetD_sat hg1 hg2 (meetD_sat_of_econsD hM)

/-! ## Reductivity of the meet (Lemma 8, items 1 and 2)

The meet is below both operands in runtime precision (`EPrecTy`/`EPrecD`,
Figure 12); the results are stated once for the operand that `π` picks. At
distribution types the meet is tag-guidedly reductive (`TagPrec`) into the
operand `π` along the provenance tag `π` (`meetDL` or `meetDR`, through
`tagPrec_witness`): each entry is below the operand entry its tag names, by the
simple-type case, and the push-forward clause is a marginal clause of the
meet's formula. Runtime
precision follows by `eprecD_of_tagPrec`. No consistency hypothesis is needed:
the pointwise clause only needs the consistency of the pair of each entry, which
holds on the carrier. -/

mutual
/-- Lemma 8 (reductivity of the meet operator), item 1: the
simple meet is below each of its operands (`π` picks the operand). -/
theorem eprec_meetTy (π : Side) : ∀ {σ τ m : FTy}, GoodTy σ → GoodTy τ →
    σ ⊓ τ = some m → m ⊑̇ π.pick σ τ
  | .real, .real, _, _, _, hm => by cases hm; rw [Side.pick_self]; exact .real
  | .bool, .bool, _, _, _, hm => by cases hm; rw [Side.pick_self]; exact .bool
  | .unk, _, _, _, hgτ, hm => by cases hm; cases π; exacts [.unk, EPrecTy.refl hgτ]
  | .real, .unk, _, _, _, hm => by cases hm; cases π; exacts [.real, .unk]
  | .bool, .unk, _, _, _, hm => by cases hm; cases π; exacts [.bool, .unk]
  | .arrow _ _, .unk, _, hgσ, _, hm => by
      rw [meetTy_unk_right] at hm
      cases hm; cases π; exacts [EPrecTy.refl hgσ, .unk]
  | .real, .bool, _, _, _, hm | .real, .arrow _ _, _, _, _, hm
  | .bool, .real, _, _, _, hm | .bool, .arrow _ _, _, _, _, hm
  | .arrow _ _, .real, _, _, _, hm | .arrow _ _, .bool, _, _, _, hm => nomatch hm
  | .arrow s1 E1, .arrow s2 E2, m, hgσ, hgτ, hm => by
      cases hgσ with
      | arrow hgs1 hgE1 =>
      cases hgτ with
      | arrow hgs2 hgE2 =>
        cases hs : meetTy s1 s2 with
        | none =>
            rw [meetTy_arrow, hs] at hm
            exact (nomatch hm)
        | some s =>
            rw [meetTy_arrow, hs] at hm
            simp only [Option.map_some, Option.some.injEq] at hm
            subst hm
            rw [Side.pick_app π FTy.arrow]
            exact .arrow (eprec_meetTy π hgs1 hgs2 hs)
              (eprecD_of_tagPrec (tagPrec_meetD π hgE1 hgE2) fun _ => meetD_C_nonneg)
  termination_by structural σ τ m hg1 hg2 hm => σ
/-- The meet is tag-guidedly reductive into its operand `π` along the
provenance tag `π`: every entry of the carrier is a consistent pair, so its type
is below the entry of that operand, and the push-forward along the tag is a marginal
clause of the meet's formula. -/
theorem tagPrec_meetD (π : Side) {D1 D2 : FDist} (hg1 : GoodD D1) (hg2 : GoodD D2) :
    TagPrec (meetD D1 D2) (π.pick D1 D2) (witnessTag EConsTy D1 D2 π) :=
  match D1, D2, hg1, hg2 with
  | .mk _ _ _, .mk _ _ _, hg1, hg2 =>
      tagPrec_witness π fun c => by
        rw [witnessTag_ty]
        exact eprec_meetTy π (hg1.tys _) (hg2.tys _) (meetD_ty_spec _ _ c)
  termination_by structural D1
end

/-- Lemma 8 (reductivity of the meet operator), item 2: the
distribution meet is below each of its operands. -/
theorem eprec_meetD (π : Side) {D1 D2 : FDist} (hg1 : GoodD D1) (hg2 : GoodD D2) :
    D1 ⊓ D2 ⊑̇ π.pick D1 D2 :=
  eprecD_of_tagPrec (tagPrec_meetD π hg1 hg2) fun _ => meetD_C_nonneg

/-! ## Evidence from consistent transitivity (Lemma 9)

`ε₁ ∘ ε₂` is the meet `ε₁ ⊓ ε₂`, defined exactly on runtime-consistent
evidences (Lemma 34). It is below both operands (Lemma 8), hence, by
transitivity of runtime precision, evidence for the composed judgment, and it
is well-formed. -/

/-- Lemma 9 (evidence from consistent transitivity), simple types. The
definedness of `ε1 ∘ ε2` is stated as the runtime consistency `EConsTy ε1 ε2`
(Lemma 34); the conclusion also records that the composition is
well-formed. -/
theorem transTy_invariant {ε1 ε2 σ1 σ' σ2 : FTy}
    (h1 : ε1 ⊢ σ1 ∼̇ σ') (h2 : ε2 ⊢ σ' ∼̇ σ2)
    (hg1 : GoodTy ε1) (hg2 : GoodTy ε2) (hc : ε1 ∼̇ ε2) :
    ∃ ε3, ε1 ⊓ ε2 = some ε3 ∧ ε3 ⊢ σ1 ∼̇ σ2 ∧ GoodTy ε3 := by
  obtain ⟨ε3, hm⟩ := Option.isSome_iff_exists.mp (cons_meetTy_isSome hc)
  exact ⟨ε3, hm,
    ⟨EPrecTy.trans (eprec_meetTy .l hg1 hg2 hm) h1.1,
     EPrecTy.trans (eprec_meetTy .r hg1 hg2 hm) h2.2⟩,
    goodTy_meetTy hg1 hg2 hc hm⟩

/-- Lemma 9 (evidence from consistent transitivity), distribution types. The
definedness of `ε1 ∘ ε2` (satisfiability of its formula) is stated as the
runtime consistency `EConsD ε1 ε2` (Lemma 34); the conclusion also records
that the composition is well-formed. -/
theorem transD_invariant {ε1 ε2 D1 D' D2 : FDist}
    (h1 : ε1 ⊢ D1 ∼̇ D') (h2 : ε2 ⊢ D' ∼̇ D2)
    (hg1 : GoodD ε1) (hg2 : GoodD ε2) (hc : ε1 ∼̇ ε2) :
    ε1 ⊓ ε2 ⊢ D1 ∼̇ D2 ∧ GoodD (ε1 ⊓ ε2) :=
  ⟨⟨EPrecD.trans (eprec_meetD .l hg1 hg2) h1.1,
    EPrecD.trans (eprec_meetD .r hg1 hg2) h2.2⟩,
   goodD_meetD hg1 hg2 hc⟩

/-- The erasure of a defined tagged meet of well-formed, runtime-consistent
evidences is well-formed. -/
theorem goodTy_emeetTy_some {e1 e2 e3 : TagTy} (hg1 : GoodTy e1.toF)
    (hg2 : GoodTy e2.toF) (hc : EConsTy e1.toF e2.toF)
    (hm : emeetTy e1 e2 = some e3) : GoodTy e3.toF :=
  goodTy_meetTy hg1 hg2 hc (emeetTy_toF_some hm)

/-! ## Validity of the tagged meet

Along the provenance tags the meet is tag-guidedly reductive into each
operand (`tagPrec_meetD`), and hereditary validity
(`HVTag π`/`HValid π`) survives the tagged meet
`emeetTy`/`emeetD`. The typing of composed evidence in the reduction rules
consumes these facts. -/

/-! ### The entries of the tagged meet -/

/-- The simple evidence of an entry of `e1 ∘ e2` is the tagged meet of the
operand entries that its provenance names (`?` where the meet is undefined). -/
theorem emeetD_ty' (e1 e2 : TagD) (c : Fin (emeetD e1 e2).n) :
    (emeetD e1 e2).ty c
      = (emeetTy (e1.ty (meetDL e1.toF e2.toF c)) (e2.ty (meetDR e1.toF e2.toF c))).getD .unk := by
  cases e1; cases e2; rfl

/-- The simple evidence of an entry of `e1 ∘ e2`, as a `some`: every entry of
the carrier is a consistent pair, so the tagged meet of the entries its tags name
is defined, and it is that simple evidence. -/
theorem emeetD_ty_spec (e1 e2 : TagD) (c : Fin (emeetD e1 e2).n) :
    emeetTy (e1.ty (meetDL e1.toF e2.toF c)) (e2.ty (meetDR e1.toF e2.toF c))
      = some ((emeetD e1 e2).ty c) := by
  have h := meetD_ty_spec e1.toF e2.toF c
  rw [tagD_toF_ty, tagD_toF_ty] at h
  rw [emeetD_ty']
  exact some_getD_of_map_toF ((emeetTy_toF _ _).trans h)

/-- The erasure of the simple evidence of an entry of `e1 ∘ e2` is the type of
the same entry of the meet of the erasures (the two have the same number of
entries, definitionally). -/
theorem emeetD_ty_toF (e1 e2 : TagD) (c : Fin (emeetD e1 e2).n) :
    ((emeetD e1 e2).ty c).toF = (meetD e1.toF e2.toF).ty c := by
  rw [emeetD_ty', toF_getD_unk, emeetTy_toF, meetD_ty', tagD_toF_ty, tagD_toF_ty]

/-! ### The tagged meet along one tag

The tags `π` of `e1 ∘ e2` are those of its operand on the side `π`: the left
tags come from `e1` and the right tags from `e2`. The results that follow one
tag are stated once for `π`, with `a` the operand whose tags the meet keeps
and `b` the other operand, so that the meet is
`emeetTy (π.pick a b) (π.pick b a)`. -/

/-- A defined meet of `Real` with any evidence is `Real`. -/
theorem emeetTy_pick_real {π : Side} {b m : TagTy}
    (hm : emeetTy (π.pick .real b) (π.pick b .real) = some m) : m = .real := by
  cases π <;> cases b <;> simp [Side.pick, emeetTy] at hm <;> exact hm.symm

/-- A defined meet of `Bool` with any evidence is `Bool`. -/
theorem emeetTy_pick_bool {π : Side} {b m : TagTy}
    (hm : emeetTy (π.pick .bool b) (π.pick b .bool) = some m) : m = .bool := by
  cases π <;> cases b <;> simp [Side.pick, emeetTy] at hm <;> exact hm.symm

/-- A defined meet of an arrow `s → d` with an evidence `b`: either `b` is `?`
and the meet is `s → d`, or `b` is an arrow and the meet is the arrow of the
meets of the domains and of the codomains, in the same order. -/
theorem emeetTy_pick_arrow {π : Side} {s b m : TagTy} {d : TagD}
    (hm : emeetTy (π.pick (.arrow s d) b) (π.pick b (.arrow s d)) = some m) :
    (b = .unk ∧ m = .arrow s d) ∨
      ∃ s0 d0 s3, b = .arrow s0 d0 ∧ emeetTy (π.pick s s0) (π.pick s0 s) = some s3 ∧
        m = .arrow s3 (emeetD (π.pick d d0) (π.pick d0 d)) := by
  cases π <;> cases b with
  | real | bool => simp [Side.pick, emeetTy] at hm
  | unk => exact .inl ⟨rfl, by simp [Side.pick, emeetTy] at hm; exact hm.symm⟩
  | arrow s0 d0 =>
      refine .inr ⟨s0, d0, ?_⟩
      simp only [Side.pick, emeetTy] at hm
      split at hm
      · exact ⟨_, rfl, ‹_›, (Option.some.inj hm).symm⟩
      · exact nomatch hm

/-- The index, in the operand `a`, of an entry of the meet that keeps the tags
`π` of `a` (`meetDL` or `meetDR`). -/
noncomputable def emeetDTag :
    (π : Side) → (a b : TagD) → Fin (emeetD (π.pick a b) (π.pick b a)).n → Fin a.n
  | .l, a, b => meetDL a.toF b.toF
  | .r, a, b => meetDR b.toF a.toF

/-- The index, in the other operand `b`, of an entry of the meet that keeps the
tags `π` of `a`. -/
noncomputable def emeetDOther :
    (π : Side) → (a b : TagD) → Fin (emeetD (π.pick a b) (π.pick b a)).n → Fin b.n
  | .l, a, b => meetDR a.toF b.toF
  | .r, a, b => meetDL b.toF a.toF

/-- `emeetD_ty_spec` along `π`: the simple evidence of an entry is the tagged
meet of the entries of the two operands that it pairs. -/
theorem emeetD_ty_pick (π : Side) (a b : TagD) (c : Fin (emeetD (π.pick a b) (π.pick b a)).n) :
    emeetTy (π.pick (a.ty (emeetDTag π a b c)) (b.ty (emeetDOther π a b c)))
        (π.pick (b.ty (emeetDOther π a b c)) (a.ty (emeetDTag π a b c)))
      = some ((emeetD (π.pick a b) (π.pick b a)).ty c) := by
  cases π <;> exact emeetD_ty_spec _ _ c

/-- Validity along `π` of the tagged meet from the validity of its entries: the
tags `π` of an entry are those of the entry of `a` it comes from, and the
tag-guided precision composes through the reductivity of the meet into `a`
(`tagPrec_meetD`). -/
theorem hvalid_emeetD_of_cells {π : Side} {a b : TagD} {A : FDist}
    (ht : ∀ k, a.tag π k < A.n) (hp : TagPrec a.toF A fun k => ⟨a.tag π k, ht k⟩)
    (hga : GoodD a.toF) (hgb : GoodD b.toF)
    (hc : ∀ c, HVTag π ((emeetD (π.pick a b) (π.pick b a)).ty c)
      (A.ty ⟨a.tag π (emeetDTag π a b c), ht _⟩)) :
    HValid π (emeetD (π.pick a b) (π.pick b a)) A := by
  cases π
  · exact .mk (fun c => ht _)
      (tagPrec_of_eq (emeetD_toF _ _) (TagPrec.comp (tagPrec_meetD .l hga hgb) hp)) hc
  · exact .mk (fun c => ht _)
      (tagPrec_of_eq (emeetD_toF _ _) (TagPrec.comp (tagPrec_meetD .r hgb hga) hp)) hc

/-! ### One-sided hereditary validity of the tagged meet -/

mutual
/-- Lemma 37 (consistent transitivity preserves validity), simple types, one
side: if `a` is valid for `σ` along `π`, then so is its tagged meet with `b`
(the meet keeps the tags `π` of `a`). -/
theorem hemeetTy_valid {π : Side} : ∀ {a b m : TagTy} {σ : FTy},
    a ⊩[π] σ → GoodTy a.toF → GoodTy b.toF →
    π.pick a b ∘ π.pick b a = some m → m ⊩[π] σ
  | _, _, _, _, .unk, _, _, _ => .unk
  | _, _, _, _, .real, _, _, hm => by rw [emeetTy_pick_real hm]; exact .real
  | _, _, _, _, .bool, _, _, hm => by rw [emeetTy_pick_bool hm]; exact .bool
  | _, _, _, _, .arrow hs hd, hga, hgb, hm => by
      obtain ⟨rfl, rfl⟩ | ⟨s0, d0, s3, rfl, hs3, rfl⟩ := emeetTy_pick_arrow hm
      · exact .arrow hs hd
      · cases hga with
        | arrow hgs hgd =>
          cases hgb with
          | arrow hgs0 hgd0 =>
            exact .arrow (hemeetTy_valid hs hgs hgs0 hs3) (hemeetD_valid hd hgd hgd0)
/-- Lemma 37, distribution types, one side: validity along `π` survives the
tagged meet; each entry is handled by the simple-type case. -/
theorem hemeetD_valid {π : Side} : ∀ {a b : TagD} {A : FDist},
    a ⊩[π] A → GoodD a.toF → GoodD b.toF →
    π.pick a b ∘ π.pick b a ⊩[π] A
  | a, b, _, .mk ht hp hh, hga, hgb =>
      hvalid_emeetD_of_cells ht hp hga hgb fun c =>
        hemeetTy_valid (hh _) (TagD.goodTy_entry hga _) (TagD.goodTy_entry hgb _)
          (emeetD_ty_pick π a b c)
end

/-- Lemma 37 (consistent transitivity preserves validity), distribution types:
if `e1` is hereditarily left-valid for `A`, `e2` is hereditarily right-valid for
`C`, and both erasures are well-formed, their tagged meet is hereditarily valid
for `A ∼̇ C`. -/
theorem hvalidFor_emeetD {A C : FDist} {e1 e2 : TagD}
    (h1 : e1 ⊩[.l] A) (h2 : e2 ⊩[.r] C)
    (hg1 : GoodD e1.toF) (hg2 : GoodD e2.toF) :
    e1 ∘ e2 ⊩ A ∼̇ C :=
  ⟨hemeetD_valid h1 hg1 hg2, hemeetD_valid h2 hg2 hg1⟩

/-- Lemma 37 (consistent transitivity preserves validity), simple types: if `e1`
is valid for `σ1 ∼̇ σ'`, `e2` is valid for `σ' ∼̇ σ2`, both are well-formed and
`e1 ∘ e2` is defined, then `e1 ∘ e2` is valid for `σ1 ∼̇ σ2`. Type safety uses it
at each coercion. -/
theorem hetransTy_invariant {e1 e2 e3 : TagTy} {σ1 σ' σ2 : FTy}
    (h1 : e1 ⊩ σ1 ∼̇ σ') (h2 : e2 ⊩ σ' ∼̇ σ2)
    (hg1 : GoodTy e1.toF) (hg2 : GoodTy e2.toF)
    (hm3 : e1 ∘ e2 = some e3) : e3 ⊩ σ1 ∼̇ σ2 :=
  ⟨hemeetTy_valid h1.1 hg1 hg2 hm3, hemeetTy_valid h2.2 hg2 hg1 hm3⟩

/-! ## Per-entry facts about composed routing evidence

Rule (D::μ) computes the routing evidence `(μ′ ∥ μ) ∘ ξ` and steps to an
error when the composition is undefined, that is, when its formula is
unsatisfiable. The routing evidence is consumed by the step rather than
written in the result, so the reduction needs only its per-entry facts and
its marginals. The lemmas below provide them from the satisfiability of the
composition and the validity of the operands' entries; the consistency of
the pair of each entry holds on the carrier. -/

/-- The formula of the tagged meet is that of the meet of the erasures, so a
solution of the composition yields solutions of both operands' formulas. -/
theorem emeetD_C_dest {e1 e2 : TagD} {w : Fin (emeetD e1 e2).toF.n → ℝ}
    (hw : (emeetD e1 e2).toF.C w) : (∃ p, e1.toF.C p) ∧ (∃ q, e2.toF.C q) :=
  let ⟨h1, h2, _⟩ := (meetD_C_iff e1.toF e2.toF w).1 hw
  ⟨⟨_, h1⟩, ⟨_, h2⟩⟩

/-- The erasure of the tagged meet of well-formed evidences is well-formed as
soon as its formula is satisfiable. -/
theorem goodD_emeetD_sat {e1 e2 : TagD} (hg1 : GoodD e1.toF) (hg2 : GoodD e2.toF)
    (hsat : ∃ w, (emeetD e1 e2).toF.C w) : GoodD (emeetD e1 e2).toF := by
  rw [emeetD_toF] at hsat ⊢
  exact goodD_meetD_sat hg1 hg2 hsat

/-- Lemma 40 (validity of the routing evidence), item 2: per-entry validity of
a composed evidence: the simple evidence of each entry is valid for the pair of
entries of `A` and `C` that its tags name. Each side inherits the validity of
its operand's entry, and the consistency the composition needs is that of the
pair of the entry, which holds on the carrier. Rule (D::μ) uses it to type each
per-entry coercion. -/
theorem hemeetD_entry : ∀ {e1 e2 : TagD} {A C : FDist},
    (∀ (i : Fin e1.n) (h : e1.l i < A.n), e1.ty i ⊩[.l] A.ty ⟨_, h⟩) →
    (∀ (j : Fin e2.n) (h : e2.r j < C.n), e2.ty j ⊩[.r] C.ty ⟨_, h⟩) →
    (∀ i : Fin e1.n, GoodTy (e1.ty i).toF) →
    (∀ j : Fin e2.n, GoodTy (e2.ty j).toF) →
    ∀ (c : Fin (e1 ∘ e2).n)
      (h1 : (e1 ∘ e2).l c < A.n) (h2 : (e1 ∘ e2).r c < C.n),
      (e1 ∘ e2).ty c ⊩ A.ty ⟨_, h1⟩ ∼̇ C.ty ⟨_, h2⟩
  | e1, e2, A, C, hcL, hcR, hg1, hg2, c, h1, h2 =>
      ⟨hemeetTy_valid (hcL (meetDL e1.toF e2.toF c) h1) (hg1 _) (hg2 _) (emeetD_ty_spec e1 e2 c),
       hemeetTy_valid (hcR (meetDR e1.toF e2.toF c) h2) (hg2 _) (hg1 _) (emeetD_ty_spec e1 e2 c)⟩

/-- Lemma 40 (validity of the routing evidence), item 2: per-entry
well-formedness of a composed evidence, assuming only that the operands' entries
are well-formed: the simple evidence of an entry is the meet of two well-formed
consistent entries. -/
theorem goodTy_emeetD_entry : ∀ {e1 e2 : TagD},
    (∀ i : Fin e1.n, GoodTy (e1.ty i).toF) →
    (∀ j : Fin e2.n, GoodTy (e2.ty j).toF) →
    ∀ c : Fin (e1 ∘ e2).n, GoodTy ((e1 ∘ e2).ty c).toF
  | e1, e2, hg1, hg2, c =>
      goodTy_emeetTy_some (hg1 _) (hg2 _)
        (by rw [← tagD_toF_ty, ← tagD_toF_ty]; exact meetCell_cons _ _ c)
        (emeetD_ty_spec e1 e2 c)

/-- The push-forward of a solution of a composed evidence along the `r` tags
of its right operand solves the formula of `C`: the column clause of the
meet's formula, followed by the push-forward that the right validity of `e2`
provides. Type safety uses it in the case of rule (D::μ). -/
theorem emeetD_pushR : ∀ {e1 e2 : TagD} {C : FDist},
    HValid .r e2 C → ∀ {w : Fin (emeetD e1 e2).n → ℝ}, (emeetD e1 e2).toF.C w →
    ∀ (hR : ∀ c : Fin (emeetD e1 e2).n, (emeetD e1 e2).r c < C.n),
    C.C (pushfwd (fun c => (⟨(emeetD e1 e2).r c, hR c⟩ : Fin C.n)) w)
  | e1, e2, C, .mk _ hp2 _, w, hw, _ =>
      (congrArg C.C (pushfwd_comp _ _ w)).mp
        (hp2.push _ ((meetD_C_iff e1.toF e2.toF w).1 hw).2.1)

/-! ## The tagged meet of two types (`tagMeetTy`/`tagMeetD`)

The meet of two types, tagged at every level with the projections of the
entries of the carrier: the tagged witness construction (`tagWitness`) on the
runtime-consistent pairs. Elaboration uses it to build the evidence of an
ascription; it is hereditarily valid on both sides. -/

mutual
/-- The tagged meet of two simple types: `meetTy` with projection tags. When
one side is `?`, the result is the other type with diagonal tags
(`FTy.toTag`). The codomain is `tagMeetD D1 D2`, written out because
`tagMeetD` is defined after this block. -/
noncomputable def tagMeetTy : FTy → FTy → Option TagTy
  | .real, .real => some .real
  | .bool, .bool => some .bool
  | .unk, t => some t.toTag
  | t, .unk => some t.toTag
  | .arrow s1 D1, .arrow s2 D2 =>
      match tagMeetTy s1 s2 with
      | some s => some (.arrow s (tagWitness EConsTy D1 D2 (tagMeetDty D1 D2) Fin.val Fin.val))
      | none => none
  | _, _ => none
/-- The entries of the tagged meet of two distribution types (the entry
function of `tagMeetD`). -/
noncomputable def tagMeetDty : (D1 D2 : FDist) → Fin (liveK EConsTy D1 D2).card → TagTy
  | .mk n1 ty1 C1, .mk n2 ty2 C2 => fun c =>
      (tagMeetTy (ty1 (witnessL EConsTy ⟨n1, ty1, C1⟩ ⟨n2, ty2, C2⟩ c))
        (ty2 (witnessR EConsTy ⟨n1, ty1, C1⟩ ⟨n2, ty2, C2⟩ c))).getD .unk
end

/-- The tagged meet of two distribution types: the tagged witness construction
on the runtime-consistent pairs, with the entries `tagMeetDty` and the left
and right projections of each entry of the carrier as tags. Its number of entries
and its formula are those of `meetD D1 D2`, definitionally. -/
noncomputable def tagMeetD (D1 D2 : FDist) : TagD :=
  tagWitness EConsTy D1 D2 (tagMeetDty D1 D2) Fin.val Fin.val

/-- `σ ⊓ᵗ τ`, the meet of formula simple types as a tagged evidence, the
initial evidence of the elaboration (Figure 16). The article writes `⊓` for
both readings; Lean needs a second symbol because `meetTy` and `tagMeetTy`
take the same arguments. -/
scoped infixl:69 (name := tagMeetTyStx) " ⊓ᵗ " => tagMeetTy
/-- `D1 ⊓ᵗ D2`, the meet of formula distribution types as a tagged
evidence. -/
scoped infixl:69 (name := tagMeetDStx) " ⊓ᵗ " => tagMeetD

/-- The tagged meet of two types, unfolded: the number of entries and the formula
of the meet, and the projections of each entry as tags. -/
theorem tagMeetD_eq (D1 D2 : FDist) :
    tagMeetD D1 D2 = ⟨(meetD D1 D2).n, tagMeetDty D1 D2, (meetD D1 D2).C,
      fun c => (meetDL D1 D2 c).val, fun c => (meetDR D1 D2 c).val⟩ := rfl

/-- `?` is a right unit of the tagged meet of two types. -/
@[simp] theorem tagMeetTy_unk_right : ∀ (t : FTy), tagMeetTy t .unk = some t.toTag
  | .real => rfl
  | .bool => rfl
  | .unk => rfl
  | .arrow _ _ => rfl

mutual
/-- Erasing the tags of `tagMeetTy` gives `meetTy`. -/
theorem tagMeetTy_toF : ∀ (t1 t2 : FTy),
    Option.map TagTy.toF (tagMeetTy t1 t2) = meetTy t1 t2
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
  | .unk, .arrow s d => by
      show Option.map TagTy.toF (some (FTy.arrow s d).toTag)
        = some (FTy.arrow s d)
      rw [Option.map_some, FTy.toTag_toF]
  | .arrow s d, .real => rfl
  | .arrow s d, .bool => rfl
  | .arrow s d, .unk => by
      rw [tagMeetTy_unk_right, meetTy_unk_right, Option.map_some,
        FTy.toTag_toF]
  | .arrow s1 d1, .arrow s2 d2 => by
      have hs := tagMeetTy_toF s1 s2
      have hd := tagMeetD_toF d1 d2
      cases hm : tagMeetTy s1 s2 with
      | none =>
          rw [hm] at hs
          simp only [tagMeetTy, meetTy, hm, ← hs, Option.map_none]
      | some s =>
          rw [hm] at hs
          simp only [tagMeetTy, meetTy, hm, ← hs, Option.map_some]
          show some (FTy.arrow s.toF (tagMeetD d1 d2).toF)
            = some (FTy.arrow s.toF (meetD d1 d2))
          rw [hd]
/-- Erasing the tags of `tagMeetD` gives `meetD`. -/
@[simp] theorem tagMeetD_toF : ∀ (D1 D2 : FDist),
    (tagMeetD D1 D2).toF = meetD D1 D2
  | .mk n1 ty1 C1, .mk n2 ty2 C2 => by
      show witness EConsTy _ _ _ = witness EConsTy _ _ _
      congr 1
      funext c
      show ((tagMeetTy (ty1 _) (ty2 _)).getD .unk).toF = (meetTy (ty1 _) (ty2 _)).getD .unk
      rw [toF_getD_unk, tagMeetTy_toF]
end

/-! ### The entries of the tagged meet of two types -/

/-- The simple evidence of an entry of `tagMeetD D1 D2` is the tagged meet of
the operand entries named by its tags. -/
theorem tagMeetD_ty' (D1 D2 : FDist) (c : Fin (tagMeetD D1 D2).n) :
    (tagMeetD D1 D2).ty c
      = (tagMeetTy (D1.ty (meetDL D1 D2 c)) (D2.ty (meetDR D1 D2 c))).getD .unk := by
  cases D1; cases D2; rfl

/-- The erasure of the simple evidence of an entry of `tagMeetD D1 D2` is the
type of the same entry of the meet. -/
theorem tagMeetD_ty_toF (D1 D2 : FDist) (c : Fin (tagMeetD D1 D2).n) :
    ((tagMeetD D1 D2).ty c).toF = (meetD D1 D2).ty c := by
  rw [tagMeetD_ty', toF_getD_unk, tagMeetTy_toF, meetD_ty']

/-- The simple evidence of an entry of `tagMeetD D1 D2`, as a `some`: the tagged
meet of the two operand entries the entry comes from is defined, and it is that
simple evidence. -/
theorem tagMeetD_ty_spec (D1 D2 : FDist) (c : Fin (tagMeetD D1 D2).n) :
    tagMeetTy (D1.ty (meetDL D1 D2 c)) (D2.ty (meetDR D1 D2 c))
      = some ((tagMeetD D1 D2).ty c) := by
  rw [tagMeetD_ty']
  exact some_getD_of_map_toF ((tagMeetTy_toF _ _).trans (meetD_ty_spec D1 D2 c))

/-! ### Hereditary validity of the tagged meet of two types -/

mutual
/-- Lemma 35 (validity of the meet), simple types: on well-formed,
runtime-consistent simple types, the tagged meet is defined and hereditarily
valid on both sides. -/
theorem hvtag_tagMeetTy : ∀ {σ σ' : FTy}, GoodTy σ → GoodTy σ' → σ ∼̇ σ' →
    ∃ e, σ ⊓ᵗ σ' = some e ∧ e ⊩[.l] σ ∧ e ⊩[.r] σ'
  | _, _, _, _, .real => ⟨.real, rfl, .real, .real⟩
  | _, _, _, _, .bool => ⟨.bool, rfl, .bool, .bool⟩
  | _, _, _, hg', .unkL => ⟨_, rfl, .unk, hvtag_toTag .r hg'⟩
  | _, _, hg, _, .unkR => ⟨_, tagMeetTy_unk_right _, hvtag_toTag .l hg, .unk⟩
  | _, _, hg, hg', .arrow hds hdD => by
      cases hg with
      | arrow hgs1 hgD1 =>
        cases hg' with
        | arrow hgs2 hgD2 =>
          obtain ⟨es, hes, hL, hR⟩ := hvtag_tagMeetTy hgs1 hgs2 hds
          refine ⟨.arrow es (tagMeetD _ _), ?_,
            .arrow hL (hvalid_tagMeetD hgD1 hgD2).1,
            .arrow hR (hvalid_tagMeetD hgD1 hgD2).2⟩
          simp only [tagMeetTy, hes]
          rfl
/-- Lemma 35 (validity of the meet), distribution types: the tagged meet of two
well-formed distribution types is hereditarily valid on both sides: every
entry of the carrier pairs consistent entries, so its simple evidence is the
hereditarily valid tagged meet of those entries. -/
theorem hvalid_tagMeetD : ∀ {D D' : FDist}, GoodD D → GoodD D' →
    D ⊓ᵗ D' ⊩[.l] D ∧ D ⊓ᵗ D' ⊩[.r] D'
  | .mk _ _ _, .mk _ _ _, hg1, hg2 =>
      hvalid_tagWitness
        (tagPrec_of_eq (tagMeetD_toF _ _) (tagPrec_meetD .l hg1 hg2))
        (tagPrec_of_eq (tagMeetD_toF _ _) (tagPrec_meetD .r hg1 hg2))
        (fun c =>
          let ⟨_, he, hL, _⟩ := hvtag_tagMeetTy (hg1.tys _) (hg2.tys _) (meetCell_cons _ _ c)
          (congrArg (HVTag .l · _) (Option.some.inj (he.symm.trans (tagMeetD_ty_spec _ _ c)))).mp hL)
        (fun c =>
          let ⟨_, he, _, hR⟩ := hvtag_tagMeetTy (hg1.tys _) (hg2.tys _) (meetCell_cons _ _ c)
          (congrArg (HVTag .r · _) (Option.some.inj (he.symm.trans (tagMeetD_ty_spec _ _ c)))).mp hR)
end

/-! ## A common lower bound witnesses consistency

In the runtime relations, `X ⊑̇ A` and `X ⊑̇ B` with `X` well-formed imply
`A ∼̇ B`. This is one direction of the characterization of runtime
consistency stated after Lemma 8; the other is Lemma 8 with Lemma 34. In
particular, evidence for a judgment witnesses the consistency of its two
sides (`consD_of_evD`). At distribution types the two precision liftings
are composed through a shared solution of the lower bound (`Lift.symm`,
`Lift.trans`), and the support condition is the simple-type statement. -/

mutual
/-- Lemma 8 (reductivity of the meet operator), item 3,
definedness, simple types: two simple types with a well-formed common lower
bound in runtime precision are runtime-consistent. -/
theorem consTy_of_common_lb : ∀ {e a b : FTy}, GoodTy e →
    e ⊑̇ a → e ⊑̇ b → a ∼̇ b
  | _, _, b, _, .unk, _ => .unkL
  | _, _, _, _, .real, .real => .real
  | _, _, _, _, .real, .unk => .unkR
  | _, _, _, _, .bool, .bool => .bool
  | _, _, _, _, .bool, .unk => .unkR
  | _, _, _, _, .arrow _ _, .unk => .unkR
  | _, _, _, hg, .arrow hs1 hD1, .arrow hs2 hD2 => by
      cases hg with
      | arrow hgs hgD =>
        exact .arrow (consTy_of_common_lb hgs hs1 hs2)
          (consD_of_common_lb hgD hD1 hD2)
  termination_by structural e a b hg h1 h2 => h1
/-- Lemma 8 (reductivity of the meet operator), item 3,
definedness, distribution types: two distribution types with a well-formed
common lower bound in runtime precision are runtime-consistent: the two
precision liftings compose through a shared solution of the lower bound. -/
theorem consD_of_common_lb : ∀ {E A B : FDist}, GoodD E →
    E ⊑̇ A → E ⊑̇ B → A ∼̇ B
  | E, A, B, hg, .mk R1 hR1 hc1, .mk R2 hR2 hc2 => by
      obtain ⟨p, hp⟩ := hg.good.sat
      obtain ⟨qA, hqA, hlA⟩ := hc1 p hp
      obtain ⟨qB, hqB, hlB⟩ := hc2 p hp
      exact .mk (fun a b => ∃ i, R1 i a ∧ R2 i b)
        (fun a b ⟨i, h1, h2⟩ => consTy_of_common_lb (hg.tys i) (hR1 i a h1) (hR2 i b h2))
        ⟨qA, qB, hqA, hqB, hlA.symm.trans hlB fun _ i _ h1 h2 => ⟨i, h1, h2⟩⟩
  termination_by structural E A B hg h1 h2 => h1
end

/-- Well-formed evidence for `A ∼̇ B` witnesses the runtime consistency of `A`
and `B`. -/
theorem consD_of_evD {ε A B : FDist} (h : EEvD ε A B) (hg : GoodD ε) :
    EConsD A B :=
  consD_of_common_lb hg h.1 h.2

/-! ## Greatest lower bound (Lemma 8, item 3)

A well-formed common lower bound of two types is below their meet. At
distribution types, a solution `x` of the lower bound is transported through
both precision couplings `u` and `v` with the three-index weight of their
composition through `x` (`glue₃`, `T a i b = u i a · v i b / x i`). Summed
over `i` it is the composed coupling of the two operands (`IsCoupling.glue`),
which is supported on consistent pairs because two types with a common lower
bound are consistent (`consTy_of_common_lb`); its restriction to the carrier
solves the meet's formula and, restricted to the carrier, `T` couples `x`
with that solution (`witness_coupling_of_glue`). -/

/-- The coupling part of the greatest-lower-bound property of the meet: the
coupling it produces sends each entry of `X` only to entries of the meet whose
two provenance tags (`meetDL`, `meetDR`) are related to it by the input couplings
`R1` and `R2`. The precision of the entries is added in
`eprec_meetD_glb` and `eprec_meetD_glb_tags`. -/
theorem eprec_meetD_glb_core : ∀ {X A B : FDist}
    {R1 : Fin X.n → Fin A.n → Prop} {R2 : Fin X.n → Fin B.n → Prop}, GoodD X →
    (∀ i a, R1 i a → EPrecTy (X.ty i) (A.ty a)) →
    (∀ i b, R2 i b → EPrecTy (X.ty i) (B.ty b)) →
    SymLiftAll R1 X.C A.C → SymLiftAll R2 X.C B.C →
    SymLiftAll (fun i c => R1 i (meetDL A B c) ∧ R2 i (meetDR A B c)) X.C (meetD A B).C
  | X, A, B, R1, R2, hg, hR1, hR2, hc1, hc2 => by
      intro x hx
      obtain ⟨p, hp, u, hu, hsu⟩ := hc1 x hx
      obtain ⟨q, hq, v, hv, hsv⟩ := hc2 x hx
      -- two entries related to the same entry of `X` are consistent
      have hcons : ∀ {a i b}, R1 i a → R2 i b → EConsTy (A.ty a) (B.ty b) := fun h1 h2 =>
        consTy_of_common_lb (hg.tys _) (hR1 _ _ h1) (hR2 _ _ h2)
      -- a positive three-index weight relates `i` to both entries
      have hT : ∀ {a i b}, 0 < glue₃ x (fun a i => u i a) v a i b → R1 i a ∧ R2 i b :=
        fun h => let ⟨h1, h2⟩ := glue₃_pos hu.symm hv h; ⟨hsu _ _ h1, hsv _ _ h2⟩
      -- the composition of the two couplings through `x` is supported on
      -- consistent pairs; its restriction to the carrier solves the meet's
      -- formula and the three-index weight couples `x` with it
      obtain ⟨w, hw, hc⟩ := witness_coupling_of_glue (ty := meetDty A B)
        (T := fun i a b => glue₃ x (fun a i => u i a) v a i b) hp hq (hu.symm.glue hv)
        (fun a b h => let ⟨_, h1, h2⟩ := glue₂_pos hu.symm hv h; hcons (hsu _ _ h1) (hsv _ _ h2))
        (fun i a b => glue₃_nonneg hu.symm hv a i b)
        (fun i => (Finset.sum_congr rfl fun a _ => sum_glue₃_right hu.symm hv a i).trans
          (hu.row i))
        fun _ _ => rfl
      exact ⟨w, hw, _, hc, fun _ _ h => hT h⟩

mutual
/-- Lemma 8 (reductivity of the meet operator), item 3,
simple types: a well-formed common lower bound of `A` and `B` is below their
meet. The definedness of the meet, also part of the article's statement, is
given by `consTy_of_common_lb` and `cons_meetTy_isSome`. -/
theorem eprec_meetTy_glb : ∀ {X A B mAB : FTy}, GoodTy X →
    X ⊑̇ A → X ⊑̇ B → A ⊓ B = some mAB → X ⊑̇ mAB
  | _, _, B, mAB, _, .unk, h2, hm => by
      -- `A = ?`: the meet collapses to `B` (definitional first clause)
      obtain rfl : B = mAB := Option.some.inj hm
      exact h2
  | _, _, _, mAB, _, .real, h2, hm => by
      cases h2 with
      | real =>
          obtain rfl : FTy.real = mAB := Option.some.inj hm
          exact .real
      | unk =>
          rw [meetTy_unk_right] at hm
          obtain rfl : FTy.real = mAB := Option.some.inj hm
          exact .real
  | _, _, _, mAB, _, .bool, h2, hm => by
      cases h2 with
      | bool =>
          obtain rfl : FTy.bool = mAB := Option.some.inj hm
          exact .bool
      | unk =>
          rw [meetTy_unk_right] at hm
          obtain rfl : FTy.bool = mAB := Option.some.inj hm
          exact .bool
  | _, _, _, mAB, hg, .arrow hs1 hD1, .unk, hm => by
      -- `B = ?`: the meet collapses to `A`
      rw [meetTy_unk_right] at hm
      obtain rfl := Option.some.inj hm
      exact .arrow hs1 hD1
  | .arrow sX DX, .arrow sA DA, .arrow sB DB, mAB, hg,
      .arrow hs1 hD1, .arrow hs2 hD2, hm => by
      cases hg with
      | arrow hgs hgD =>
        cases hms : meetTy sA sB with
        | none =>
            simp only [meetTy, hms] at hm
            exact nomatch hm
        | some s3 =>
            simp only [meetTy, hms] at hm
            obtain rfl := Option.some.inj hm
            exact .arrow (eprec_meetTy_glb hgs hs1 hs2 hms)
              (eprec_meetD_glb hgD hD1 hD2)
  termination_by structural X A B mAB hg h1 h2 hm => h1
/-- Lemma 8 (reductivity of the meet operator), item 3,
distribution types: a well-formed common lower bound of `A` and `B` is below
`A ⊓ B`. The definedness of the meet (satisfiability of its formula) is given
by `consD_of_common_lb` and `meetD_sat_iff_econsD`. -/
theorem eprec_meetD_glb : ∀ {X A B : FDist}, GoodD X →
    X ⊑̇ A → X ⊑̇ B → X ⊑̇ A ⊓ B
  | X, A, B, hg, .mk R1 hR1 hc1, .mk R2 hR2 hc2 =>
      .intro ((eprec_meetD_glb_core hg hR1 hR2 hc1 hc2).mono fun i c ⟨hL, hR⟩ =>
        eprec_meetTy_glb (hg.tys i) (hR1 i _ hL) (hR2 i _ hR) (meetD_ty_spec A B c))
  termination_by structural X A B hg h1 h2 => h1
end

/-- Tag-aware form of `eprec_meetD_glb`: the coupling it produces sends each
entry of `X` only to entries of the meet whose two provenance tags (`meetDL`,
`meetDR`) are related to it by the input couplings `R1` and `R2`. The routed
cases of the dynamic gradual guarantee use it: the left tag names the value
being routed and the right tag its target entry. -/
theorem eprec_meetD_glb_tags : ∀ {X A B : FDist}
    {R1 : Fin X.n → Fin A.n → Prop} {R2 : Fin X.n → Fin B.n → Prop}, GoodD X →
    (∀ i a, R1 i a → EPrecTy (X.ty i) (A.ty a)) →
    (∀ i b, R2 i b → EPrecTy (X.ty i) (B.ty b)) →
    SymLiftAll R1 X.C A.C → SymLiftAll R2 X.C B.C →
    SymLiftAll (fun i c => EPrecTy (X.ty i) ((meetD A B).ty c) ∧
      R1 i (meetDL A B c) ∧ R2 i (meetDR A B c)) X.C (meetD A B).C
  | X, A, B, R1, R2, hg, hR1, hR2, hc1, hc2 =>
      (eprec_meetD_glb_core hg hR1 hR2 hc1 hc2).mono fun i c ⟨hL, hR⟩ =>
        ⟨eprec_meetTy_glb (hg.tys i) (hR1 i _ hL) (hR2 i _ hR) (meetD_ty_spec A B c), hL, hR⟩

end GradualProb.TPLC
