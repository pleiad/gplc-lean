import GradualProb.TPLC.EvidencePrecision
import GradualProb.TPLC.PrecisionSubstitution

/-!
# Cases of the dynamic gradual guarantee for TPLC

This module proves the case lemmas of Theorem 5 (dynamic gradual guarantee for
TPLC), which `TPLC/GradualGuarantee` assembles. Each lemma takes a reduction
rule of the more precise term together with the given reduction of the less
precise one and shows that the resulting configurations are related by
precision (`DConfPrec`). The ascription steps rely on Lemma 12 (monotonicity
of evidence combination, `meetTy_mono`); the routed rules (Dlet) and (D::μ)
rely on the facts for reordering (Lemmas 10 and 48), and rule (D::μ) also on
Lemma 8 (reductivity of the meet operator).

## Main results

* `dgg_cell`, `dgg_cell_cond`, `dgg_cell_ef`: one value ascription (the
  coercion at a single entry), rules (D::σ) and (Derr::σ); `dgg_cell_ef` is
  Lemma 49 (coercion of related values).
* `dgg_app_cond`: the case of rule (Dapp).
* `dgg_dascD_cond`: the case of rule (D::μ).
* `dgg_dlet_cond`: the case of rule (Dlet).
* `dconfprec_choose_cond`, `dconfprec_choose_unk_cond`, `dconfprec_chooseU`,
  `dconfprec_wsum`, `dgg_cells_assemble`: Lemma 50 (precision of
  configurations is a congruence), items 2 and 3, for the operations that
  build configurations.

## Reading guide

The file goes from the entry level to the rule level: runtime types of related
values, the simulation of one coercion, the precision of the computed routing
evidences (`eprecD_routing`, `eprecD_routing_tags`), the assembly of routed
entries, the congruences for mixtures, the inversion lemmas for the reduction
of the less precise term (`red_*_inv`), and finally the conditional cases
`dgg_app_cond`, `dgg_dascD_cond` and `dgg_dlet_cond`.
-/


namespace GradualProb.TPLC

open GradualProb.GPLC

open Classical


/-! ## From related values to related runtime types

The routed rules (Dlet) and (D::μ) compare the two computed routing
evidences, and for that they need the runtime types of the two terms they reduce first to
be related. Precision of configurations relates them: its coupling has positive
weight only between related values, and related values exhibit related types. -/

/-- A closed well-typed value that is not an error is an ascription. -/
theorem asc_of_not_err {v : Val} (hv : HasTyV [] v v.tyEntry)
    (hne : ∀ σ, v ≠ .err σ) : ∃ ε u σ, v = .asc ε u σ := by
  cases v with
  | var x => cases hv with | var hx => simp at hx
  | err σ => exact absurd rfl (hne σ)
  | asc ε u σ => exact ⟨ε, u, σ, rfl⟩

/-- Related closed values exhibit types related by runtime precision: an
ascription by its annotation, an error by the type premise of rule `errV`. -/
theorem tyEntry_eprec : ∀ {v v' : Val}, PrecV [] [] v v' →
    EPrecTy v.tyEntry v'.tyEntry
  | _, _, .var => .unk
  | _, _, .asc _ _ _ hσ => eprecTy_of_precTy hσ
  | _, _, .errV hty hσ => by
      rw [tyEntry_of_hasTy hty]
      exact eprecTy_of_precTy hσ

/-- Related closed values that are not variables (the values that reduction
produces) exhibit types related by type precision (Definition 6): both the
annotation of an ascribed value and the type of an error come from the
premise of their rule. -/
theorem tyEntry_prec : ∀ {v v' : Val}, PrecV [] [] v v' →
    (∀ x, v ≠ .var x) → PrecTy v.tyEntry v'.tyEntry
  | _, _, .var, hne => absurd rfl (hne _)
  | _, _, .asc _ _ _ hσ, _ => hσ
  | _, _, .errV hty hσ, _ => by
      rw [tyEntry_of_hasTy hty]
      exact hσ

/-- A value well typed in the empty context is not a variable. -/
theorem not_var_of_closed {v : Val} {σ : FTy} (h : HasTyV [] v σ) :
    ∀ x, v ≠ .var x := by
  intro x hx
  subst hx
  cases h with | var hxx => simp at hxx

/-- Precision of configurations implies runtime precision of their computed
types (`DConf.confF`). -/
theorem eprecD_confF_of_dconfprec {V V' : DConf} (h : DConfPrec V V') :
    EPrecD V.confF V'.confF :=
  .intro (h.mono fun _ _ => tyEntry_eprec)


/-! ## Error-free configurations

Theorem 5 assumes that the reduction of the more precise term raises no
error. `ErrFree` is the corresponding property of a configuration: every outcome
with positive probability is an ascription, not an error. -/

/-- No outcome of positive probability in any solution of the configuration is an
error. -/
def ErrFree (V : DConf) : Prop :=
  ∀ p, V.C p → ∀ c, 0 < p c →
    ∃ (ε : TagTy) (u : Raw) (σ : FTy), V.val c = .asc ε u σ

/-- A Dirac configuration on an ascription is error-free. -/
theorem errFree_point {ε : TagTy} {u : Raw} {σ : FTy} :
    ErrFree (DConf.point (.asc ε u σ)) := fun _ _ _ _ => ⟨ε, u, σ, rfl⟩


/-! ## Simulation of a single coercion

Rules (D::μ) and (Dlet) coerce, at each entry of their routing evidence, a
value of the term they reduce first to the type of the target entry. The lemmas below
simulate one such coercion, independently of the syntactic shape of the
term: related values, related evidences and related targets give related
results. -/

/-- Lemma 49 (coercion of related values), extended to every coercion of a
value (both cases of rule (D::σ), and rule (Derr::σ)): if related closed
values are coerced with related evidences to related targets and the precise
coercion steps to `w`, then the less precise one steps to some `w'` with
`w ⊑ w'`. The less precise side always steps (`ascV_total`) and its result is
above the precise one: if the precise evidences compose, so do the less
precise ones (`meetTy_mono`) and the composed evidences are related; if the
precise side fails, its error is below the less precise value, which is well
typed by the validity of its own evidence.
-/
theorem dgg_cell {e e' : TagTy} {v v' w : Val} {σt σt' : FTy}
    (hv : HasTyV [] v v.tyEntry) (hv' : HasTyV [] v' v'.tyEntry)
    (hevR : HVTag .r e σt) (hev' : HVTagTy e' v'.tyEntry σt')
    (hge : GoodTy e.toF) (hge' : GoodTy e'.toF)
    (hgσt' : GoodTy σt')
    (hvv : PrecV [] [] v v') (hee : TagPrecTy .r σt σt' e e')
    (hσ : PrecTy σt σt')
    (hstep : Red (.ascV e v σt) 1 (DConf.point w)) :
    ∃ w', Red (.ascV e' v' σt') 1 (DConf.point w') ∧ PrecV [] [] w w' := by
  have hless : ∀ {ww' : Val}, Red (.ascV e' v' σt') 1 (DConf.point ww') →
      HasTyV [] ww' σt' :=
    fun h => cell_coercion_typed hv' hev' hge' hgσt' h
  have hco := red_ascV_iff.1 hstep
  -- the precise side fails: its error is below the less precise result
  have herr : w = .err σt → ∃ w', Red (.ascV e' v' σt') 1 (DConf.point w') ∧
      PrecV [] [] w w' := by
    rintro rfl
    obtain ⟨ww', hstep'⟩ := ascV_total hv' e' σt'
    exact ⟨ww', hstep', PrecV.errV (hless hstep') hσ⟩
  cases v with
  | var x => exact nomatch hco
  | err σe => cases hco; exact herr rfl
  | asc ε1 u σv =>
    rcases Val.coerce_asc_inv hco with ⟨ε3, hmeet, hgε3, rfl⟩ | ⟨-, rfl⟩
    · -- the precise evidences compose, hence so do the less precise ones
      cases hv with
      | ascRaw hu hev1 hge1 _ =>
        cases hvv with
        | asc hε1 hε1L hu' hσv =>
          rename_i ε1' u2 σv2
          cases hv' with
          | ascRaw hu2 hev1' hge1' _ =>
            obtain ⟨m', hm', hgm', hmm'⟩ :=
              meetTy_mono hge1 hge hge1' hge' (TagPrecTy.toEPrecTy hε1)
                (TagPrecTy.toEPrecTy hee) (emeetTy_toF_some hmeet) hgε3
            obtain ⟨e3t', hme3', hetoF'⟩ := emeetTy_some_of_meetTy hm'
            refine ⟨.asc e3t' u2 σt', Red.dascOk hme3' (by rw [hetoF']; exact hgm'),
              ?_⟩
            refine PrecV.asc ?_ ?_ hu' hσ
            · exact tagPrecTy_emeetTy hge hge1 hge' hge1'
                hevR hev'.right hee (TagPrecTy.toEPrecTy hε1) hmeet hme3' hgε3
            · -- the left half, against the raw values' types
              intro σu σu' hty1 hty2
              obtain rfl := hasTy_closed_det_raw hu hty1
              obtain rfl := hasTy_closed_det_raw hu2 hty2
              exact tagPrecTy_emeetTy hge1 hge hge1' hge'
                hev1.left hev1'.left
                (hε1L hu hu2)
                (TagPrecTy.toEPrecTy hee) hmeet hme3' hgε3
    · exact herr rfl

/-! ## Precision of the routing evidences

Rule (D::μ) routes the outcomes of the ascribed term's result through the evidence
`E = meetD (reorderD μ′ μ) ξ`, where `μ′` is the runtime type of the
ascribed term, `μ` its static type and `ξ` the evidence of the ascription.
Writing `E′ = meetD (reorderD μ′′ μₗ) ξ′` for the less precise side, the
precise routing evidence is below the less precise one:

    E ⊑̇ μ′ ∥ μ ⊑̇ μ′                 (Lemma 8 and Lemma 10, reductivity)
    μ′ ⊑̇ μ′′                          (induction hypothesis on the ascribed term)
    RefDist μ′′ μₗ                    (type safety of the less precise side)
    ─────────────────────────────────
    E ⊑̇ μ′′ ∥ μₗ                     (Lemma 48, greatest lower bound of reordering)

    E ⊑̇ ξ ⊑̇ ξ′                        (Lemma 8 and the term precision)
    ─────────────────────────────────
    E ⊑̇ E′                            (Lemma 8, greatest lower bound)
-/

/-- The precise routing evidence is below the less precise one (runtime precision). -/
theorem eprecD_routing {γp γl A B : FDist} {εd εd' : FDist}
    (hgγp : GoodD γp) (hgA : GoodD A) (hgγl : GoodD γl)
    (hgεd : GoodD εd) (hgrp : GoodD (reorderD γp A))
    (hgE : GoodD (meetD (reorderD γp A) εd))
    (hrun : EPrecD γp γl) (href : RefDist γl B) (hev : EPrecD εd εd') :
    EPrecD (meetD (reorderD γp A) εd) (meetD (reorderD γl B) εd') := by
  -- below the less precise reordering
  have h1 : EPrecD (meetD (reorderD γp A) εd) (reorderD γp A) :=
    eprec_meetD .l hgrp hgεd
  have h2 : EPrecD (reorderD γp A) γp := eprec_reorderD .l hgγp hgA
  have h4 : EPrecD (meetD (reorderD γp A) εd) γl :=
    EPrecD.trans (EPrecD.trans h1 h2) hrun
  have h5 : EPrecD (meetD (reorderD γp A) εd) (reorderD γl B) :=
    eprec_reorderD_glb hgγl h4 href
  -- below the less precise evidence written in the term
  have h7 : EPrecD (meetD (reorderD γp A) εd) εd' :=
    EPrecD.trans (eprec_meetD .r hgrp hgεd) hev
  -- hence below their meet
  exact eprec_meetD_glb hgE h5 h7

/-! ### The routing evidence and the meet of erasures

Rule (D::μ) computes the routing evidence `(μ′ ∥ μ) ∘ ξ` on tagged evidences.
Its entries and formula are those of the meet of erasures
`meetD (tagReorderD μ′ μ).toF ξ.toF`, definitionally (`emeetD_toF` equates
the entries), so the relational lemmas of this module are stated over that
meet and read the tagged entries directly. `routing_toF` relates it to the
meet `meetD (reorderD μ′ μ) ξ.toF` of the untagged operators, whose entries
agree with the tagged ones only propositionally. -/

/-- The erasure of the computed routing evidence. -/
theorem routing_toF (D1 D2 : FDist) (ξ : TagD) :
    (emeetD (tagReorderD D1 D2) ξ).toF = meetD (reorderD D1 D2) ξ.toF := by
  rw [emeetD_toF, tagReorderD_toF]

/-- `eprecD_routing` for the tagged evidences, as rule (D::μ) computes
them. -/
theorem eprecD_routing_tagged {γp γl A B : FDist} {εd εd' : TagD}
    (hgγp : GoodD γp) (hgA : GoodD A) (hgγl : GoodD γl)
    (hgεd : GoodD εd.toF) (hgrp : GoodD (tagReorderD γp A).toF)
    (hgE : GoodD (emeetD (tagReorderD γp A) εd).toF)
    (hrun : EPrecD γp γl) (href : RefDist γl B)
    (hev : EPrecD εd.toF εd'.toF) :
    EPrecD (emeetD (tagReorderD γp A) εd).toF
      (emeetD (tagReorderD γl B) εd').toF := by
  rw [tagReorderD_toF] at hgrp
  rw [routing_toF] at hgE
  rw [routing_toF, routing_toF]
  exact eprecD_routing hgγp hgA hgγl hgεd hgrp hgE hrun href hev

/-! ## The less precise side cannot fail

The failure case of rule (D::μ) applies when the composed routing evidence
is not defined, that is, when its formula is unsatisfiable. If the precise
side composed, its formula has a solution, and the precision of the routing
evidences carries it to a solution of the less precise one. -/

/-- If the composed routing evidence of the precise side of rule (D::μ) is
satisfiable, then so is the one of the less precise side. -/
theorem dascD_less_precise_defined {γp γl A B : FDist} {εd εd' : TagD}
    (hgγp : GoodD γp) (hgA : GoodD A) (hgγl : GoodD γl)
    (hgεd : GoodD εd.toF) (hgrp : GoodD (tagReorderD γp A).toF)
    (hgE : GoodD (emeetD (tagReorderD γp A) εd).toF)
    (hrun : EPrecD γp γl) (href : RefDist γl B)
    (hev : EPrecD εd.toF εd'.toF)
    (hsat : ∃ w, (emeetD (tagReorderD γp A) εd).toF.C w) :
    ∃ w', (emeetD (tagReorderD γl B) εd').toF.C w' :=
  eprecD_sat (eprecD_routing_tagged hgγp hgA hgγl hgεd hgrp hgE hrun href hev)
    hsat


/-! ## Determinism of the coercion at a single entry and the conditional simulation

Theorem 5 is stated for a given reduction of the less precise term, so the
simulation of one coercion compares two given steps. The ascription of a value is
deterministic, so it suffices to compose `dgg_cell` with that determinism. -/

/-- The one-step reduction of a value ascription is deterministic. -/
theorem red_ascV_det {e : TagTy} {v : Val} {σt : FTy} {w1 w2 : Val}
    (h1 : Red (.ascV e v σt) 1 (DConf.point w1))
    (h2 : Red (.ascV e v σt) 1 (DConf.point w2)) : w1 = w2 :=
  Option.some.inj ((red_ascV_iff.1 h1).symm.trans (red_ascV_iff.1 h2))

/-- The simulation of one coercion with both steps given. -/
theorem dgg_cell_cond {e e' : TagTy} {v v' w w' : Val} {σt σt' : FTy}
    (hv : HasTyV [] v v.tyEntry) (hv' : HasTyV [] v' v'.tyEntry)
    (hevR : HVTag .r e σt) (hev' : HVTagTy e' v'.tyEntry σt')
    (hge : GoodTy e.toF) (hge' : GoodTy e'.toF)
    (hgσt' : GoodTy σt')
    (hvv : PrecV [] [] v v') (hee : TagPrecTy .r σt σt' e e')
    (hσ : PrecTy σt σt')
    (hstep : Red (.ascV e v σt) 1 (DConf.point w))
    (hstep' : Red (.ascV e' v' σt') 1 (DConf.point w')) :
    PrecV [] [] w w' := by
  obtain ⟨w'', hstep'', hww''⟩ :=
    dgg_cell hv hv' hevR hev' hge hge' hgσt' hvv hee hσ hstep
  rwa [red_ascV_det hstep'' hstep'] at hww''


/-! ## Tag-aware precision of the routing evidences -/

/-- The tag-aware version of `eprecD_routing`: a coupling between the entries
of the two routing evidences that, on each pair of positive weight, relates
the evidences of the entries (tag-aware precision), the values they route (left tags,
against the relation `Rval` given by the induction hypothesis on the
ascribed term) and their targets (right tags). These are the obligations that
rule `PrecV.asc` imposes on each paired entry. The routed value and the target
of an entry are given as the functions `fL`, `fR` with the equations that tie
them to the entry projections, so that rule (D::μ) can pass its own forms. -/
theorem eprecD_routing_tags {γp γl A B γb γb' : FDist} {εd εd' : TagD}
    {Rval : Fin γp.n → Fin γl.n → Prop}
    {fL : Fin (emeetD (tagReorderD γp A) εd).n → Fin γp.n}
    {fR : Fin (emeetD (tagReorderD γp A) εd).n → Fin γb.n}
    {fL' : Fin (emeetD (tagReorderD γl B) εd').n → Fin γl.n}
    {fR' : Fin (emeetD (tagReorderD γl B) εd').n → Fin γb'.n}
    (hfL : ∀ k, fL k = reorderDL γp A (meetDL (tagReorderD γp A).toF εd.toF k))
    (hfR : ∀ k, (fR k : ℕ) = εd.r (meetDR (tagReorderD γp A).toF εd.toF k))
    (hfL' : ∀ c, fL' c = reorderDL γl B (meetDL (tagReorderD γl B).toF εd'.toF c))
    (hfR' : ∀ c, (fR' c : ℕ) = εd'.r (meetDR (tagReorderD γl B).toF εd'.toF c))
    (hgγp : GoodD γp) (hgA : GoodD A) (hgγl : GoodD γl)
    (hgεd : GoodD εd.toF) (hgεd' : GoodD εd'.toF)
    (hgB : GoodD B) (hgγb' : GoodD γb')
    (hgrp : GoodD (tagReorderD γp A).toF)
    (hgE : GoodD (emeetD (tagReorderD γp A) εd).toF)
    (hvεd' : HValid .r εd' γb') (hrl : EReordD γl B)
    (hRval : ∀ i i', Rval i i' → EPrecTy (γp.ty i) (γl.ty i'))
    (hrun : SymLiftAll Rval γp.C γl.C)
    (href : RefDist γl B)
    (hev : TagPrecD .r εd εd' γb γb') :
    SymLiftAll (fun k c =>
        TagPrecTy .r (γb.ty (fR k)) (γb'.ty (fR' c))
          ((emeetD (tagReorderD γp A) εd).ty k) ((emeetD (tagReorderD γl B) εd').ty c) ∧
        Rval (fL k) (fL' c) ∧
        PrecTy (γb.ty (fR k)) (γb'.ty (fR' c)))
      (emeetD (tagReorderD γp A) εd).toF.C (emeetD (tagReorderD γl B) εd').toF.C := by
  have hgX : GoodD (meetD (tagReorderD γp A).toF εd.toF) := by
    rw [emeetD_toF] at hgE; exact hgE
  have hgrlT : GoodD (tagReorderD γl B).toF := goodD_tagReorderD_toF hgγl hgB hrl
  -- (A) the precise routing evidence is related (tag-aware) to the less precise
  -- evidence written in the term, by reductivity of the meet
  have hA : TagPrecD .r (emeetD (tagReorderD γp A) εd) εd' γb γb' :=
    tagPrecD_emeet_compose hgεd hgrp hev
  -- the functional coupling given by the left projections of the entries
  have hTR : TagPrec (tagReorderD γp A).toF γp (reorderDL γp A) :=
    tagPrec_of_eq (tagReorderD_toF γp A) (tagPrec_reorderD .l hgγp hgA)
  have hEL : TagPrec (meetD (tagReorderD γp A).toF εd.toF) γp
      (fun k => reorderDL γp A (meetDL (tagReorderD γp A).toF εd.toF k)) :=
    TagPrec.comp (tagPrec_meetD .l hgrp hgεd) hTR
  -- the lifting against the less precise reordering, through the left tags
  have hreord : SymLiftAll (fun k c' =>
      EPrecTy ((meetD (tagReorderD γp A).toF εd.toF).ty k) ((tagReorderD γl B).toF.ty c') ∧
      Rval (reorderDL γp A (meetDL (tagReorderD γp A).toF εd.toF k)) (reorderDL γl B c'))
      (meetD (tagReorderD γp A).toF εd.toF).C (tagReorderD γl B).toF.C :=
    (eprec_reorderD_glb_tags
      (R1 := fun k i' => Rval (reorderDL γp A (meetDL (tagReorderD γp A).toF εd.toF k)) i')
      hgγl (fun k i' h => EPrecTy.trans (hEL.cell k) (hRval _ _ h))
      (coup_comp_fun (R := Rval) hEL hgX.good hrun) href).mono fun k c' ⟨h1, h2⟩ =>
        ⟨by rw [tagD_toF_ty, tagReorderD_ty_toF]; exact h1, h2⟩
  -- the lifting of (A), with the targets of the precise entries written as `fR`
  have hevE : SymLiftAll (fun k c'' =>
      TagPrecTy .r (γb.ty (fR k)) (γb'.ty ⟨εd'.r c'', hev.tag_lt' _⟩)
        ((emeetD (tagReorderD γp A) εd).ty k) (εd'.ty c'') ∧
      PrecTy (γb.ty (fR k)) (γb'.ty ⟨εd'.r c'', hev.tag_lt' _⟩))
      (meetD (tagReorderD γp A).toF εd.toF).C εd'.toF.C :=
    hA.coup.mono fun c c'' ⟨hty, hdst⟩ => by
      have hidx : (⟨(emeetD (tagReorderD γp A) εd).r c, hA.tag_lt c⟩ : Fin γb.n) = fR c :=
        Fin.ext (hfR c).symm
      dsimp only [TagD.tag_r] at hty hdst
      rw [hidx] at hty hdst
      exact ⟨hty, hdst⟩
  refine SymLiftAll.mono
    (eprec_meetD_glb_tags hgX (fun _ _ h => h.1)
      (fun k c'' h => by
        have := TagPrecTy.toEPrecTy h.1
        rw [emeetD_ty_toF, ← tagD_toF_ty] at this
        exact this)
      hreord hevE)
    fun k c h => ?_
  obtain ⟨-, h1, h2ty, h2dst⟩ := h
  -- the less precise target of an entry of the meet is that of its origin in `ξ′`
  have hdst' : (⟨εd'.r (meetDR (tagReorderD γl B).toF εd'.toF c), hev.tag_lt' _⟩ : Fin γb'.n)
      = fR' c :=
    (Fin.ext (hfR' c)).symm
  rw [hdst'] at h2ty h2dst
  refine ⟨?_, ?_, h2dst⟩
  · -- (B) tag-aware greatest lower bound: the common lower bound is below the
    -- less precise meet, with the targets named by its second origin
    refine tagPrecTy_glb ?_ ?_ ?_ (hgγb'.tys _) ?_ ?_ h2ty
      (emeetD_ty_spec (tagReorderD γl B) εd' c)
    · rw [emeetD_ty_toF]; exact hgX.tys k
    · exact TagD.goodTy_entry hgrlT _
    · exact TagD.goodTy_entry hgεd' _
    · cases hvεd' with
      | mk hr _ hh =>
          have := hh (meetDR (tagReorderD γl B).toF εd'.toF c)
          dsimp only [TagD.tag_r] at this
          have heq : (⟨εd'.r (meetDR (tagReorderD γl B).toF εd'.toF c), hr _⟩ : Fin γb'.n)
              = fR' c :=
            (Fin.ext (hfR' c)).symm
          rw [heq] at this
          exact this
    · -- the first origin: precision of erasures
      rw [emeetD_ty_toF, ← tagD_toF_ty]
      exact h1.1
  · rw [hfL k, hfL' c]; exact h1.2

/-! ## Assembly of the routed entries

Given a coupling between the entries of two routing evidences that, on each
pair of positive weight, relates the routed values, the evidences of the entries and
the targets, the coercions at the entries are simulated one by one and the resulting
configurations are related. The statement does not mention the operators,
so it serves rules (D::μ) and (Dlet) alike. -/
/-- Lemma 50 (precision of configurations is a congruence), item 3, for the
routed entries: if a coupling of the entries of two routing evidences relates, on
each pair of positive weight, the coerced values, the evidences of the entries and the
targets, then the configurations of the coerced entries are related. -/
theorem dgg_cells_assemble {Ep Ep' : FDist}
    {wv : Fin Ep.n → Val} {wv' : Fin Ep'.n → Val}
    {etag : Fin Ep.n → TagTy} {etag' : Fin Ep'.n → TagTy}
    {vsrc : Fin Ep.n → Val} {vsrc' : Fin Ep'.n → Val}
    {dst : Fin Ep.n → FTy} {dst' : Fin Ep'.n → FTy}
    (hv : ∀ k, ⊢ vsrc k : (vsrc k).tyEntry)
    (hv' : ∀ c, ⊢ vsrc' c : (vsrc' c).tyEntry)
    (hevR : ∀ k, etag k ⊩[.r] dst k)
    (hev' : ∀ c, etag' c ⊩ (vsrc' c).tyEntry ∼̇ dst' c)
    (hge : ∀ k, GoodTy (etag k).toF) (hge' : ∀ c, GoodTy (etag' c).toF)
    (hgdst' : ∀ c, GoodTy (dst' c))
    (hstep : ∀ k, .ascV (etag k) (vsrc k) (dst k) ⇓[1] DConf.point (wv k))
    (hstep' : ∀ c, .ascV (etag' c) (vsrc' c) (dst' c) ⇓[1] DConf.point (wv' c))
    (hcoup : SymLiftAll (fun k c =>
        vsrc k ⊑ vsrc' c ∧
        dst k ⊑ dst' c ⊢[.r] etag k ⊑̇ etag' c ∧
        dst k ⊑ dst' c) Ep.C Ep'.C) :
    ⟨Ep.n, wv, Ep.C⟩ ⊑ ⟨Ep'.n, wv', Ep'.C⟩ :=
  hcoup.mono fun k c ⟨hvv, hee, hσ⟩ =>
    dgg_cell_cond (hv k) (hv' c) (hevR k) (hev' c) (hge k) (hge' c)
      (hgdst' c) hvv hee hσ (hstep k) (hstep' c)


/-! ## The case of rule (D::μ)

The entrywise premises of the rule, the validity of the two routing evidences
entry by entry (`hvalidFor_dascD_evidence`) and the coupling of their entries
(`eprecD_routing_tags`) feed the assembler `dgg_cells_assemble`; everything
is stated over the entries of the routing evidences the rule computes. -/
/-- The case of rule (D::μ): the mixtures that the rule builds from related
ascribed terms, with related evidences, are related. -/
theorem dgg_dascD {εd εd' : TagD} {μ μ' μb μb' : FDist} {V0 V0' : DConf}
    (hev : TagPrecD .r εd εd' μb μb')
    {wv : Fin (emeetD (tagReorderD V0.confF μ) εd).n → Val}
    {wv' : Fin (emeetD (tagReorderD V0'.confF μ') εd').n → Val}
    (hR : ∀ c : Fin (emeetD (tagReorderD V0.confF μ) εd).n,
      (emeetD (tagReorderD V0.confF μ) εd).r c < μb.n)
    (hR' : ∀ c : Fin (emeetD (tagReorderD V0'.confF μ') εd').n,
      (emeetD (tagReorderD V0'.confF μ') εd').r c < μb'.n)
    (hcell : ∀ c, Red (.ascV ((emeetD (tagReorderD V0.confF μ) εd).ty c)
      (V0.val (reorderDL V0.confF μ (meetDL (tagReorderD V0.confF μ).toF εd.toF c)))
      (μb.ty ⟨_, hR c⟩)) 1 (DConf.point (wv c)))
    (hcell' : ∀ c, Red (.ascV ((emeetD (tagReorderD V0'.confF μ') εd').ty c)
      (V0'.val (reorderDL V0'.confF μ' (meetDL (tagReorderD V0'.confF μ').toF εd'.toF c)))
      (μb'.ty ⟨_, hR' c⟩)) 1 (DConf.point (wv' c)))
    (hgV0 : GoodD V0.confF) (hgμ : GoodD μ) (hgV0' : GoodD V0'.confF)
    (hgμ' : GoodD μ') (hgεd : GoodD εd.toF) (hgεd' : GoodD εd'.toF)
    (hgμb' : GoodD μb')
    (hgrp : GoodD (tagReorderD V0.confF μ).toF)
    (hgE : GoodD (emeetD (tagReorderD V0.confF μ) εd).toF)
    (hgE' : GoodD (emeetD (tagReorderD V0'.confF μ') εd').toF)
    (hvals : ∀ i, HasTyV [] (V0.val i) ((V0.val i).tyEntry))
    (hvals' : ∀ i, HasTyV [] (V0'.val i) ((V0'.val i).tyEntry))
    (hIH : DConfPrec V0 V0')
    (href : RefDist V0'.confF μ')
    (hrd : EReordD V0.confF μ) (hrdl : EReordD V0'.confF μ')
    (hvalR : HValid .r εd μb) (hvalR' : HValid .r εd' μb') :
    DConfPrec (DConf.wsumPoint (emeetD (tagReorderD V0.confF μ) εd).toF.C wv)
      (DConf.wsumPoint (emeetD (tagReorderD V0'.confF μ') εd').toF.C wv') := by
  have hvalid : (emeetD (tagReorderD V0.confF μ) εd).HValidFor V0.confF μb :=
    hvalidFor_dascD_evidence hgV0 hgμ hrd hvalR hgεd
  have hvalid' :
      (emeetD (tagReorderD V0'.confF μ') εd').HValidFor V0'.confF μb' :=
    hvalidFor_dascD_evidence hgV0' hgμ' hrdl hvalR' hgεd'
  refine dgg_cells_assemble
    (etag := (emeetD (tagReorderD V0.confF μ) εd).ty)
    (etag' := (emeetD (tagReorderD V0'.confF μ') εd').ty)
    (vsrc := fun c => V0.val (reorderDL V0.confF μ
      (meetDL (tagReorderD V0.confF μ).toF εd.toF c)))
    (vsrc' := fun c => V0'.val (reorderDL V0'.confF μ'
      (meetDL (tagReorderD V0'.confF μ').toF εd'.toF c)))
    (dst := fun c => μb.ty ⟨_, hR c⟩) (dst' := fun c => μb'.ty ⟨_, hR' c⟩)
    (fun c => hvals _) (fun c => hvals' _)
    (fun c => (hvalid.entryH (reorderDL _ _ _).isLt (hR c)).right)
    (fun c => hvalid'.entryH (reorderDL _ _ _).isLt (hR' c))
    (fun c => TagD.goodTy_entry hgE c) (fun c => TagD.goodTy_entry hgE' c)
    (fun c => hgμb'.tys _) hcell hcell' ?_
  refine SymLiftAll.mono
    (eprecD_routing_tags (Rval := fun i i' => PrecV [] [] (V0.val i) (V0'.val i'))
      (fL := fun c => reorderDL V0.confF μ (meetDL (tagReorderD V0.confF μ).toF εd.toF c))
      (fR := fun c => ⟨_, hR c⟩)
      (fL' := fun c => reorderDL V0'.confF μ' (meetDL (tagReorderD V0'.confF μ').toF εd'.toF c))
      (fR' := fun c => ⟨_, hR' c⟩)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hgV0 hgμ hgV0' hgεd hgεd' hgμ' hgμb' hgrp hgE hvalR' hrdl
      (fun i i' h => tyEntry_eprec h) (fun p hp => hIH p hp) href hev)
    fun k c ⟨hty, hval, hdst⟩ => ⟨hval, hty, hdst⟩

/-! ## Congruences of `DConfPrec` for the operations on configurations

The operations that build configurations preserve precision. The two
liftings are put side by side by `Lift.append`. -/


/-- One block of a binary mixture, with the relation required only when the
branch has positive probability: if `a = 0` the block's coupling is the product
coupling (`IsCoupling.prod`) and imposes nothing. -/
theorem block_cond {a : ℝ} {V1 V1' : DConf} (hg1 : GoodD V1.confF)
    (hg1' : GoodD V1'.confF) (h1 : 0 < a → DConfPrec V1 V1')
    (ha : 0 ≤ a) {p : Fin V1.n → ℝ} (hp : V1.C p) :
    ∃ p' : Fin V1'.n → ℝ, V1'.C p' ∧
      Lift (fun i j => 0 < a → PrecV [] [] (V1.val i) (V1'.val j)) p p' := by
  rcases eq_or_lt_of_le ha with h | h
  · obtain ⟨p', hp'⟩ := hg1'.good.sat
    exact ⟨p', hp', _, .prod (hg1.good.nonneg p hp) (hg1'.good.nonneg p' hp')
      (hg1.good.mass p hp) (hg1'.good.mass p' hp'), fun _ _ _ hpos => absurd h hpos.ne⟩
  · obtain ⟨p', hp', hl⟩ := h1 h p hp
    exact ⟨p', hp', hl.mono fun _ _ hR _ => hR⟩

/-- Lemma 50 (precision of configurations is a congruence), item 2: binary
mixtures with the same concrete probability preserve precision, each branch's
hypothesis required only when the branch has positive probability. -/
theorem dconfprec_choose_cond {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {V1 V1' V2 V2' : DConf}
    (hg1 : GoodD V1.confF) (hg1' : GoodD V1'.confF)
    (hg2 : GoodD V2.confF) (hg2' : GoodD V2'.confF)
    (h1 : 0 < a → V1 ⊑ V1') (h2 : a < 1 → V2 ⊑ V2') :
    DConf.choose a V1 V2 ⊑ DConf.choose a V1' V2' := by
  rintro x ⟨p, q, hp, hq, rfl⟩
  obtain ⟨p', hp', hl1⟩ := block_cond hg1 hg1' h1 ha0 hp
  obtain ⟨q', hq', hl2⟩ :=
    block_cond (a := 1 - a) hg2 hg2' (fun h => h2 (by linarith)) (by linarith) hq
  exact ⟨_, ⟨p', q', hp', hq', rfl⟩,
    (hl1.smul_of_pos ha0).append (hl2.smul_of_pos (sub_nonneg.2 ha1))
      (fun i j h => by simpa using h) (fun i j h => by simpa using h)⟩

/-- Lemma 50 (precision of configurations is a congruence), item 2: as
`dconfprec_choose_cond`, with a less precise mixture of unknown probability
(`DConf.chooseU`): the coupling of `dconfprec_choose_cond` ends in a solution of
`DConf.choose a`, which is one of the hull. -/
theorem dconfprec_choose_unk_cond {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {V1 V1' V2 V2' : DConf}
    (hg1 : GoodD V1.confF) (hg1' : GoodD V1'.confF)
    (hg2 : GoodD V2.confF) (hg2' : GoodD V2'.confF)
    (h1 : 0 < a → V1 ⊑ V1') (h2 : a < 1 → V2 ⊑ V2') :
    DConf.choose a V1 V2 ⊑ DConf.chooseU V1' V2' := by
  intro x hx
  obtain ⟨y, hy, hl⟩ := dconfprec_choose_cond ha0 ha1 hg1 hg1' hg2 hg2' h1 h2 x hx
  exact ⟨y, ⟨a, ha0, ha1, hy⟩, hl⟩

/-- Lemma 50 (precision of configurations is a congruence), item 2: mixtures of
unknown probability on both sides preserve precision. -/
theorem dconfprec_chooseU {V1 V1' V2 V2' : DConf}
    (h1 : V1 ⊑ V1') (h2 : V2 ⊑ V2') :
    DConf.chooseU V1 V2 ⊑ DConf.chooseU V1' V2' := by
  rintro x ⟨aa, ha0, ha1, p, q, hp, hq, rfl⟩
  obtain ⟨p', hp', hl1⟩ := h1 p hp
  obtain ⟨q', hq', hl2⟩ := h2 q hq
  exact ⟨_, ⟨aa, ha0, ha1, p', q', hp', hq', rfl⟩,
    (hl1.smul ha0).append (hl2.smul (sub_nonneg.2 ha1))
      (fun i j h => by simpa using h) (fun i j h => by simpa using h)⟩


/-! ## Inversion of the precision of ascribed values -/

/-- Inversion of the precision of an ascribed value: the less precise value
is an ascription and the four premises of rule `PrecV.asc` hold. -/
theorem tprecV_asc_inv : ∀ {ε : TagTy} {u : Raw} {σ : FTy} {v' : Val},
    PrecV [] [] (.asc ε u σ) v' →
    ∃ (ε' : TagTy) (u' : Raw) (σ' : FTy), v' = .asc ε' u' σ' ∧
      TagPrecTy .r σ σ' ε ε' ∧
      (∀ {τ τ' : FTy}, HasTyRaw [] u τ → HasTyRaw [] u' τ' →
        TagPrecTy .l τ τ' ε ε') ∧
      PrecRaw [] [] u u' ∧ PrecTy σ σ'
  | _, _, _, _, .asc hε hεL hu hσ => ⟨_, _, _, rfl, hε, hεL, hu, hσ⟩


/-! ## Simulation of one coercion without errors

When the precise result is not an error, the precise coercion composed, so
the less precise one composes too, both produce ascriptions and rule `errV` is not
involved. The conclusion adds that the less precise result is not an error
either. -/
/-- Lemma 49 (coercion of related values), error-free form: if the precise
coercion yields an ascription `w`, then the less precise coercion yields an
ascription `w'` with `w ⊑ w'`. -/
theorem dgg_cell_ef {e e' : TagTy} {v v' w : Val} {σt σt' : FTy}
    (hv : ⊢ v : v.tyEntry) (hv' : ⊢ v' : v'.tyEntry)
    (hevR : e ⊩[.r] σt) (hev' : e' ⊩ v'.tyEntry ∼̇ σt')
    (hge : GoodTy e.toF) (hge' : GoodTy e'.toF)
    (hvv : v ⊑ v') (hee : σt ⊑ σt' ⊢[.r] e ⊑̇ e')
    (hσ : σt ⊑ σt')
    (hstep : .ascV e v σt ⇓[1] DConf.point w)
    (hw : ∃ (ε : TagTy) (u : Raw) (σ : FTy), w = .asc ε u σ) :
    ∃ w', .ascV e' v' σt' ⇓[1] DConf.point w' ∧ w ⊑ w' ∧
      ∃ (ε : TagTy) (u : Raw) (σ : FTy), w' = .asc ε u σ := by
  obtain ⟨εw, uw, σw, rfl⟩ := hw
  have hco := red_ascV_iff.1 hstep
  cases v with
  | var x => exact nomatch hco
  | err σe => exact nomatch hco
  | asc ε1 u σv =>
    -- the precise coercion composed (otherwise its result is an error); so
    -- does the less precise one, by monotonicity
    rcases Val.coerce_asc_inv hco with ⟨ε3, hmeet, hgε3, hwk⟩ | ⟨-, hwk⟩
    · cases hwk
      cases hv with
      | ascRaw hu hev1 hge1 _ =>
        cases hvv with
        | asc hε1 hε1L hu' hσv =>
          rename_i ε1' u2 σv2
          cases hv' with
          | ascRaw hu2 hev1' hge1' _ =>
            obtain ⟨m', hm', hgm', hmm'⟩ :=
              meetTy_mono hge1 hge hge1' hge' (TagPrecTy.toEPrecTy hε1)
                (TagPrecTy.toEPrecTy hee) (emeetTy_toF_some hmeet) hgε3
            obtain ⟨e3t', hme3', hetoF'⟩ := emeetTy_some_of_meetTy hm'
            refine ⟨.asc e3t' u2 σt',
              Red.dascOk hme3' (by rw [hetoF']; exact hgm'), ?_, _, _, _, rfl⟩
            refine PrecV.asc ?_ ?_ hu' hσ
            · exact tagPrecTy_emeetTy hge hge1 hge' hge1'
                hevR hev'.right hee (TagPrecTy.toEPrecTy hε1) hmeet hme3' hgε3
            · intro σu σu' hty1 hty2
              obtain rfl := hasTy_closed_det_raw hu hty1
              obtain rfl := hasTy_closed_det_raw hu2 hty2
              exact tagPrecTy_emeetTy hge1 hge hge1' hge'
                hev1.left hev1'.left
                (hε1L hu hu2)
                (TagPrecTy.toEPrecTy hee) hmeet hme3' hgε3
    · exact nomatch hwk


/-! ## Error-freeness of configurations -/


/-- An error configuration (of a well-formed type) is never error-free. -/
theorem not_errFree_errAt {γ : FDist} (hg : GoodD γ) :
    ¬ ErrFree (DConf.errAt γ) := by
  intro h
  obtain ⟨p, hp⟩ := hg.good.sat
  obtain ⟨c, hc⟩ := exists_pos_of_sum_pos (f := p) (by rw [hg.good.mass p hp]; exact one_pos)
  obtain ⟨ε, u, σ, hcc⟩ := h p hp c hc
  exact nomatch hcc

/-! ## Auxiliary facts for the rules without routing -/


/-- A value ascription that reduces at some index reduces at index 1. -/
theorem red_ascV_index_one {e : TagTy} {v : Val} {σ : FTy} {k : ℕ} {V : DConf}
    (h : Red (.ascV e v σ) k V) : Red (.ascV e v σ) 1 V := by
  obtain ⟨w, hw, rfl⟩ := red_ascV_coerce h
  exact red_ascV_of_coerce hw

/-- A distribution error reduces only to its error configuration. -/
theorem red_errD_inv : ∀ {μ : FDist} {k : ℕ} {V : DConf},
    Red (.errD μ) k V → V = DConf.errAt μ
  | _, _, _, .derr => rfl
  | _, _, _, .dmon h0 => red_errD_inv h0

/-! ## Weighted sums of configurations

Two weighted sums whose summands are coupled, with coupled branches related,
are related. The coupling of the sums is the product of the coupling of the
summands with the coupling of each branch (`Lift.sigmaFin`), and the less precise
solution of a branch is the convex combination, weighted by the coupling, of
the solutions that the coupled precise branches propose; hence the convexity
hypothesis `hconv`, which the formulas of well-typed configurations satisfy. -/

/-- The outcome `(k, i)` of a weighted sum holds the value of the outcome `i` of the
branch `k`. -/
theorem DConf.wsum_val {K : ℕ} (W : (Fin K → ℝ) → Prop) (Vk : Fin K → DConf) (k : Fin K)
    (i : Fin (Vk k).n) : (DConf.wsum W Vk).val (finSigmaFinEquiv ⟨k, i⟩) = (Vk k).val i := by
  show (Vk (finSigmaFinEquiv.symm
    (finSigmaFinEquiv (⟨k, i⟩ : (k : Fin K) × Fin (Vk k).n))).1).val _ = _
  rw [Equiv.symm_apply_apply]

/-- Lemma 50 (precision of configurations is a congruence), item 3: if the less
precise branches have nonempty convex solution sets and, for every solution `ω`
of `W`, a solution `ω'` of `W'` and a coupling of them relate the branches on
every pair of positive weight, then the weighted sums are related. -/
theorem dconfprec_wsum {K K' : ℕ} {W : (Fin K → ℝ) → Prop}
    {W' : (Fin K' → ℝ) → Prop} {Vk : Fin K → DConf} {Vk' : Fin K' → DConf}
    (hconv : ∀ c, ∀ p r, (Vk' c).C p → (Vk' c).C r → ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      (Vk' c).C (fun i => a * p i + (1 - a) * r i))
    (hsat' : ∀ c, ∃ p, (Vk' c).C p)
    (hcoup : SymLiftAll (fun k c => Vk k ⊑ Vk' c) W W') :
    DConf.wsum W Vk ⊑ DConf.wsum W' Vk' := by
  rintro x ⟨ω, hW, b, hb, hx⟩
  obtain rfl : x = _ := funext hx
  obtain ⟨ω', hW', t, ht, hs⟩ := hcoup ω hW
  -- for each pair of summands of positive weight, the less precise solution that
  -- precision proposes (any solution for the pairs of weight zero)
  have hpair : ∀ k c, ∃ r : Fin (Vk' c).n → ℝ, (Vk' c).C r ∧ (0 < t k c →
      Lift (fun i j => PrecV [] [] ((Vk k).val i) ((Vk' c).val j)) (b k) r) := by
    intro k c
    by_cases hkc : 0 < t k c
    · obtain ⟨r, hr, hl⟩ := hs k c hkc (b k) (hb k (ht.left_pos hkc))
      exact ⟨r, hr, fun _ => hl⟩
    · obtain ⟨r, hr⟩ := hsat' c
      exact ⟨r, hr, fun h => absurd h hkc⟩
  choose r hr hl using hpair
  -- the less precise solution of a branch is the convex combination of the
  -- proposed solutions, and the product coupling `Lift.sigmaFin` relates the sums
  refine ⟨_, ⟨ω', hW', fun c j => ∑ k, t k c / ω' c * r k c j, fun c hc => ?_, fun cj => ?_⟩,
    Lift.sigmaFin (R := fun k c => 0 < t k c) ht (fun _ _ h => h) hl fun k c i j _ h => ?_⟩
  · refine convexC_sum (hconv c) (fun k => t k c / ω' c) (fun k => r k c)
      (fun k => div_nonneg (ht.nonneg k c) hc.le) ?_ (fun k => hr k c)
    rw [← Finset.sum_div, ht.col c, div_self hc.ne']
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, mul_comm (ω' _), div_mul_cancel_of_imp fun h => ht.eq_zero_of_right h k]
  · rw [DConf.wsum_val, DConf.wsum_val]
    exact h


/-! ## Coupling of the routing entries of `let` -/

/-- The routing evidence of rule (Dlet) is a plain reordering. Given a
coupling of the bound terms' configurations whose support satisfies `Rval`,
this builds a coupling between the entries of the two reorderings that, on
each pair of positive weight, relates the routed values (left tags), the
evidences of the entries against the targets (tag-aware precision) and the targets
(type precision). -/
theorem eprecD_letrouting_tags {γp γl μ B : FDist}
    {Rval : Fin γp.n → Fin γl.n → Prop}
    (hgγp : GoodD γp) (hgμ : GoodD μ) (hgγl : GoodD γl)
    (hgrp : GoodD (reorderD γp μ))
    (hRval : ∀ i i', Rval i i' → PrecTy (γp.ty i) (γl.ty i'))
    (hrun : SymLiftAll Rval γp.C γl.C)
    (href : RefDist γl B) :
    SymLiftAll (fun k c =>
        Rval (reorderDL γp μ k) (reorderDL γl B c) ∧
        TagPrecTy .r (μ.ty (reorderDR γp μ k)) (B.ty (reorderDR γl B c))
          ((tagReorderD γp μ).ty k) ((tagReorderD γl B).ty c) ∧
        PrecTy (μ.ty (reorderDR γp μ k)) (B.ty (reorderDR γl B c)))
      (reorderD γp μ).C (reorderD γl B).C := by
  have hEL : TagPrec (reorderD γp μ) γp (reorderDL γp μ) := tagPrec_reorderD .l hgγp hgμ
  refine SymLiftAll.mono
    (eprec_reorderD_glb_align
      (R1 := fun k i' => Rval (reorderDL γp μ k) i')
      hgγp hgμ hgγl (fun k i' h => hRval _ _ h)
      (coup_comp_fun (R := Rval) hEL hgrp.good hrun) href)
    fun k c ⟨hval, _, htag, hdst⟩ => ⟨hval, htag, hdst⟩

/-! ## The entries of rule (Dlet)

The coercions at the entries are compared with `dgg_cell_cond`, fed by the coupling of
`eprecD_letrouting_tags`. The validity of the evidence at each entry comes from the
hereditary validity of the tagged reordering, and the types of the values
from type safety. -/

/-- Validity along `π`, entry by entry, of the tagged reordering. -/
theorem tagReorderD_entry (π : Side) {D1 D2 : FDist} (hg1 : GoodD D1) (hg2 : GoodD D2)
    (c : Fin (reorderD D1 D2).n) :
    HVTag π ((tagReorderD D1 D2).ty c) ((π.pick D1 D2).ty (witnessTag Eq D1 D2 π c)) := by
  obtain ⟨hL, hR⟩ := hvalid_tagReorderD hg1 hg2
  cases π
  · cases hL with
    | mk _ _ hh => exact hh c
  · cases hR with
    | mk _ _ hh => exact hh c

/-- The result of a value ascription has the target type (in both the success
and the failure case). -/
theorem red_ascV_result_typed {ε : TagTy} {v : Val} {σt : FTy} {w : Val}
    (hty : HasTyT [] (.ascV ε v σt) (pointF σt))
    (h : Red (.ascV ε v σt) 1 (DConf.point w)) : HasTyV [] w σt := by
  obtain ⟨hvals, -, -⟩ := type_safety h hty
  have hw := hvals ⟨0, Nat.one_pos⟩
  have hval : (DConf.point w).val ⟨0, Nat.one_pos⟩ = w := rfl
  rw [hval] at hw
  rwa [tyEntry_of_red_ascV h] at hw

/-- Typing of the ascription that rule (Dlet) performs at each entry. -/
theorem hasTy_letcell {D1 D2 : FDist} {V0 : DConf} (hg1 : GoodD D1)
    (hg2 : GoodD D2) (hgr : GoodD (reorderD D1 D2))
    (hvals : ∀ i, HasTyV [] (V0.val i) ((V0.val i).tyEntry))
    (hconf : V0.confF = D1) (c : Fin (reorderD D1 D2).n) :
    HasTyT [] (.ascV ((tagReorderD D1 D2).ty c)
      (V0.val (Fin.cast (congrArg FDist.n hconf).symm (reorderDL D1 D2 c)))
      (D2.ty (reorderDR D1 D2 c)))
      (pointF (D2.ty (reorderDR D1 D2 c))) := by
  have hL : HVTag .l _ (D1.ty (reorderDL D1 D2 c)) := tagReorderD_entry .l hg1 hg2 c
  have heq : D1.ty (reorderDL D1 D2 c)
      = (V0.val (Fin.cast (congrArg FDist.n hconf).symm
          (reorderDL D1 D2 c))).tyEntry := by
    subst hconf; rfl
  rw [heq] at hL
  exact HasTyT.ascV (hvals _) ⟨hL, tagReorderD_entry .r hg1 hg2 c⟩
    (by rw [tagReorderD_ty_toF D1 D2 c]; exact hgr.tys c) (hg2.tys _)

/-- The weighted sums produced by rule (Dlet) on both sides are related, given
the coercions at the entries and a hypothesis `hbranch` relating the branches of
coupled entries. -/
theorem dgg_dlet_cells {μ μ' : FDist} {V0 V0' : DConf}
    {wv : Fin (reorderD V0.confF μ).n → Val}
    {wv' : Fin (reorderD V0'.confF μ').n → Val}
    {Vk : Fin (reorderD V0.confF μ).n → DConf}
    {Vk' : Fin (reorderD V0'.confF μ').n → DConf}
    (hgV0 : GoodD V0.confF) (hgμ : GoodD μ)
    (hgV0' : GoodD V0'.confF) (hgμ' : GoodD μ')
    (hgrp : GoodD (reorderD V0.confF μ))
    (hgrp' : GoodD (reorderD V0'.confF μ'))
    (hvals : ∀ i, HasTyV [] (V0.val i) ((V0.val i).tyEntry))
    (hvals' : ∀ i, HasTyV [] (V0'.val i) ((V0'.val i).tyEntry))
    (hstep : ∀ k, Red (.ascV ((tagReorderD V0.confF μ).ty k)
      (V0.val (reorderDL V0.confF μ k)) (μ.ty (reorderDR V0.confF μ k))) 1
      (DConf.point (wv k)))
    (hstep' : ∀ c, Red (.ascV ((tagReorderD V0'.confF μ').ty c)
      (V0'.val (reorderDL V0'.confF μ' c)) (μ'.ty (reorderDR V0'.confF μ' c))) 1
      (DConf.point (wv' c)))
    (hIH : DConfPrec V0 V0')
    (href : RefDist V0'.confF μ')
    (hbranch : ∀ k c, PrecV [] [] (wv k) (wv' c) →
      PrecTy (μ.ty (reorderDR V0.confF μ k)) (μ'.ty (reorderDR V0'.confF μ' c)) →
      (∃ ω, (reorderD V0.confF μ).C ω ∧ 0 < ω k) →
      DConfPrec (Vk k) (Vk' c))
    (hconv : ∀ c', ∀ p r, (Vk' c').C p → (Vk' c').C r → ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      (Vk' c').C (fun i => a * p i + (1 - a) * r i))
    (hsat' : ∀ c', ∃ p, (Vk' c').C p) :
    DConfPrec (DConf.wsum (reorderD V0.confF μ).C Vk)
      (DConf.wsum (reorderD V0'.confF μ').C Vk') := by
  refine dconfprec_wsum hconv hsat' ?_
  intro ω hω
  obtain ⟨ω', hω', t, ht, hs⟩ :=
    eprecD_letrouting_tags (Rval := fun i i' => PrecV [] [] (V0.val i) (V0'.val i'))
      hgV0 hgμ hgV0' hgrp
      (fun i i' h => tyEntry_prec h (not_var_of_closed (hvals i)))
      (fun p hp => hIH p hp) href ω hω
  refine ⟨ω', hω', t, ht, fun k c hpos => ?_⟩
  obtain ⟨hval, htag, hdst⟩ := hs k c hpos
  -- the coercion at the entry, simulated
  have hcoerce : PrecV [] [] (wv k) (wv' c) :=
    dgg_cell_cond (hvals _) (hvals' _)
      (tagReorderD_entry .r hgV0 hgμ k)
      ⟨tagReorderD_entry .l hgV0' hgμ' c, tagReorderD_entry .r hgV0' hgμ' c⟩
      (by rw [tagReorderD_ty_toF V0.confF μ k]; exact hgrp.tys k)
      (by rw [tagReorderD_ty_toF V0'.confF μ' c]; exact hgrp'.tys c)
      (hgμ'.tys _) hval htag hdst (hstep k) (hstep' c)
  exact hbranch k c hcoerce hdst ⟨ω, hω, ht.left_pos hpos⟩

/-! ## Inversion of the reduction of the less precise term

Theorem 5 is stated for a given reduction of the less precise term. The cases
below invert that reduction according to the shape of the term. -/

/-- A value reduces only to its Dirac configuration. -/
theorem red_val_inv : ∀ {v : Val} {k : ℕ} {V : DConf},
    Red (.val v) k V → V = DConf.point v
  | _, _, _, .dv => rfl
  | _, _, _, .dmon h0 => red_val_inv h0

/-- Inversion of the reduction of a choice: rule (D⊕) reduces both branches,
at a concrete probability or at the unknown probability. -/
theorem red_choice_inv : ∀ {p : GProb} {m n : Tm} {k : ℕ} {V : DConf},
    Red (.choice p m n) k V →
    (∃ (a : ℝ) (k1 k2 : ℕ) (V1 V2 : DConf), 0 ≤ a ∧ a ≤ 1 ∧ p = .q a ∧
      Red m k1 V1 ∧ Red n k2 V2 ∧ V = DConf.choose a V1 V2) ∨
    (∃ (k1 k2 : ℕ) (V1 V2 : DConf), p = .unk ∧
      Red m k1 V1 ∧ Red n k2 V2 ∧ V = DConf.chooseU V1 V2)
  | _, _, _, _, _, .dchoice ha0 ha1 h1 h2 =>
      .inl ⟨_, _, _, _, _, ha0, ha1, rfl, h1, h2, rfl⟩
  | _, _, _, _, _, .dchoiceU h1 h2 => .inr ⟨_, _, _, _, rfl, h1, h2, rfl⟩
  | _, _, _, _, _, .dmon h0 => red_choice_inv h0

/-- Inversion of the reduction of an addition of two ascribed reals: the
evidences compose and the result is the Dirac on the ascribed sum. -/
theorem red_add_real_inv : ∀ {ε1 ε2 : TagTy} {r1 r2 : ℝ} {k : ℕ} {V : DConf},
    Red (.add (.asc ε1 (.real r1) .real) (.asc ε2 (.real r2) .real)) k V →
    ∃ ε3, emeetTy ε1 ε2 = some ε3 ∧
      V = DConf.point (.asc ε3 (.real (r1 + r2)) .real)
  | _, _, _, _, _, _, .dadd hm => ⟨_, hm, rfl⟩
  | _, _, _, _, _, _, .dmon h0 => red_add_real_inv h0

/-- A value ascription reduces only to a Dirac configuration. -/
theorem red_ascV_point_inv {e : TagTy} {v : Val} {σ : FTy} {k : ℕ}
    {V : DConf} (h : Red (.ascV e v σ) k V) : ∃ w, V = DConf.point w :=
  (red_ascV_coerce h).imp fun _ => And.right

/-- Inversion of the reduction of a conditional: on `true` it reduces the
first branch, on `false` the second, and on an error it yields the error at
the hull of the branch types. -/
theorem red_ite_inv : ∀ {v : Val} {m n : Tm} {k : ℕ} {V : DConf},
    Red (.ite v m n) k V →
    (∃ (ε : TagTy) (k1 : ℕ), v = .asc ε (.bool true) .bool ∧ Red m k1 V) ∨
    (∃ (ε : TagTy) (k1 : ℕ), v = .asc ε (.bool false) .bool ∧ Red n k1 V) ∨
    (∃ (σ : FTy) (D1 D2 : FDist), v = .err σ ∧ V = DConf.errAt (chooseSemU D1 D2))
  | _, _, _, _, _, .dit h => .inl ⟨_, _, rfl, h⟩
  | _, _, _, _, _, .dif h => .inr (.inl ⟨_, _, rfl, h⟩)
  | _, _, _, _, _, .eIte _ _ => .inr (.inr ⟨_, _, _, rfl, rfl⟩)
  | _, _, _, _, _, .dmon h0 => red_ite_inv h0


/-- Inversion of the reduction of an application. -/
theorem red_app_inv : ∀ {fn v : Val} {k : ℕ} {V : DConf}, Red (.app fn v) k V →
    (∃ (ε : TagTy) (σ' : FTy) (m : Tm) (σa : FTy) (Dres : FDist) (s : TagTy)
       (d : TagD) (k1 k2 : ℕ) (w : Val),
      fn = .asc ε (.lam σ' m) (.arrow σa Dres) ∧
      tagDom ε = some s ∧ tagCod ε = some d ∧
      Red (.ascV s v σ') k1 (DConf.point w) ∧
      Red ((Tm.ascT d m Dres).subErr w Dres) k2 V) ∨
    (∃ (σa : FTy) (D : FDist), fn = .err (.arrow σa D) ∧ V = DConf.errAt D)
  | _, _, _, _, .dapp hd hc h1 h2 =>
      .inl ⟨_, _, _, _, _, _, _, _, _, _, rfl, hd, hc, h1, h2⟩
  | _, _, _, _, .eApp => .inr ⟨_, _, rfl, rfl⟩
  | _, _, _, _, .dmon h0 => red_app_inv h0

/-- The case of rule (Dapp). If the precise result is error-free, the
coercion of the argument composed (otherwise `subErr` would make the whole body
an error), so the coerced argument is an ascription. `dgg_cell_cond` relates it
to the less precise coerced argument, which is therefore an ascription as
well. The two contracta (the bodies ascribed by the codomain evidences, with
the coerced arguments substituted) are related by `prec_subst0`, and the
induction hypothesis on the body concludes. -/
theorem dgg_app_cond {s0 : TagTy} {d0 : TagD} {σ' : FTy} {m : Tm} {σa : FTy}
    {Dres : FDist} {v : Val} {k1 k2 : ℕ} {w : Val} {V : DConf}
    (hargred : Red (.ascV s0.flip v σ') k1 (DConf.point w))
    (hbodyred : Red ((Tm.ascT d0 m Dres).subErr w Dres) k2 V)
    (hef : ErrFree V)
    {fn' v' : Val} {Dr Dr' : FDist} {kL : ℕ} {VL : DConf}
    (hredL : Red (.app fn' v') kL VL)
    (hty : HasTyT [] (.app (.asc (.arrow s0 d0) (.lam σ' m) (.arrow σa Dres)) v)
      Dr)
    (hty' : HasTyT [] (.app fn' v') Dr')
    (hpf : PrecV [] [] (.asc (.arrow s0 d0) (.lam σ' m) (.arrow σa Dres)) fn')
    (hpv : PrecV [] [] v v')
    (hIHb : ∀ {n'' : Tm} {kb : ℕ} {Vb : DConf} {Dm Dm' : FDist},
      Red n'' kb Vb →
      HasTyT [] ((Tm.ascT d0 m Dres).subErr w Dres) Dm →
      HasTyT [] n'' Dm' →
      PrecT [] [] ((Tm.ascT d0 m Dres).subErr w Dres) n'' → DConfPrec V Vb) :
    DConfPrec V VL := by
  cases hty with
  | app hfn hv =>
  cases hfn with
  | ascRaw hlam hevε hgε hgarr =>
  cases hlam with
  | lam hmty hgσ' =>
  obtain ⟨hevL, hevR⟩ := hevε
  cases hevL with
  | arrow hLs0 hLd0 =>
  cases hevR with
  | arrow hRs0 hRd0 =>
  cases hgε with
  | arrow hgs0 hgd0 =>
  cases hgarr with
  | arrow hgσa hgDres =>
  have hargred1 := red_ascV_index_one hargred
  obtain rfl : v.tyEntry = σa := tyEntry_of_hasTy hv
  have hwty0 : HasTyV [] w σ' :=
    cell_coercion_typed hv ⟨hvtag_flip hRs0, hvtag_flip hLs0⟩
      (by rw [TagTy.flip_toF]; exact hgs0) hgσ' hargred1
  obtain ⟨εw, uw, σw, rfl⟩ : ∃ (ε : TagTy) (u : Raw) (σ : FTy),
      w = .asc ε u σ := by
    cases w with
    | asc ε u σ => exact ⟨ε, u, σ, rfl⟩
    | var x => cases hwty0 with | var hx => simp at hx
    | err σ =>
        rw [Tm.subErr_err] at hbodyred
        rw [red_errD_inv hbodyred] at hef
        exact absurd hef (not_errFree_errAt hgDres)
  -- the less precise function is, by precision, an ascribed λ
  obtain ⟨ε', ulam', σf', rfl, hpεR, hpεL, hplam, hpσf⟩ := tprecV_asc_inv hpf
  cases hplam with
  | @lam _ _ _ σ'2 _ m2 hpσ' hpm =>
  cases hty' with
  | app hfn' hv' =>
  cases hfn' with
  | ascRaw hlam' hevε' hgε' hgarr' =>
  cases hlam' with
  | lam hm2ty hgσ'2 =>
  obtain ⟨hevL', hevR'⟩ := hevε'
  cases hevR' with
  | @arrow s0' d0' _ _ hRs0' hRd0' =>
  cases hevL' with
  | arrow hLs0' hLd0' =>
  cases hgε' with
  | arrow hgs0' hgd0' =>
  cases hgarr' with
  | arrow hgσa' hgDres' =>
  cases hpσf with
  | arrow hpσa hpDres =>
  obtain rfl : v'.tyEntry = _ := tyEntry_of_hasTy hv'
  -- the less precise reduction is that of an application with arrow evidence
  rcases red_app_inv hredL with
    ⟨ε2, σ2, m3, σa2, D2, s2, d2, k1', k2', w2, heqfn, hdom2, hcod2,
      hargred2, hbodyred2⟩ | ⟨σa2, D2, heqfn, -⟩
  · -- the syntactic shape fixes the less precise evidence and body
    cases heqfn
    obtain rfl : s2 = s0'.flip := by
      simp only [tagDom, Option.some.injEq] at hdom2; exact hdom2.symm
    obtain rfl : d2 = d0' := by
      simp only [tagCod, Option.some.injEq] at hcod2; exact hcod2.symm
    -- the coercion of the argument: both steps are given
    have hflipR :=
      TagPrecTy.flip (hpεL (.lam hmty hgσ')
        (.lam hm2ty hgσ'2)).arrow_inv.1
    have hww' : PrecV [] [] (.asc εw uw σw) _ :=
      dgg_cell_cond hv hv' (hvtag_flip hLs0)
        ⟨hvtag_flip hRs0', hvtag_flip hLs0'⟩
        (by rw [TagTy.flip_toF]; exact hgs0)
        (by rw [TagTy.flip_toF]; exact hgs0') hgσ'2 hpv hflipR hpσ'
        hargred1 (red_ascV_index_one hargred2)
    have hw'ty :=
      cell_coercion_typed hv' ⟨hvtag_flip hRs0', hvtag_flip hLs0'⟩
        (by rw [TagTy.flip_toF]; exact hgs0') hgσ'2 (red_ascV_index_one hargred2)
    obtain ⟨εw2, uw2, σw2, rfl⟩ : ∃ (ε : TagTy) (u : Raw) (σ : FTy),
        w2 = .asc ε u σ := by
      obtain ⟨e2, u2, s2, heq, -, -, -, -⟩ := tprecV_asc_inv hww'
      exact ⟨e2, u2, s2, heq⟩
    -- the ascribed bodies, substituted and related
    have hmsub : HasTyT [] (m.subst0 (.asc εw uw σw)) _ :=
      hasTy_subst0_tm hwty0 hmty
    have hmsub' : HasTyT [] (m2.subst0 (.asc εw2 uw2 σw2)) _ :=
      hasTy_subst0_tm hw'ty hm2ty
    rw [Tm.subErr_asc] at hbodyred2
    refine hIHb hbodyred2
      (hasTy_subst0_tm hwty0 (.ascT hmty ⟨hLd0, hRd0⟩ hgd0 hgDres))
      (hasTy_subst0_tm hw'ty (.ascT hm2ty ⟨hLd0', hRd0'⟩ hgd0' hgDres')) ?_
    rw [Tm.subErr_asc]
    simp only [Tm.subst0, Tm.subst]
    refine PrecT.ascT ?_ ?_ (prec_subst0 hpm hww' hwty0 hw'ty) hpDres
    · intro D1 D2x ht1 ht2
      exact hpεR.arrow_inv.2
    · intro D1 D2x ht1 ht2
      obtain rfl := hasTy_closed_det_tm (hasTy_subst0_tm hwty0 hmty) ht1
      obtain rfl := hasTy_closed_det_tm (hasTy_subst0_tm hw'ty hm2ty) ht2
      exact (hpεL (.lam hmty hgσ')
        (.lam hm2ty hgσ'2)).arrow_inv.2
  · -- the less precise function cannot be an error: it is an ascription
    exact nomatch heqfn


/-- Inversion of the reduction of a distribution ascription. -/
theorem red_ascT_inv : ∀ {εd : TagD} {m : Tm} {μb : FDist} {k : ℕ}
    {V : DConf}, Red (.ascT εd m μb) k V →
    (∃ (μ : FDist) (k1 : ℕ) (V0 : DConf)
       (hR : ∀ c : Fin (emeetD (tagReorderD V0.confF μ) εd).n,
         (emeetD (tagReorderD V0.confF μ) εd).r c < μb.n)
       (wv : Fin (emeetD (tagReorderD V0.confF μ) εd).n → Val),
      Red m k1 V0 ∧ HasTyT [] m μ ∧
      (∃ w, (emeetD (tagReorderD V0.confF μ) εd).toF.C w) ∧
      (∀ c, Red (.ascV ((emeetD (tagReorderD V0.confF μ) εd).ty c)
        (V0.val (reorderDL V0.confF μ (meetDL (tagReorderD V0.confF μ).toF εd.toF c)))
        (μb.ty ⟨_, hR c⟩)) 1 (DConf.point (wv c))) ∧
      V = DConf.wsumPoint (emeetD (tagReorderD V0.confF μ) εd).toF.C wv) ∨
    (∃ (μ : FDist) (k1 : ℕ) (V0 : DConf), Red m k1 V0 ∧ HasTyT [] m μ ∧
      ¬ (∃ w, (emeetD (tagReorderD V0.confF μ) εd).toF.C w) ∧
      V = DConf.errAt μb)
  | _, _, _, _, _, .dascD hvR hr ht hsat hcell =>
      .inl ⟨_, _, _, (fun c => emeetD_r_lt_of_hvalid hvR.2 c), _, hr, ht, hsat, hcell, rfl⟩
  | _, _, _, _, _, .dascDErr _ hr ht hns => .inr ⟨_, _, _, hr, ht, hns, rfl⟩
  | _, _, _, _, _, .dmon h0 => red_ascT_inv h0


/-- The case of rule (D::μ). The less precise reduction is inverted: its failure case
contradicts the satisfiability that `dascD_less_precise_defined` transports from the
precise side, so it composed, and its steps at each entry are those that `dgg_dascD`
requires. -/
theorem dgg_dascD_cond {εd εd' : TagD} {m m' : Tm} {μ μb μb' : FDist}
    {k1 kL : ℕ} {V0 : DConf} {VL : DConf}
    {wv : Fin (emeetD (tagReorderD V0.confF μ) εd).n → Val}
    (hR : ∀ c : Fin (emeetD (tagReorderD V0.confF μ) εd).n,
      (emeetD (tagReorderD V0.confF μ) εd).r c < μb.n)
    (hrm : Red m k1 V0) (htm : HasTyT [] m μ)
    (hsat : ∃ w, (emeetD (tagReorderD V0.confF μ) εd).toF.C w)
    (hcell : ∀ c, Red (.ascV ((emeetD (tagReorderD V0.confF μ) εd).ty c)
      (V0.val (reorderDL V0.confF μ (meetDL (tagReorderD V0.confF μ).toF εd.toF c)))
      (μb.ty ⟨_, hR c⟩)) 1 (DConf.point (wv c)))
    (hredL : Red (.ascT εd' m' μb') kL VL)
    (hty : HasTyT [] (.ascT εd m μb) μb)
    (hty' : HasTyT [] (.ascT εd' m' μb') μb')
    (hpεR : ∀ {D D' : FDist}, HasTyT [] m D → HasTyT [] m' D' →
      TagPrecD .r εd εd' μb μb')
    (hIH : ∀ {kx : ℕ} {Vx : DConf}, Red m' kx Vx → DConfPrec V0 Vx) :
    DConfPrec (DConf.wsumPoint (emeetD (tagReorderD V0.confF μ) εd).toF.C wv)
      VL := by
  cases hty with
  | @ascT _ _ _ μ0 _ htm0 hvalid hgεd hgμb =>
  cases hty' with
  | @ascT _ _ _ μ2 _ htm' hvalid' hgεd' hgμb' =>
  obtain rfl : μ = μ0 := det_tm htm htm0
  obtain ⟨hvals, hgV0, hrefV0⟩ := type_safety hrm htm
  have hgμ : GoodD μ := wf_tm htm ctxGood_nil
  have hgμ' : GoodD μ2 := wf_tm htm' ctxGood_nil
  have hrd : EReordD V0.confF μ :=
    reorderD_sat_iff_ereordD.mp (reorderD_sat_of_refDist hgV0.good.sat hrefV0)
  have hgrp : GoodD (tagReorderD V0.confF μ).toF := goodD_tagReorderD_toF hgV0 hgμ hrd
  have hgE : GoodD (emeetD (tagReorderD V0.confF μ) εd).toF :=
    goodD_emeetD_sat hgrp hgεd hsat
  rcases red_ascT_inv hredL with
    ⟨μ3, k1', V0'', hR', wv', hrm', htm3, hsat', hcell', rfl⟩ |
    ⟨μ3, k1', V0'', hrm', htm3, hns, rfl⟩
  · obtain rfl := det_tm htm3 htm'
    obtain ⟨hvals', hgV0', hrefV0'⟩ := type_safety hrm' htm3
    have hrdl := reorderD_sat_iff_ereordD.mp
      (reorderD_sat_of_refDist hgV0'.good.sat hrefV0')
    have hgE' := goodD_emeetD_sat (goodD_tagReorderD_toF hgV0' hgμ' hrdl) hgεd' hsat'
    exact dgg_dascD (hpεR htm htm3) hR hR'
      hcell hcell' hgV0 hgμ hgV0' hgμ' hgεd hgεd' hgμb' hgrp hgE hgE'
      hvals hvals' (hIH hrm') hrefV0' hrd hrdl hvalid.2 hvalid'.2
  · obtain rfl := det_tm htm3 htm'
    obtain ⟨hvals', hgV0', hrefV0'⟩ := type_safety hrm' htm3
    exact absurd (dascD_less_precise_defined hgV0 hgμ hgV0' hgεd hgrp hgE
      (eprecD_confF_of_dconfprec (hIH hrm')) hrefV0'
      ((hpεR htm htm3)).toEPrecD hsat) hns


/-- Inversion of the reduction of a `let`: the only rule is (Dlet). The typing
of the bound term is a hypothesis, so that its type `μ` (which rule (Dlet)
exposes as components) is a parameter. -/
theorem red_letin_inv : ∀ {m : Tm} {μ : FDist} {ns : Fin μ.n → Tm} {k : ℕ} {V : DConf},
    Red (.letin m μ.n ns) k V → HasTyT [] m μ →
    ∃ (k1 k2 : ℕ) (V0 : DConf)
      (wv : Fin (tagReorderD V0.confF μ).n → Val)
      (Vk : Fin (tagReorderD V0.confF μ).n → DConf)
      (Fb : Fin (tagReorderD V0.confF μ).n → FDist),
      Red m k1 V0 ∧
      (∀ c, Red (.ascV ((tagReorderD V0.confF μ).ty c)
        (V0.val (reorderDL V0.confF μ c)) (μ.ty (reorderDR V0.confF μ c))) 1
        (DConf.point (wv c))) ∧
      (∀ c, HasTyT [μ.ty (reorderDR V0.confF μ c)] (ns (reorderDR V0.confF μ c)) (Fb c)) ∧
      (∀ c, Red ((ns (reorderDR V0.confF μ c)).subErr (wv c) (Fb c)) k2 (Vk c)) ∧
      V = DConf.wsum (tagReorderD V0.confF μ).toF.C Vk
  | _, ⟨_, _, _⟩, _, _, _, .dlet hr ht hcell hbty hbred, hμ => by
      injection det_tm hμ ht with _ hty hC
      subst hty hC
      exact ⟨_, _, _, _, _, _, hr, hcell, hbty, hbred, rfl⟩
  | _, _, _, _, _, .dmon h0, hμ => red_letin_inv h0 hμ


/-! ## The case of rule (Dlet)

The coupling of entries (`eprecD_letrouting_tags`) gives, on each pair of
positive weight, related routed values and related branches; the
coercions at the entries are compared with `dgg_cell_cond`, the bodies with
`dgg_dlet_branch_cond`, and `dconfprec_wsum` assembles the result. -/

/-- If a weighted sum is error-free, so is each branch of positive weight. -/
theorem errFree_wsum {K : ℕ} {W : (Fin K → ℝ) → Prop} {Vk : Fin K → DConf}
    (h : ErrFree (DConf.wsum W Vk)) {ω : Fin K → ℝ} (hω : W ω)
    {b : (i : Fin K) → Fin (Vk i).n → ℝ}
    (hb : ∀ i, 0 < ω i → (Vk i).C (b i))
    (k : Fin K) (hk : 0 < ω k) : ErrFree (Vk k) := by
  intro p hp j hpos
  set b' : (i : Fin K) → Fin (Vk i).n → ℝ :=
    fun i => if h : i = k then h ▸ p else b i with hb'
  have hbk : b' k = p := by simp [hb']
  obtain ⟨ε, u, σ, hc⟩ :=
    h (fun c => ω (finSigmaFinEquiv.symm c).1 * b' _ (finSigmaFinEquiv.symm c).2)
      ⟨ω, hω, b', fun i hi => by
        by_cases hik : i = k
        · subst hik; rw [hbk]; exact hp
        · simp only [hb', dif_neg hik]; exact hb i hi,
        fun c => rfl⟩
      (finSigmaFinEquiv ⟨k, j⟩)
      (by
        show 0 < ω (finSigmaFinEquiv.symm (finSigmaFinEquiv
            (⟨k, j⟩ : (i : Fin K) × Fin (Vk i).n))).1
          * b' _ (finSigmaFinEquiv.symm (finSigmaFinEquiv
            (⟨k, j⟩ : (i : Fin K) × Fin (Vk i).n))).2
        rw [Equiv.symm_apply_apply, hbk]
        exact mul_pos hk hpos)
  rw [DConf.wsum_val] at hc
  exact ⟨ε, u, σ, hc⟩

/-! ## Simulation of one branch of `let` -/

/-- One branch of rule (Dlet): the precise coerced value is an ascription, so
`subErr` is ordinary substitution; the bodies, related by the precision rule of
`let`, stay related after substitution (`prec_subst0`), and the induction
hypothesis on the branch concludes. -/
theorem dgg_dlet_branch_cond {n n' : Tm} {w w' : Val} {τ τ' : FTy}
    {Fb Fb' : FDist} {kb' : ℕ} {Vb Vb' : DConf}
    (hpn : PrecT [τ] [τ'] n n') (hww' : PrecV [] [] w w')
    (hw : HasTyV [] w τ) (hw' : HasTyV [] w' τ')
    (hbty : HasTyT [τ] n Fb) (hbty' : HasTyT [τ'] n' Fb')
    (hwasc : ∃ (ε : TagTy) (u : Raw) (σ : FTy), w = .asc ε u σ)
    (hred' : Red (n'.subErr w' Fb') kb' Vb')
    (hIH : ∀ {n2 : Tm} {ky : ℕ} {Vy : DConf} {Dx Dx' : FDist},
      Red n2 ky Vy → HasTyT [] (n.subst0 w) Dx → HasTyT [] n2 Dx' →
      PrecT [] [] (n.subst0 w) n2 → DConfPrec Vb Vy) :
    DConfPrec Vb Vb' := by
  obtain ⟨ε, u, σ, rfl⟩ := hwasc
  obtain ⟨ε', u', σ', rfl, -, -, -, -⟩ := tprecV_asc_inv hww'
  rw [Tm.subErr_asc] at hred'
  exact hIH hred' (hasTy_subst0_tm hw hbty) (hasTy_subst0_tm hw' hbty')
    (prec_subst0 hpn hww' hw hw')

/-- The case of rule (Dlet). The data of the precise rule are parameters, the
less precise derivation is inverted inside, and the induction hypotheses are those
of the bound term (`hIHm`) and of the branches (`hIHb`). -/
theorem dgg_dlet_cond {m m' : Tm} {μ μ' : FDist} {ns : Fin μ.n → Tm}
    {ns' : Fin μ'.n → Tm} {k1 k2 : ℕ} {V0 : DConf}
    {wv : Fin (tagReorderD V0.confF μ).n → Val}
    {Vk : Fin (tagReorderD V0.confF μ).n → DConf}
    {Fb : Fin (tagReorderD V0.confF μ).n → FDist}
    (hrm : Red m k1 V0) (htm : HasTyT [] m μ)
    (hcell : ∀ c, Red (.ascV ((tagReorderD V0.confF μ).ty c)
      (V0.val (reorderDL V0.confF μ c)) (μ.ty (reorderDR V0.confF μ c))) 1
      (DConf.point (wv c)))
    (hbty : ∀ c, HasTyT [μ.ty (reorderDR V0.confF μ c)] (ns (reorderDR V0.confF μ c)) (Fb c))
    (hbred : ∀ c, Red ((ns (reorderDR V0.confF μ c)).subErr (wv c) (Fb c)) k2 (Vk c))
    (hef : ErrFree (DConf.wsum (tagReorderD V0.confF μ).toF.C Vk))
    (htm' : HasTyT [] m' μ')
    {kx : ℕ} {V' : DConf} (hred' : Red (.letin m' μ'.n ns') kx V')
    (hp : PrecT [] [] (.letin m μ.n ns) (.letin m' μ'.n ns'))
    (hIHm : ∀ {ky : ℕ} {Vy : DConf}, Red m' ky Vy → DConfPrec V0 Vy)
    (hIHb : ∀ (c : Fin (tagReorderD V0.confF μ).n) {n2 : Tm} {ky : ℕ}
      {Vy : DConf} {Dx Dx' : FDist},
      Red n2 ky Vy →
      HasTyT [] ((ns (reorderDR V0.confF μ c)).subst0 (wv c)) Dx →
      HasTyT [] n2 Dx' →
      PrecT [] [] ((ns (reorderDR V0.confF μ c)).subst0 (wv c)) n2 →
      DConfPrec (Vk c) Vy) :
    DConfPrec (DConf.wsum (tagReorderD V0.confF μ).toF.C Vk) V' := by
  obtain ⟨k1', k2', V0', wv', Vk', Fb', hrm',
    hcell', hbty', hbred', rfl⟩ := red_letin_inv hred' htm'
  cases hp with
  | letin hm hbodies hcoup =>
    -- type safety for the two bound terms
    obtain ⟨hvals, hgV0, hrefV0⟩ := type_safety hrm htm
    obtain ⟨hvals', hgV0', hrefV0'⟩ := type_safety hrm' htm'
    have hgμ : GoodD μ := wf_tm htm ctxGood_nil
    have hgμ' : GoodD μ' := wf_tm htm' ctxGood_nil
    have hrd : EReordD V0.confF μ :=
      reorderD_sat_iff_ereordD.mp (reorderD_sat_of_refDist hgV0.good.sat hrefV0)
    have hrd' : EReordD V0'.confF μ' :=
      reorderD_sat_iff_ereordD.mp
        (reorderD_sat_of_refDist hgV0'.good.sat hrefV0')
    have hgrp : GoodD (reorderD V0.confF μ) := goodD_reorderD hgV0 hgμ hrd
    have hgrp' : GoodD (reorderD V0'.confF μ') := goodD_reorderD hgV0' hgμ' hrd'
    -- the coerced values, typed at the target of their entry
    have hwtyP : ∀ k : Fin (reorderD V0.confF μ).n,
        HasTyV [] (wv k) (μ.ty (reorderDR V0.confF μ k)) := fun k =>
      red_ascV_result_typed (hasTy_letcell hgV0 hgμ hgrp hvals rfl k) (hcell k)
    have hwtyL : ∀ c : Fin (reorderD V0'.confF μ').n,
        HasTyV [] (wv' c) (μ'.ty (reorderDR V0'.confF μ' c)) := fun c =>
      red_ascV_result_typed (hasTy_letcell hgV0' hgμ' hgrp' hvals' rfl c) (hcell' c)
    -- and the substituted less precise branches, typed
    have hbranchTyL : ∀ c : Fin (reorderD V0'.confF μ').n,
        HasTyT [] ((ns' (reorderDR V0'.confF μ' c)).subErr (wv' c) (Fb' c)) (Fb' c) := fun c =>
      subErr_typed (hwtyL c) (hbty' c)
        (wf_tm (hbty' c) (ctxGood_cons (hgμ'.tys _) ctxGood_nil))
    refine dgg_dlet_cells hgV0 hgμ hgV0' hgμ' hgrp hgrp' hvals hvals' hcell hcell'
      (hIHm hrm') hrefV0' ?_ ?_ ?_
    · -- the branches: the precision of their types comes from the routing
      intro k c hcoerce hττ hmass
      refine dgg_dlet_branch_cond
        (hbodies htm htm' _ _ hττ (reorderDR V0.confF μ k).isLt
          (reorderDR V0'.confF μ' c).isLt) hcoerce
        (hwtyP k) (hwtyL c) (hbty k) (hbty' c) ?_ (hbred' c) ?_
      · -- the precise coerced value is not an error
        refine asc_of_not_err ?_ ?_
        · have h := hwtyP k
          rwa [tyEntry_of_hasTy h]
        · intro σ hσ
          have hb := hbred k
          rw [hσ, Tm.subErr_err] at hb
          obtain ⟨ω, hω, hωpos⟩ := hmass
          -- one solution per precise branch, to build that of the sum
          have hsol : ∀ c0 : Fin (tagReorderD V0.confF μ).n, ∃ pc, (Vk c0).C pc := fun c0 =>
            (type_safety (hbred c0) (subErr_typed (hwtyP c0) (hbty c0)
              (wf_tm (hbty c0) (ctxGood_cons (hgμ.tys _) ctxGood_nil)))).good.good.sat
          have hff := errFree_wsum hef hω
            (b := fun c0 => Classical.choose (hsol c0))
            (fun c0 _ => Classical.choose_spec (hsol c0)) k hωpos
          rw [red_errD_inv hb] at hff
          exact not_errFree_errAt (wf_tm (hbty k)
            (ctxGood_cons (hgμ.tys _) ctxGood_nil)) hff
      · intro n2 ky Vy Dx Dx' hr2 ht2 ht2' hp2
        exact hIHb k hr2 ht2 ht2' hp2
    · -- convexity of the formulas of the less precise branches
      intro c' p r hp1 hp2 a ha0 ha1
      exact (type_safety (hbred' c') (hbranchTyL c')).good.good.convex
        p r hp1 hp2 a ha0 ha1
    · intro c'
      exact (type_safety (hbred' c') (hbranchTyL c')).good.good.sat


end GradualProb.TPLC
