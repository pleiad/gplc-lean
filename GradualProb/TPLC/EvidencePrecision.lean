import GradualProb.TPLC.Reorder

/-!
# Precision of evidence combination

This module proves that evidence combination (the meet) is monotone with
respect to the runtime precision `⊑̇` of Figure 12 (`EPrecTy`/`EPrecD`), which is
Lemma 12, and the companion facts for the tag-aware precision `⊢[π]` between
evidences of Figure 18 (Lemmas 46, 47 and 48). The ascription, application and
`let` cases of the dynamic gradual guarantee (Theorem 5) consume these facts.

## Main results

* `meetTy_mono`, `meetD_mono`: Lemma 12 (monotonicity of evidence combination).
* `meetD_mono_tags`: the distribution case of Lemma 12 with the coupling
  exposed, relating the tags of the two meets.
* `tagPrecTy_emeet_compose`/`tagPrecD_emeet_compose` (Lemma 47, item 1):
  composing the more precise evidence with a meet preserves tag-aware
  precision.
* `tagPrecTy_emeetTy`/`tagPrecD_emeetD`: Lemma 46 (tag-aware monotonicity of
  evidence combination).
* `tagPrecTy_glb`/`tagPrecD_glb`: Lemma 47, item 2, a common lower bound is
  tag-aware below the tagged meet.
* `tagPrecTy_reorderTy_glb` (Lemma 47, item 3), `tagPrecD_reorderD_glb`, and
  `eprec_reorderD_glb_align` (Lemma 48): the tag-aware greatest-lower-bound
  property of the routing evidence `tagReorderD`, used by the (Dlet) case.

## Reading guide

The cells of a meet enumerate the consistent pairs of entries of its operands.
`meetD_mono_core` pushes a solution of a meet's constraint forward onto the
full grid of pairs (`isCoupling_pushfwd_prod`), transports it through the two
precision couplings with the tensor composition (`Lift.tensor`), and
restricts the result to the cells of the less precise meet
(`IsCoupling.restrict`, `Lift.restrict`).  `coup_comp_fun` composes a functional
coupling with a general one (`Lift.pushfwd`, `Lift.trans`).

Lemmas 46 and 47, item 1, are stated once for the tag `π`: the meet keeps the
tags `π` of one of its operands (`l` from the first, `r` from the second),
written `a`, and the other operand is written `b`, so that the meet is
`emeetTy (π.pick a b) (π.pick b a)`. The simple-type cases recurse on the
derivation of tag-aware precision and invert the meet with
`emeetTy_pick_arrow`. Each distribution case delegates to a lemma `…_of_cells`
that builds the coupling for each of the two tags (`l` or `r`), and supplies
the relation between the coupled cells by the simple-type case. The results on
the routing evidence come last.
-/


namespace GradualProb.TPLC

open GradualProb.GPLC


/-! ## Lemma 12: monotonicity of evidence combination

The distribution case pushes a solution of the precise meet's constraint onto
the grid of pairs of entries, transports it through the two precision couplings
with the tensor composition (`Lift.tensor`), and restricts the result to the
cells of the less precise meet.  The transported probability lies on
consistent less precise pairs by the transfer of consistency along precision
(`econs_eprec_ty`, Lemma 24).  The entries of the coupled cells are related by
the simple-type case, by mutual recursion. -/

/-- The coupling part of the distribution case of Lemma 12.  For cell
relations `R1`, `R2` contained in `⊑̇` and couplings of the operands supported
on them, each solution of the precise meet's constraint is coupled with one of
the less precise meet's, and coupled cells have their left tags related by
`R1` and their right tags by `R2`.  The precision of the entries is added in
`meetD_mono_tags`. -/
theorem meetD_mono_core : ∀ {D1 D2 D1' D2' : FDist}
    {R1 : Fin D1.n → Fin D1'.n → Prop} {R2 : Fin D2.n → Fin D2'.n → Prop},
    (∀ a a', R1 a a' → EPrecTy (D1.ty a) (D1'.ty a')) →
    (∀ b b', R2 b b' → EPrecTy (D2.ty b) (D2'.ty b')) →
    SymLiftAll R1 D1.C D1'.C → SymLiftAll R2 D2.C D2'.C →
    SymLiftAll (fun c c' => R1 (meetDL D1 D2 c) (meetDL D1' D2' c') ∧
        R2 (meetDR D1 D2 c) (meetDR D1' D2' c'))
      (meetD D1 D2).C (meetD D1' D2').C
  | D1, D2, D1', D2', R1, R2, hR1, hR2, hc1, hc2 => by
      intro w hw
      obtain ⟨hC1, hC2, hnn⟩ := (meetD_C_iff _ _ _).1 hw
      -- on the grid of pairs, the solution is a coupling of its two marginals
      have hP := isCoupling_pushfwd_prod (meetCell D1 D2) hnn
      -- the tensor composition with the two precision couplings
      obtain ⟨q1', hq1', hl1⟩ := hc1 _ hC1
      obtain ⟨q2', hq2', hl2⟩ := hc2 _ hC2
      obtain ⟨Q, hQ, hl⟩ := Lift.tensor hP hl1 hl2
      -- the transported joint lies on the cells of the less precise meet
      have hQr : ∀ a b, Q a b ≠ 0 → (a, b) ∈ Set.range (meetCell D1' D2') := fun a b hne => by
        obtain ⟨x, hx, h1, h2⟩ :=
          hl.exists_of_right_pos (j := (a, b)) ((hQ.nonneg a b).lt_of_ne' hne)
        obtain ⟨c, hc, -⟩ := pushfwd_pos hx
        have hx' : EConsTy (D1.ty x.1) (D2.ty x.2) := by
          have h : EConsTy (D1.ty (meetCell D1 D2 c).1) (D2.ty (meetCell D1 D2 c).2) :=
            meetCell_cons D1 D2 c
          rwa [show meetCell D1 D2 c = (x.1, x.2) from hc] at h
        exact meetCell_range (econs_eprec_ty hx' (hR1 _ _ h1) (hR2 _ _ h2))
      obtain ⟨rfl, rfl⟩ := hQ.restrict (meetCell_injective D1' D2') hQr
      refine ⟨fun c' => Q (meetDL D1' D2' c') (meetDR D1' D2' c'),
        (meetD_C_iff _ _ _).2 ⟨hq1', hq2', fun _ => hQ.nonneg _ _⟩, ?_⟩
      -- from cells to pairs, through the tensor, and back to cells
      have h₁ : Lift (fun c x => meetCell D1 D2 c = x) w (pushfwd (meetCell D1 D2) w) :=
        .pushfwd _ hnn fun _ => rfl
      have h₂ : Lift (fun y c' => meetCell D1' D2' c' = y)
          (fun y : Fin D1'.n × Fin D2'.n => Q y.1 y.2)
          (fun c' => Q (meetDL D1' D2' c') (meetDR D1' D2' c')) :=
        (Lift.restrict (meetCell_injective D1' D2') (fun _ => hQ.nonneg _ _)
          (fun y => hQr y.1 y.2) fun _ => rfl).symm
      exact (h₁.comp hl).trans h₂ fun _ _ _ ⟨_, hx, h⟩ hy => by subst hx hy; exact h

mutual
/-- Lemma 12 (monotonicity of evidence combination), simple types: if `σ ⊓ τ` is
defined (it exists and is well-formed), `σ ⊑̇ σ'` and `τ ⊑̇ τ'`, then `σ' ⊓ τ'` is defined
and `σ ⊓ τ ⊑̇ σ' ⊓ τ'`.  Definedness of the less precise meet follows from the coupling
clause (`eprecD_sat`): every solution of the precise formula is transported to
one of the less precise formula. -/
theorem meetTy_mono : ∀ {σ τ σ' τ' m : FTy}, GoodTy σ → GoodTy τ →
    GoodTy σ' → GoodTy τ' → σ ⊑̇ σ' → τ ⊑̇ τ' →
    σ ⊓ τ = some m → GoodTy m →
    ∃ m', σ' ⊓ τ' = some m' ∧ GoodTy m' ∧ m ⊑̇ m'
  | .real, .real, σ', τ', m, _, _, hgσ', hgτ', h1, h2, hm, _ => by
      obtain rfl := Option.some.inj hm
      cases h1 with
      | real =>
        cases h2 with
        | real => exact ⟨.real, rfl, .real, .real⟩
        | unk => exact ⟨.real, meetTy_unk_right _, .real, .real⟩
      | unk =>
        cases h2 with
        | real => exact ⟨.real, rfl, .real, .real⟩
        | unk => exact ⟨.unk, rfl, .unk, .unk⟩
  | .real, .bool, _, _, _, _, _, _, _, _, _, hm, _ => nomatch hm
  | .real, .arrow _ _, _, _, _, _, _, _, _, _, _, hm, _ => nomatch hm
  | .bool, .real, _, _, _, _, _, _, _, _, _, hm, _ => nomatch hm
  | .bool, .arrow _ _, _, _, _, _, _, _, _, _, _, hm, _ => nomatch hm
  | .arrow _ _, .real, _, _, _, _, _, _, _, _, _, hm, _ => nomatch hm
  | .arrow _ _, .bool, _, _, _, _, _, _, _, _, _, hm, _ => nomatch hm
  | .bool, .bool, σ', τ', m, _, _, hgσ', hgτ', h1, h2, hm, _ => by
      obtain rfl := Option.some.inj hm
      cases h1 with
      | bool =>
        cases h2 with
        | bool => exact ⟨.bool, rfl, .bool, .bool⟩
        | unk => exact ⟨.bool, meetTy_unk_right _, .bool, .bool⟩
      | unk =>
        cases h2 with
        | bool => exact ⟨.bool, rfl, .bool, .bool⟩
        | unk => exact ⟨.unk, rfl, .unk, .unk⟩
  | .unk, τ, σ', τ', m, _, _, hgσ', hgτ', h1, h2, hm, _ => by
      obtain rfl := Option.some.inj hm
      cases h1 with
      | unk => exact ⟨τ', rfl, hgτ', h2⟩
  | .real, .unk, σ', τ', m, _, _, hgσ', hgτ', h1, h2, hm, _ => by
      obtain rfl := Option.some.inj hm
      cases h2 with
      | unk =>
        exact ⟨σ', meetTy_unk_right _, hgσ', h1⟩
  | .bool, .unk, σ', τ', m, _, _, hgσ', hgτ', h1, h2, hm, _ => by
      obtain rfl := Option.some.inj hm
      cases h2 with
      | unk =>
        exact ⟨σ', meetTy_unk_right _, hgσ', h1⟩
  | .arrow s1 E1, .unk, σ', τ', m, hgσ, _, hgσ', hgτ', h1, h2, hm, _ => by
      rw [meetTy_unk_right] at hm
      obtain rfl := Option.some.inj hm
      cases h2 with
      | unk =>
        exact ⟨σ', meetTy_unk_right _, hgσ', h1⟩
  | .arrow s1 E1, .arrow s2 E2, σ', τ', m, hgσ, hgτ, hgσ', hgτ', h1, h2, hm,
      hgm => by
      cases hgσ with
      | arrow hgs1 hgE1 =>
      cases hgτ with
      | arrow hgs2 hgE2 =>
        cases hs : meetTy s1 s2 with
        | none =>
            rw [meetTy_arrow, hs] at hm
            exact (nomatch hm)
        | some s3 =>
          rw [meetTy_arrow, hs] at hm
          simp only [Option.map_some, Option.some.injEq] at hm
          subst hm
          cases hgm with
          | arrow hgs3 hgE12 =>
            cases h1 with
            | unk =>
              -- σ' = ?: the less precise meet is τ'; right reductivity
              refine ⟨τ', rfl, hgτ', ?_⟩
              exact EPrecTy.trans
                (eprec_meetTy .r (.arrow hgs1 hgE1) (.arrow hgs2 hgE2)
                  (by rw [meetTy_arrow, hs]; rfl))
                h2
            | @arrow _ _ s1' E1' hs1' hD1' =>
              cases h2 with
              | unk =>
                -- τ' = ?: the less precise meet is σ'; left reductivity
                refine ⟨.arrow s1' E1', meetTy_unk_right _, hgσ', ?_⟩
                exact EPrecTy.trans
                  (eprec_meetTy .l (.arrow hgs1 hgE1) (.arrow hgs2 hgE2)
                    (by rw [meetTy_arrow, hs]; rfl))
                  (.arrow hs1' hD1')
              | arrow hs2' hD2' =>
                cases hgσ' with
                | arrow hgs1' hgE1' =>
                cases hgτ' with
                | arrow hgs2' hgE2' =>
                  obtain ⟨s3', hs3', hgs3', hss'⟩ :=
                    meetTy_mono hgs1 hgs2 hgs1' hgs2' hs1' hs2' hs hgs3
                  have hEE' : EPrecD (meetD _ _) (meetD _ _) :=
                    .intro ((meetD_mono_tags hgE1 hgE2 hgE1' hgE2' (fun _ _ h => h)
                      (fun _ _ h => h) hD1'.coup hD2'.coup hgE12).mono fun _ _ h => h.1)
                  refine ⟨.arrow s3' (meetD _ _), ?_, .arrow hgs3'
                      (goodD_meetD_sat hgE1' hgE2' (eprecD_sat hEE' hgE12.good.sat)),
                    .arrow hss' hEE'⟩
                  rw [meetTy_arrow, hs3']
                  rfl
  termination_by structural σ τ σ' τ' m hgσ hgτ hgσ' hgτ' h1 h2 hm hgm => σ
/-- The distribution case of Lemma 12 with the coupling exposed.  For cell
relations `R1`, `R2` contained in `⊑̇` and couplings of the operands supported
on them, each solution of the precise meet's constraint is coupled with one of
the less precise meet's, and coupled cells are `⊑̇`-related, with their left tags
related by `R1` and their right tags by `R2`.  The coupling is that of
`meetD_mono_core`; `meetTy_mono` and `meetD_mono` instantiate `R1` and `R2`
with the relations of the operands' precision liftings, and the tag-aware
lemmas below use `meetD_mono_core` directly. -/
theorem meetD_mono_tags : ∀ {D1 D2 D1' D2' : FDist}
    {R1 : Fin D1.n → Fin D1'.n → Prop} {R2 : Fin D2.n → Fin D2'.n → Prop},
    GoodD D1 → GoodD D2 → GoodD D1' → GoodD D2' →
    (∀ a a', R1 a a' → EPrecTy (D1.ty a) (D1'.ty a')) →
    (∀ b b', R2 b b' → EPrecTy (D2.ty b) (D2'.ty b')) →
    SymLiftAll R1 D1.C D1'.C → SymLiftAll R2 D2.C D2'.C →
    GoodD (meetD D1 D2) →
    SymLiftAll (fun c c' => EPrecTy ((meetD D1 D2).ty c) ((meetD D1' D2').ty c') ∧
        R1 (meetDL D1 D2 c) (meetDL D1' D2' c') ∧
        R2 (meetDR D1 D2 c) (meetDR D1' D2' c'))
      (meetD D1 D2).C (meetD D1' D2').C
  | .mk n1 ty1 C1, .mk n2 ty2 C2, .mk n1' ty1' C1', .mk n2' ty2' C2', R1, R2,
      hg1, hg2, hg1', hg2', hR1, hR2, hc1, hc2, hgmeet =>
      (meetD_mono_core hR1 hR2 hc1 hc2).mono fun c c' ⟨hL1, hL2⟩ => by
        refine ⟨?_, hL1, hL2⟩
        -- the entry of each cell is the meet of the entries that its tags name
        obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp
          (cons_meetTy_isSome (meetCell_cons _ _ c))
        have hty : (meetD (.mk n1 ty1 C1) (.mk n2 ty2 C2)).ty c = m :=
          congrArg (Option.getD · FTy.unk) hm
        obtain ⟨m', hm', -, hmm'⟩ :=
          meetTy_mono (hg1.tys _) (hg2.tys _) (hg1'.tys _) (hg2'.tys _)
            (hR1 _ _ hL1) (hR2 _ _ hL2) hm (hty ▸ hgmeet.tys c)
        have hty' : (meetD (.mk n1' ty1' C1') (.mk n2' ty2' C2')).ty c' = m' :=
          congrArg (Option.getD · FTy.unk) hm'
        rw [hty, hty']
        exact hmm'
  termination_by structural D1 D2 D1' D2' R1 R2 hg1 hg2 hg1' hg2' hR1 hR2 hc1 hc2
    hgmeet => D1
end

/-- Lemma 12 (monotonicity of evidence combination), distribution types: if
`D1 ⊓ D2` is defined, `D1 ⊑̇ D1'` and `D2 ⊑̇ D2'`, then `D1' ⊓ D2'` is defined and
`D1 ⊓ D2 ⊑̇ D1' ⊓ D2'`. -/
theorem meetD_mono : ∀ {D1 D2 D1' D2' : FDist}, GoodD D1 → GoodD D2 →
    GoodD D1' → GoodD D2' → D1 ⊑̇ D1' → D2 ⊑̇ D2' →
    GoodD (D1 ⊓ D2) →
    GoodD (D1' ⊓ D2') ∧ D1 ⊓ D2 ⊑̇ D1' ⊓ D2'
  | _, _, _, _, hg1, hg2, hg1', hg2', hd1, hd2, hgmeet =>
      have hprec : EPrecD (meetD _ _) (meetD _ _) :=
        .intro ((meetD_mono_tags hg1 hg2 hg1' hg2' (fun _ _ h => h) (fun _ _ h => h)
          hd1.coup hd2.coup hgmeet).mono fun _ _ h => h.1)
      ⟨goodD_meetD_sat hg1' hg2' (eprecD_sat hprec hgmeet.good.sat), hprec⟩


/-! ## Tags of the tagged meet

The tags of `emeetD` are those of its operands composed with the
projections of the carrier pair: `l = l₁ ∘ π₁` and `r = r₂ ∘ π₂`. -/

/-- Composition of a functional coupling with a general one.  A tag map `f`
with `TagPrec X Y f` pushes each solution of `X` to one of `Y`; composing with a
coupling of `Y` and `Z` supported on `R` gives a coupling of `X` and `Z`
supported on `R ∘ f`.  This transports a relation from the cells of an evidence
to the cells of a composition. -/
theorem coup_comp_fun {X Y Z : FDist} {f : Fin X.n → Fin Y.n}
    {R : Fin Y.n → Fin Z.n → Prop}
    (hf : TagPrec X Y f) (hgX : Good X) (hc : SymLiftAll R Y.C Z.C) :
    SymLiftAll (fun k c => R (f k) c) X.C Z.C := fun w hw =>
  let ⟨r, hr, hl⟩ := hc _ (hf.push w hw)
  ⟨r, hr, (Lift.pushfwd (R := fun k b => f k = b) f (hgX.nonneg w hw) fun _ => rfl).trans hl
    fun _ _ _ hkb hbc => by subst hkb; exact hbc⟩


/-- Only `?` is less precise than `?`. -/
theorem eprecTy_unk_left : ∀ {t : FTy}, EPrecTy .unk t → t = .unk
  | _, .unk => rfl


/-- A tagged evidence less precise than `?` is `?`. -/
theorem tagTy_unk_of_eprec {e : TagTy} (h : EPrecTy (TagTy.unk).toF e.toF) :
    e = .unk := by
  cases e with
  | unk => rfl
  | real => exact absurd (eprecTy_unk_left h) (by simp [TagTy.toF])
  | bool => exact absurd (eprecTy_unk_left h) (by simp [TagTy.toF])
  | arrow s d => exact absurd (eprecTy_unk_left h) (by simp [TagTy.toF])

/-- Lemma 12 for tagged meets, along one tag: the erasures of two tagged meets
of related operands are related by `⊑̇`. -/
theorem eprecTy_emeetTy_mono (π : Side) {a b a' b' m3 m3' : TagTy}
    (hga : GoodTy a.toF) (hgb : GoodTy b.toF) (hga' : GoodTy a'.toF)
    (hgb' : GoodTy b'.toF) (ha : EPrecTy a.toF a'.toF) (hb : EPrecTy b.toF b'.toF)
    (hm : emeetTy (π.pick a b) (π.pick b a) = some m3)
    (hm' : emeetTy (π.pick a' b') (π.pick b' a') = some m3')
    (hgm : GoodTy m3.toF) : EPrecTy m3.toF m3'.toF := by
  have key : ∀ {e1 e2 e1' e2' : TagTy}, GoodTy e1.toF → GoodTy e2.toF → GoodTy e1'.toF →
      GoodTy e2'.toF → EPrecTy e1.toF e1'.toF → EPrecTy e2.toF e2'.toF →
      emeetTy e1 e2 = some m3 → emeetTy e1' e2' = some m3' → EPrecTy m3.toF m3'.toF :=
    fun hg1 hg2 hg1' hg2' h1 h2 hm hm' => by
      obtain ⟨m, hmm, -, hpm⟩ :=
        meetTy_mono hg1 hg2 hg1' hg2' h1 h2 (emeetTy_toF_some hm) hgm
      rw [emeetTy_toF_some hm'] at hmm
      obtain rfl := Option.some.inj hmm
      exact hpm
  cases π
  · exact key hga hgb hga' hgb' ha hb hm hm'
  · exact key hgb hga hgb' hga' hb ha hm hm'

/-- A tagged meet is below its operand `a` in runtime precision (Lemma 8). -/
theorem eprecTy_emeetTy_pick (π : Side) {a b m : TagTy} (hga : GoodTy a.toF)
    (hgb : GoodTy b.toF) (hm : emeetTy (π.pick a b) (π.pick b a) = some m) :
    EPrecTy m.toF a.toF := by
  cases π
  · exact eprec_meetTy .l hga hgb (emeetTy_toF_some hm)
  · exact eprec_meetTy .r hgb hga (emeetTy_toF_some hm)


/-! ## Composing the more precise evidence with a meet

    C ⊑ C″ ⊢[π] a ⊓ b ⊑̇ e″   whenever   C ⊑ C″ ⊢[π] a ⊑̇ e″   (same judged types)

where `a` is the operand whose tags `π` the meet keeps: a cell of the meet
names, through its tag `π`, the same entry as the cell of `a` it comes from.
This covers tag-aware reductivity (take `e″ := a`) and composition with the
precision hypothesis of a term. -/

/-- The distribution case of `tagPrecTy_emeet_compose`, given the cells: the
coupling of `a` with `e″` transports to the meet along the projection of its
cells onto `a` (`coup_comp_fun`). -/
theorem tagPrecD_emeet_compose_of_cells {π : Side} {a b e'' : TagD} {D D'' : FDist}
    (hga : GoodD a.toF) (hgb : GoodD b.toF) (R : Fin a.n → Fin e''.n → Prop)
    (ht : ∀ k, a.tag π k < D.n) (ht' : ∀ c', e''.tag π c' < D''.n)
    (hprec : ∀ k c', R k c' →
      PrecTy (D.ty ⟨a.tag π k, ht k⟩) (D''.ty ⟨e''.tag π c', ht' c'⟩))
    (hc : SymLiftAll R a.toF.C e''.toF.C)
    (hcell : ∀ c c', R (emeetDTag π a b c) c' →
      TagPrecTy π (D.ty ⟨a.tag π (emeetDTag π a b c), ht _⟩) (D''.ty ⟨e''.tag π c', ht' c'⟩)
        ((emeetD (π.pick a b) (π.pick b a)).ty c) (e''.ty c')) :
    TagPrecD π (emeetD (π.pick a b) (π.pick b a)) e'' D D'' := by
  cases π
  · refine .mk (fun c c' => R (meetDL a.toF b.toF c) c') (fun c => ht _) ht' hcell
      (fun _ _ h => hprec _ _ h) fun w hw => ?_
    exact coup_comp_fun (Z := e''.toF) (tagPrec_meetD .l hga hgb) (goodD_meetD_sat hga hgb ⟨w, hw⟩).good hc w hw
  · refine .mk (fun c c' => R (meetDR b.toF a.toF c) c') (fun c => ht _) ht' hcell
      (fun _ _ h => hprec _ _ h) fun w hw => ?_
    exact coup_comp_fun (Z := e''.toF) (tagPrec_meetD .r hgb hga) (goodD_meetD_sat hgb hga ⟨w, hw⟩).good hc w hw

mutual
/-- Lemma 47 (tag-aware precision and the meet), item 1, simple types:
composing the more precise evidence with a meet preserves tag-aware precision
along the tag that the meet keeps. -/
theorem tagPrecTy_emeet_compose {π : Side} : ∀ {C C'' : FTy} {a b m e'' : TagTy},
    GoodTy a.toF → GoodTy b.toF → C ⊑ C'' ⊢[π] a ⊑̇ e'' →
    π.pick a b ∘ π.pick b a = some m → C ⊑ C'' ⊢[π] m ⊑̇ e''
  | _, _, _, _, _, _, hga, hgb, .flat hn hE, hm =>
      .flat (fun ⟨hC, hC'', _, he⟩ => hn ⟨hC, hC'', TagTy.isArrow_of_eprec hE he, he⟩)
        (EPrecTy.trans (eprecTy_emeetTy_pick π hga hgb hm) hE)
  | _, _, _, _, _, _, hga, hgb, .arrow hs hd, hm => by
      obtain ⟨rfl, rfl⟩ | ⟨s0, d0, s3, rfl, hs3, rfl⟩ := emeetTy_pick_arrow hm
      · exact .arrow hs hd
      · cases hga with
        | arrow hgs hgd =>
          cases hgb with
          | arrow hgs0 hgd0 =>
            exact .arrow (tagPrecTy_emeet_compose hgs hgs0 hs hs3)
              (tagPrecD_emeet_compose hgd hgd0 hd)
/-- Lemma 47 (tag-aware precision and the meet), item 1, distribution types. -/
theorem tagPrecD_emeet_compose {π : Side} : ∀ {a b e'' : TagD} {D D'' : FDist},
    GoodD a.toF → GoodD b.toF → D ⊑ D'' ⊢[π] a ⊑̇ e'' →
    D ⊑ D'' ⊢[π] π.pick a b ∘ π.pick b a ⊑̇ e''
  | a, b, _, _, _, hga, hgb, .mk R ht ht' hty hprec hc =>
      tagPrecD_emeet_compose_of_cells hga hgb R ht ht' hprec hc fun c _ hR =>
        tagPrecTy_emeet_compose (TagD.goodTy_entry hga _) (TagD.goodTy_entry hgb _)
          (hty _ _ hR) (emeetD_ty_pick π a b c)
end


/-! ## Monotonicity of the tagged meet for tag-aware precision

    C ⊑ C′ ⊢[π] a ⊓ b ⊑̇ a′ ⊓ b′   from   C ⊑ C′ ⊢[π] a ⊑̇ a′   and   b ⊑̇ b′

For the operand whose tags the meet does not keep, the runtime precision of
the erasures suffices. The result of an ascription is the composed evidence,
and the ascription rules of term precision compare it tag-aware against the
annotations. -/

/-- The distribution case of `tagPrecTy_emeetTy`, given the cells: the
coupling of the two meets is that of Lemma 12 (`meetD_mono_core`), built from
the tag-aware coupling of `a` with `a'` and the runtime coupling of `b` with
`b'`. -/
theorem tagPrecD_emeetD_of_cells {π : Side} {a b a' b' : TagD} {C C' : FDist}
    (R : Fin a.n → Fin a'.n → Prop) (ht : ∀ k, a.tag π k < C.n) (ht' : ∀ k, a'.tag π k < C'.n)
    (hR : ∀ k k', R k k' → EPrecTy (a.ty k).toF (a'.ty k').toF)
    (hprec : ∀ k k', R k k' → PrecTy (C.ty ⟨a.tag π k, ht k⟩) (C'.ty ⟨a'.tag π k', ht' k'⟩))
    (hc : SymLiftAll R a.toF.C a'.toF.C) (hb : EPrecD b.toF b'.toF)
    (hcell : ∀ c c', R (emeetDTag π a b c) (emeetDTag π a' b' c') →
      EPrecTy (b.ty (emeetDOther π a b c)).toF (b'.ty (emeetDOther π a' b' c')).toF →
      TagPrecTy π (C.ty ⟨a.tag π (emeetDTag π a b c), ht _⟩)
        (C'.ty ⟨a'.tag π (emeetDTag π a' b' c'), ht' _⟩)
        ((emeetD (π.pick a b) (π.pick b a)).ty c) ((emeetD (π.pick a' b') (π.pick b' a')).ty c')) :
    TagPrecD π (emeetD (π.pick a b) (π.pick b a)) (emeetD (π.pick a' b') (π.pick b' a')) C C' := by
  obtain ⟨Rb, hRb, hcb⟩ := hb
  have hR' : ∀ k k', R k k' → EPrecTy (a.toF.ty k) (a'.toF.ty k') := fun k k' h => by
    rw [tagD_toF_ty, tagD_toF_ty]; exact hR k k' h
  have hRb' : ∀ k k', Rb k k' → EPrecTy (b.ty k).toF (b'.ty k').toF := fun k k' h => by
    rw [← tagD_toF_ty, ← tagD_toF_ty]; exact hRb k k' h
  cases π
  · exact .mk _ (fun c => ht _) (fun c => ht' _) (fun _ _ h => hcell _ _ h.1 (hRb' _ _ h.2))
      (fun _ _ h => hprec _ _ h.1) (meetD_mono_core hR' hRb hc hcb)
  · exact .mk _ (fun c => ht _) (fun c => ht' _) (fun _ _ h => hcell _ _ h.2 (hRb' _ _ h.1))
      (fun _ _ h => hprec _ _ h.2) (meetD_mono_core hRb hR' hcb hc)

mutual
/-- Lemma 46 (tag-aware monotonicity of evidence combination), simple types:
the tagged meet is monotone for tag-aware precision along the tag it keeps
from its operand `a`. -/
theorem tagPrecTy_emeetTy {π : Side} : ∀ {C C' : FTy} {a b a' b' m3 m3' : TagTy},
    GoodTy a.toF → GoodTy b.toF → GoodTy a'.toF → GoodTy b'.toF →
    a ⊩[π] C → a' ⊩[π] C' →
    C ⊑ C' ⊢[π] a ⊑̇ a' → b.toF ⊑̇ b'.toF →
    π.pick a b ∘ π.pick b a = some m3 →
    π.pick a' b' ∘ π.pick b' a' = some m3' →
    GoodTy m3.toF →
    C ⊑ C' ⊢[π] m3 ⊑̇ m3'
  | _, _, _, _, _, _, _, _, hga, hgb, hga', hgb', hv, hv', .flat hn hE, hb, hm, hm', hgm =>
      .flat (fun ⟨hC, hC', _⟩ => hn ⟨hC, hC', hv.isArrow hC, hv'.isArrow hC'⟩)
        (eprecTy_emeetTy_mono π hga hgb hga' hgb' hE hb hm hm' hgm)
  | _, _, _, _, _, _, _, _, hga, hgb, hga', hgb', hv, hv', .arrow hs hd, hb, hm, hm',
      hgm => by
      obtain ⟨rfl, rfl⟩ | ⟨s0, d0, s3, rfl, hs3, rfl⟩ := emeetTy_pick_arrow hm
      · -- `b = ?`, so `b' = ?` and both meets are their operand `a`
        obtain rfl := tagTy_unk_of_eprec hb
        obtain ⟨-, rfl⟩ | ⟨_, _, _, h, -⟩ := emeetTy_pick_arrow hm'
        · exact .arrow hs hd
        · exact nomatch h
      · cases hv with
        | arrow hvs hvd =>
        cases hga with
        | arrow hgs hgd =>
        cases hgb with
        | arrow hgs0 hgd0 =>
        cases hgm with
        | arrow hgms hgmd =>
        obtain ⟨-, rfl⟩ | ⟨s0', d0', s3', rfl, hs3', rfl⟩ := emeetTy_pick_arrow hm'
        · -- `b' = ?`: the less precise meet is `a'`, and the more precise one
          -- is a composition with `a`
          exact .arrow (tagPrecTy_emeet_compose hgs hgs0 hs hs3)
            (tagPrecD_emeet_compose hgd hgd0 hd)
        · cases hv' with
          | arrow hvs' hvd' =>
          cases hga' with
          | arrow hgs' hgd' =>
          cases hgb' with
          | arrow hgs0' hgd0' =>
          cases hb with
          | arrow hbs hbd =>
          exact .arrow
            (tagPrecTy_emeetTy hgs hgs0 hgs' hgs0' hvs hvs' hs hbs hs3 hs3' hgms)
            (tagPrecD_emeetD hgd hgd0 hgd' hgd0' hvd hvd' hgmd hd hbd)
/-- Lemma 46 (tag-aware monotonicity of evidence combination), distribution
types. -/
theorem tagPrecD_emeetD {π : Side} : ∀ {a b a' b' : TagD} {C C' : FDist},
    GoodD a.toF → GoodD b.toF → GoodD a'.toF → GoodD b'.toF →
    a ⊩[π] C → a' ⊩[π] C' →
    GoodD (π.pick a b ∘ π.pick b a).toF →
    C ⊑ C' ⊢[π] a ⊑̇ a' → b.toF ⊑̇ b'.toF →
    C ⊑ C' ⊢[π] π.pick a b ∘ π.pick b a ⊑̇ π.pick a' b' ∘ π.pick b' a'
  | a, b, a', b', _, _, hga, hgb, hga', hgb', .mk _ _ hh, .mk _ _ hh', _,
      .mk R ht ht' hty hprec hc, hb =>
      tagPrecD_emeetD_of_cells R ht ht' (fun _ _ h => (hty _ _ h).toEPrecTy) hprec hc hb
        fun c c' hR hE =>
          tagPrecTy_emeetTy (TagD.goodTy_entry hga _) (TagD.goodTy_entry hgb _)
            (TagD.goodTy_entry hga' _) (TagD.goodTy_entry hgb' _) (hh _) (hh' _) (hty _ _ hR) hE (emeetD_ty_pick π a b c) (emeetD_ty_pick π a' b' c')
            (goodTy_emeetD_entry
              (TagD.goodTy_entry (Side.pick_prop (fun x : TagD => GoodD x.toF) π hga hgb))
              (TagD.goodTy_entry (Side.pick_prop (fun x : TagD => GoodD x.toF) π hgb hga)) c)
end


/-! ## Greatest lower bound of the tagged meet

    X ⊑̇ Y₁   and   C ⊑ C₂ ⊢[.r] X ⊑̇ Y₂   ⟹   C ⊑ C₂ ⊢[.r] X ⊑̇ Y₁ ∘ Y₂

A common lower bound is tag-aware below the meet as soon as it is tag-aware
below its second operand, because the right tag of the meet is that of that
operand. -/

/-- Untagged version: the greatest-lower-bound part of Lemma 8. -/
theorem eprecTy_glb {x y1 y2 m : TagTy} (hgx : GoodTy x.toF)
    (h1 : EPrecTy x.toF y1.toF) (h2 : EPrecTy x.toF y2.toF)
    (hm : emeetTy y1 y2 = some m) : EPrecTy x.toF m.toF :=
  eprec_meetTy_glb hgx h1 h2 (emeetTy_toF_some hm)

mutual
/-- Lemma 47 (tag-aware precision and the meet), item 2, simple types: a common
lower bound is tag-aware below the tagged meet. -/
theorem tagPrecTy_glb : ∀ {C C₂ : FTy} {x y1 y2 m : TagTy},
    GoodTy x.toF → GoodTy y1.toF → GoodTy y2.toF → GoodTy C₂ →
    y2 ⊩[.r] C₂ →
    x.toF ⊑̇ y1.toF → C ⊑ C₂ ⊢[.r] x ⊑̇ y2 →
    y1 ∘ y2 = some m → C ⊑ C₂ ⊢[.r] x ⊑̇ m
  | _, _, _, _, _, _, hgx, _, _, _, hv2, h1, .flat hn hE, hm =>
      .flat (fun ⟨hC, hC₂, hx, _⟩ => hn ⟨hC, hC₂, hx, hv2.isArrow hC₂⟩)
        (eprecTy_glb hgx h1 hE hm)
  | _, _, _, _, _, _, hgx, hgy1, hgy2, hgC₂, hv2, h1, .arrow hs hd, hm => by
      obtain ⟨rfl, rfl⟩ | ⟨s1, d1, s3, rfl, hs3, rfl⟩ := emeetTy_pick_arrow (π := .r) hm
      · exact .arrow hs hd
      · cases hgx with
        | arrow hgxs hgxd =>
        cases hgy1 with
        | arrow hgy1s hgy1d =>
        cases hgy2 with
        | arrow hgy2s hgy2d =>
        cases hgC₂ with
        | arrow hgC₂s hgC₂d =>
        cases hv2 with
        | arrow hv2s hv2d =>
        cases h1 with
        | arrow h1s h1d =>
        exact .arrow (tagPrecTy_glb hgxs hgy1s hgy2s hgC₂s hv2s h1s hs hs3)
          (tagPrecD_glb hgxd hgy1d hgy2d hgC₂d hv2d h1d hd)
/-- Lemma 47 (tag-aware precision and the meet), item 2, distribution types: a
common lower bound is tag-aware below the tagged meet. -/
theorem tagPrecD_glb : ∀ {x y1 y2 : TagD} {D D₂ : FDist},
    GoodD x.toF → GoodD y1.toF → GoodD y2.toF → GoodD D₂ →
    y2 ⊩[.r] D₂ →
    x.toF ⊑̇ y1.toF → D ⊑ D₂ ⊢[.r] x ⊑̇ y2 →
    D ⊑ D₂ ⊢[.r] x ⊑̇ y1 ∘ y2
  | x, y1, y2, _, _, hgx, hgy1, hgy2, hgD₂, .mk _ _ hh, h1, .mk R ht ht' hty hprec hc => by
    obtain ⟨R1, hR1, hc1⟩ := h1
    refine .mk _ ht (fun c => ht' (meetDR y1.toF y2.toF c)) (fun k c h => ?_)
      (fun k c h => hprec _ _ h.2.2)
      (eprec_meetD_glb_tags hgx hR1
        (fun _ _ h => by rw [tagD_toF_ty, tagD_toF_ty]; exact (hty _ _ h).toEPrecTy) hc1 hc)
    exact tagPrecTy_glb (TagD.goodTy_entry hgx _) (TagD.goodTy_entry hgy1 _)
      (TagD.goodTy_entry hgy2 _) (hgD₂.tys _) (hh _)
      (by rw [← tagD_toF_ty, ← tagD_toF_ty]; exact hR1 _ _ h.2.1) (hty _ _ h.2.2)
      (emeetD_ty_spec y1 y2 c)
end


/-! ## Tag-aware greatest lower bound of the routing evidence

The (Dlet) case of the dynamic gradual guarantee compares the routing evidences
`tagReorderD` of the two sides. -/

/-! ### Tag-aware greatest lower bound of `tagReorderD`

    μₛ ⊑ μₛ′ ⊢[.r] μᵣ ∥ᵗ μₛ ⊑̇ μᵣ′ ∥ᵗ μₛ′

from `μᵣ ⊑ μᵣ′`, the refinement of `μᵣ′` into `μₛ′` (type safety on the less precise
side).  Definedness on the less precise side is not transported:
the coupling comes from the refinement, which picks carrier cells. -/

mutual
/-- Lemma 47 (tag-aware precision and the meet), item 3: tag-aware greatest
lower bound of the tagged reordering, simple types. -/
theorem tagPrecTy_reorderTy_glb : ∀ {σr σs σr' σs' : FTy} {e e' : TagTy},
    GoodTy σr → GoodTy σs → GoodTy σr' → GoodTy σs' →
    σr ⊑ σr' → RefTy σr' σs' → σr =ʳ σs →
    σr ∥ᵗ σs = some e → σr' ∥ᵗ σs' = some e' →
    σs ⊑ σs' ⊢[.r] e ⊑̇ e'
  | σr, σs, _, _, e, e', hgr, hgs, hgr', hgs', hprec, .real, hreord,
      hte, hte' => by
      cases hprec
      cases hreord
      simp only [tagReorderTy, Option.some.injEq] at hte hte'
      subst hte; subst hte'
      exact .flat (fun h => h.1) EPrecTy.real
  | σr, σs, _, _, e, e', hgr, hgs, hgr', hgs', hprec, .bool, hreord,
      hte, hte' => by
      cases hprec
      cases hreord
      simp only [tagReorderTy, Option.some.injEq] at hte hte'
      subst hte; subst hte'
      exact .flat (fun h => h.1) EPrecTy.bool
  | σr, σs, _, _, e, e', hgr, hgs, hgr', hgs', hprec, .unk, hreord,
      hte, hte' => by
      simp only [tagReorderTy, Option.some.injEq] at hte'
      subst hte'
      exact TagPrecTy.unk_right
  | σr, σs, .arrow sP DP, .arrow sQ DQ, e, e', hgr, hgs, hgr', hgs', hprec,
      .arrow hs hD, hreord, hte, hte' => by
      cases hprec with
      | arrow hps hpD =>
        rename_i s1 D1
        cases hreord with
        | arrow hrs hrD =>
          rename_i s2 D2
          cases hgr with
          | arrow hgs1 hgD1 =>
          cases hgs with
          | arrow hgs2 hgD2 =>
          cases hgr' with
          | arrow hgsP hgDP =>
          cases hgs' with
          | arrow hgsQ hgDQ =>
            cases hes : tagReorderTy s1 s2 with
            | none => simp only [tagReorderTy, hes] at hte; exact nomatch hte
            | some es =>
              cases hes' : tagReorderTy sP sQ with
              | none => simp only [tagReorderTy, hes'] at hte'; exact nomatch hte'
              | some es' =>
                simp only [tagReorderTy, hes, Option.some.injEq] at hte
                simp only [tagReorderTy, hes', Option.some.injEq] at hte'
                subst hte; subst hte'
                exact TagPrecTy.arrow
                  (tagPrecTy_reorderTy_glb hgs1 hgs2 hgsP hgsQ hps hs
                    (EReordTy.symm hrs) hes hes')
                  (tagPrecD_reorderD_glb hgD1 hgD2 hgDP hgDQ hpD hD)
  termination_by structural σr σs σr' σs' e e' => σs'
/-- Tag-aware greatest lower bound of `tagReorderD`, distribution types. -/
theorem tagPrecD_reorderD_glb : ∀ {Dr Ds Dr' Ds' : FDist},
    GoodD Dr → GoodD Ds → GoodD Dr' → GoodD Ds' →
    PrecD Dr Dr' → RefDist Dr' Ds' →
    TagPrecD .r (tagReorderD Dr Ds) (tagReorderD Dr' Ds') Ds Ds'
  | Dr, Ds, Dr', .mk ns' tys' Cs', hgr, hgs, hgr', hgs', hprec, href => by
      classical
      -- the right tag of a cell of `tagReorderD` is its right provenance in `reorderD`
      refine TagPrecD.intro (fun c => (reorderDR Dr Ds c).isLt)
        (fun c => (reorderDR Dr' (FDist.mk ns' tys' Cs') c).isLt) ?_
      intro w hw
      obtain ⟨w', hw', hl⟩ :=
        eprec_reorderD_glb_tags hgr'
          (fun k a h => EPrecTy.trans ((tagPrec_reorderD .l hgr hgs).cell k)
            (eprecTy_of_precTy h))
          (coup_comp_fun (tagPrec_reorderD .l hgr hgs)
            (goodD_reorderD_sat hgr hgs ⟨w, hw⟩).good hprec.coup)
          href w hw
      refine ⟨w', hw', hl.mono fun c c' ⟨_, hleft⟩ => ?_⟩
      have hrefT := reorderD_cell_eq _ _ c'
      have hdst : PrecTy (Ds.ty (reorderDR Dr Ds c))
          ((FDist.mk ns' tys' Cs').ty (reorderDR Dr' (FDist.mk ns' tys' Cs') c')) := by
        rw [← reorderD_cell_eq _ _ c, ← hrefT]; exact hleft
      exact ⟨tagPrecTy_reorderTy_glb (hgr.tys _) (hgs.tys _) (hgr'.tys _) (hgs'.tys _) hleft
        (hrefT ▸ RefTy.refl (hgr'.tys _)) (reorderD_cell_live hgr c)
        (tagReorderD_ty_spec Dr Ds c) (tagReorderD_ty_spec Dr' (FDist.mk ns' tys' Cs') c'), hdst⟩
  termination_by structural Dr Ds Dr' Ds' => Ds'
end


/-! ## The open form consumed by the (Dlet) case

`tagPrecD_reorderD_glb` packs the coupling inside tag-aware precision, but the
simulation of a `let` needs a single coupling that gives at once the value each
cell routes (left tag), the branch it routes to (right tag), and the
tag-aware precision of the entries against the targets. -/

/-- Lemma 48 (greatest lower bound of reordering), aligned form: the coupling
of `eprec_reorderD_glb_tags`, which `tagPrecD_reorderD_glb` also uses, for a
free cell relation `R1`, with the cell facts stated separately. -/
theorem eprec_reorderD_glb_align : ∀ {γp μ γl B : FDist}
    {R1 : Fin (γp ∥ μ).n → Fin γl.n → Prop},
    GoodD γp → GoodD μ → GoodD γl →
    (∀ k a, R1 k a → γp.ty (reorderDL γp μ k) ⊑ γl.ty a) →
    SymLiftAll R1 (γp ∥ μ).C γl.C →
    RefDist γl B →
    SymLiftAll (fun (k : Fin (γp ∥ μ).n) (c : Fin (γl ∥ B).n) =>
        R1 k (reorderDL γl B c) ∧
        γl.ty (reorderDL γl B c) =ʳ B.ty (reorderDR γl B c) ∧
        μ.ty (reorderDR γp μ k) ⊑ B.ty (reorderDR γl B c) ⊢[.r] (γp ∥ᵗ μ).ty k ⊑̇ (γl ∥ᵗ B).ty c ∧
        μ.ty (reorderDR γp μ k) ⊑ B.ty (reorderDR γl B c))
      (γp ∥ μ).C (γl ∥ B).C
  | γp, μ, γl, B, R1, hgp, hgμ, hgl, hR1, hrun, href => by
      refine (eprec_reorderD_glb_tags hgl
          (fun k a h => EPrecTy.trans ((tagPrec_reorderD .l hgp hgμ).cell k)
            (eprecTy_of_precTy (hR1 k a h)))
          hrun href).mono fun k c ⟨_, hleft⟩ => ?_
      have hrefT := reorderD_cell_eq _ _ c
      have hdst : PrecTy (μ.ty (reorderDR γp μ k)) (B.ty (reorderDR γl B c)) := by
        rw [← reorderD_cell_eq _ _ k, ← hrefT]; exact hR1 k _ hleft
      exact ⟨hleft, reorderD_cell_live hgl c,
        tagPrecTy_reorderTy_glb (hgp.tys _) (hgμ.tys _) (hgl.tys _) (hrefT ▸ hgl.tys _)
          (hR1 k _ hleft) (hrefT ▸ RefTy.refl (hgl.tys _))
          (reorderD_cell_live hgp k) (tagReorderD_ty_spec γp μ k) (tagReorderD_ty_spec γl B c),
        hdst⟩

end GradualProb.TPLC
