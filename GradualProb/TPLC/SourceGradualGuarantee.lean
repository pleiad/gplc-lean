import GradualProb.TPLC.GradualGuarantee

/-!
# Monotone canonical elaboration and the dynamic gradual guarantee for GPLC

This module proves Lemma 55 (monotone canonical elaboration): the canonical
elaboration of a well-typed GPLC term lies above, in the typed term precision
of TPLC (`PrecV`/`PrecT`, in the environments of the two judgments), every
elaboration of every more precise term under related contexts.  Composed with
Lemma 11 (elaboration preserves types) and Theorem 5 (dynamic gradual
guarantee for TPLC), it gives Theorem 6 (dynamic gradual guarantee for GPLC).

## Main results

* `elab_canon_val`, `elab_canon_tm`: Lemma 55 (monotone canonical elaboration).
* `GPLC.dynamic_gradual_guarantee`: Theorem 6 (dynamic gradual guarantee for
  GPLC).

## Reading guide

* `wfann_ftyV`/`wfann_ftyT`: well-typed source terms have well-formed
  annotations, a hypothesis of `GPLC.static_gradual_guarantee_tm`.
* `precD_elab`/`precTy_elab`: Lemma 52 (precision of elaborated types), the
  types of two related elaborations are related by precision.  Elaboration
  keeps the source types, so this follows from Theorem 2 (static gradual
  guarantee).  It discharges the coupling premise of the `let` rule of term
  precision.
* `eprec_tagMeetTy_mono`, `tagPrecTy_toTag` and the tag-aware monotonicity of the
  tagged meet (`tagPrecTy_tagMeetTy` and its distribution-level companions,
  each stated once for the tag `π`; together Lemma 53, tag-aware monotonicity
  of the meet): the
  evidence clauses of the ascription rules `PrecV.asc`, `PrecT.ascV` and
  `PrecT.ascT` for the evidences the elaboration produces.
* `prec_letin1`: Lemma 54 (precision of single-entry lets), the `let` rule of
  term precision for the single-body bindings the elaboration introduces.
-/

namespace GradualProb.TPLC

open GradualProb.GPLC
open scoped BigOperators


/-! ## Well-formed annotations from typing -/

/- Well-typed GPLC values and terms, under a well-formed context, have
well-formed annotations (Definition 14, `GPLC.WfAnnV`/`GPLC.WfAnnT`). -/
mutual
/-- A well-typed GPLC value under a well-formed context has well-formed
annotations. -/
theorem wfann_ftyV : ∀ {Γ v σ}, GPLC.HasTyV Γ v σ → CtxGood Γ → WfAnnV v
  | _, _, _, .var _, _ => .var
  | _, _, _, .real, _ => .real
  | _, _, _, .bool, _ => .bool
  | _, _, _, .lam hm hτ, hΓ =>
      .lam hτ (wfann_ftyT hm (ctxGood_cons (goodTy_liftF hτ) hΓ))
/-- A well-typed GPLC term under a well-formed context has well-formed
annotations. -/
theorem wfann_ftyT : ∀ {Γ m D}, GPLC.HasTyT Γ m D → CtxGood Γ → WfAnnT m
  | _, _, _, .val hv, hΓ => .val (wfann_ftyV hv hΓ)
  | _, _, _, .app hv hw _ _, hΓ => .app (wfann_ftyV hv hΓ) (wfann_ftyV hw hΓ)
  -- The body of the `let` is typed once per entry of the bound term's type
  -- (one typing derivation per entry); its annotations are read off the
  -- derivation for entry 0, which exists
  -- because that type is well formed (its probabilities sum to 1, so it has
  -- at least one entry).
  | _, _, _, @GPLC.HasTyT.letin _ _ _ D F hm hbody, hΓ => by
      refine .letin (wfann_ftyT hm hΓ) ?_
      have hgD : GoodD D := good_tm hm hΓ
      have hpos : 0 < D.n := hgD.good.pos
      exact wfann_ftyT (hbody ⟨0, hpos⟩)
        (ctxGood_cons (hgD.tys ⟨0, hpos⟩) hΓ)
  | _, _, _, .choice _ _ hm hn, hΓ =>
      .choice (wfann_ftyT hm hΓ) (wfann_ftyT hn hΓ)
  | _, _, _, .choiceU hm hn, hΓ => .choice (wfann_ftyT hm hΓ) (wfann_ftyT hn hΓ)
  | _, _, _, .ascT hm _ hT, hΓ => .ascT (wfann_ftyT hm hΓ) hT
  | _, _, _, .ascV hv _ hτ, hΓ => .ascV (wfann_ftyV hv hΓ) hτ
  | _, _, _, .ite hv _ hm hn _, hΓ =>
      .ite (wfann_ftyV hv hΓ) (wfann_ftyT hm hΓ) (wfann_ftyT hn hΓ)
  | _, _, _, .add hv _ hw _, hΓ => .add (wfann_ftyV hv hΓ) (wfann_ftyV hw hΓ)
end

/-! ## Precision of elaborated types -/

/-- Lemma 52 (precision of elaborated types), distribution types: the types of
two elaborations of related source terms, under related well-formed contexts,
are related by precision. Elaboration keeps the source types, so this is
Theorem 2 (static gradual guarantee) on the source terms. -/
theorem precD_elab {Γ Γ' : List FTy} {m m' : GPLC.Tm} {tm tm' : Tm}
    {D D' : FDist} (hel : Γ ⊢ m : D ⇝ tm) (hel' : Γ' ⊢ m' : D' ⇝ tm')
    (hp : m ⊑ m') (hctx : Γ ⊑ Γ')
    (hg : CtxGood Γ) (hg' : CtxGood Γ') : D ⊑ D' := by
  obtain ⟨D'', hty'', hprec⟩ :=
    static_gradual_guarantee_tm (elab_sound_tm hel) hctx hp hg hg'
      (wfann_ftyT (elab_sound_tm hel') hg')
  obtain rfl := GPLC.det_tm hty'' (elab_sound_tm hel')
  exact hprec

/-- Lemma 52 (precision of elaborated types), simple types: the types of two
elaborations of related source values, under related well-formed contexts, are
related by precision. -/
theorem precTy_elab {Γ Γ' : List FTy} {v v' : GPLC.Val} {tv tv' : Val}
    {σ σ' : FTy} (hel : Γ ⊢ v : σ ⇝ tv) (hel' : Γ' ⊢ v' : σ' ⇝ tv')
    (hp : v ⊑ v') (hctx : Γ ⊑ Γ')
    (hg : CtxGood Γ) (hg' : CtxGood Γ') : σ ⊑ σ' := by
  obtain ⟨σ'', hty'', hprec⟩ :=
    static_gradual_guarantee_val (elab_sound_val hel) hctx hp hg hg'
      (wfann_ftyV (elab_sound_val hel') hg')
  obtain rfl := GPLC.det_val hty'' (elab_sound_val hel')
  exact hprec
/-! ## Canonical-vs-canonical evidence precision -/

/-- The tagged meets of two pairs of related types have related evidences
(compared through `toF`, as term precision compares evidences).  It follows
from Lemma 12 (monotonicity of evidence combination), `meetTy_mono`. -/
theorem eprec_tagMeetTy_mono {σ τ σ' τ' : FTy} {ε ε' : TagTy}
    (hg : GoodTy σ) (hgτ : GoodTy τ) (hg' : GoodTy σ') (hgτ' : GoodTy τ')
    (h1 : EPrecTy σ σ') (h2 : EPrecTy τ τ')
    (hpin : tagMeetTy σ τ = some ε) (hpin' : tagMeetTy σ' τ' = some ε')
    (hgε : GoodTy ε.toF) :
    EPrecTy ε.toF ε'.toF := by
  have hme : meetTy σ τ = some ε.toF := by
    have h := tagMeetTy_toF σ τ
    rw [hpin, Option.map_some] at h
    exact h.symm
  have hme' : meetTy σ' τ' = some ε'.toF := by
    have h := tagMeetTy_toF σ' τ'
    rw [hpin', Option.map_some] at h
    exact h.symm
  obtain ⟨mm', hm', -, hprec⟩ := meetTy_mono hg hgτ hg' hgτ' h1 h2 hme hgε
  rw [hme'] at hm'
  obtain rfl := Option.some.inj hm'
  exact hprec

/-! ## Tag-aware precision of diagonal evidences

The elaboration gives a literal or a λ the diagonal evidence `σ.toTag`, so the
evidence clauses of `PrecV.asc` reduce to the precision of the types: the tags
are identities and the coupling of the entries is the one of the precision itself. -/

/-- The distribution case of `tagPrecTy_toTag`, given the entrywise precision: the coupling
of the precision, read through the identity tags. -/
theorem tagPrecD_toTagD_of_cells {π : Side} {D D' : FDist} (R : Fin D.n → Fin D'.n → Prop)
    (hR : ∀ i j, R i j → PrecTy (D.ty i) (D'.ty j)) (hl : SymLiftAll R D.C D'.C)
    (hcell : ∀ i j, R i j → TagPrecTy π (D.ty i) (D'.ty j) (D.ty i).toTag (D'.ty j).toTag) :
    TagPrecD π D.toTag D'.toTag D D' := by
  obtain ⟨n, ty, C⟩ := D
  obtain ⟨n', ty', C'⟩ := D'
  cases π <;> exact .mk R (fun c => c.isLt) (fun c => c.isLt) hcell hR hl

mutual
/-- Lemma 53 (tag-aware monotonicity of the meet), item 1: diagonal evidences of
related types are related by tag-aware precision along either tag (the two
judged types of a diagonal evidence are the same). -/
theorem tagPrecTy_toTag (π : Side) : ∀ {σ σ' : FTy}, σ ⊑ σ' →
    σ ⊑ σ' ⊢[π] σ.toTag ⊑̇ σ'.toTag
  | _, _, .real => .flat (fun h => h.1) .real
  | _, _, .bool => .flat (fun h => h.1) .bool
  | _, _, .unk => .flat (fun h => h.2.1) .unk
  | _, _, .arrow hs hD => .arrow (tagPrecTy_toTag π hs) (tagPrecD_toTagD π hD)
/-- Lemma 53 (tag-aware monotonicity of the meet), item 1, distribution
level. -/
theorem tagPrecD_toTagD (π : Side) : ∀ {D D' : FDist}, D ⊑ D' →
    D ⊑ D' ⊢[π] D.toTag ⊑̇ D'.toTag
  | _, _, .mk R _ _ hR hl _ _ =>
      tagPrecD_toTagD_of_cells R hR hl fun i j h => tagPrecTy_toTag π (hR i j h)
end

/-! ## Tag-aware monotonicity of the tagged meet

What the evidence clauses of `PrecV.asc`, `PrecT.ascV` and `PrecT.ascT`
require of the evidences the elaboration produces:

    a ⊑ a′ , b ⊑ b′ , ε = tagMeetTy a b , ε′ = tagMeetTy a′ b′  ⟹  a ⊑ a′ ⊢[π] ε ⊑̇ ε′

where `a` is the operand whose tags `π` the meet keeps: the annotation for
`r` and the type of the ascribed value for `l`. When `a` is not an arrow this is
`eprec_tagMeetTy_mono`. In the arrow case the evidence is the tagged meet of the
domains and of the codomains, so the distribution level is the entrywise
monotonicity of the meet (`meetD_mono_core`). The case `b′ = ?` has its own
lemma: there the less precise evidence is the diagonal evidence of `a′`, and the
coupling goes from the more precise meet to `a′` (`coup_comp_fun` along the
tag `π` of the meet). -/

/-- The index, in the operand `a`, of an entry of the meet whose tags `π` point
into `a` (`meetDL` or `meetDR`). -/
noncomputable def meetDTag :
    (π : Side) → (a b : FDist) → Fin (meetD (π.pick a b) (π.pick b a)).n → Fin a.n
  | .l, a, b => meetDL a b
  | .r, a, b => meetDR b a

/-- The index, in the other operand `b`, of an entry of the meet whose tags `π`
point into `a`. -/
noncomputable def meetDOther :
    (π : Side) → (a b : FDist) → Fin (meetD (π.pick a b) (π.pick b a)).n → Fin b.n
  | .l, a, b => meetDR a b
  | .r, a, b => meetDL b a

/-- `tagMeetD_ty_spec` along `π`. -/
theorem tagMeetD_ty_pick (π : Side) (a b : FDist)
    (c : Fin (tagMeetD (π.pick a b) (π.pick b a)).n) :
    tagMeetTy (π.pick (a.ty (meetDTag π a b c)) (b.ty (meetDOther π a b c)))
        (π.pick (b.ty (meetDOther π a b c)) (a.ty (meetDTag π a b c)))
      = some ((tagMeetD (π.pick a b) (π.pick b a)).ty c) := by
  cases π <;> exact tagMeetD_ty_spec _ _ c

/-- `?` is a unit of the tagged meet of two types, on either side. -/
theorem tagMeetTy_pick_unk (π : Side) (x : FTy) :
    tagMeetTy (π.pick x .unk) (π.pick .unk x) = some x.toTag := by
  cases π
  · exact tagMeetTy_unk_right x
  · rfl

/-- A defined tagged meet of an arrow `s → D` with a type `b`: either `b` is
`?` and the meet is the diagonal of `s → D`, or `b` is an arrow and the meet is
the arrow of the tagged meets of the domains and of the codomains, in the same
order. -/
theorem tagMeetTy_pick_arrow {π : Side} {s b : FTy} {D : FDist} {ε : TagTy}
    (hm : tagMeetTy (π.pick (.arrow s D) b) (π.pick b (.arrow s D)) = some ε) :
    (b = .unk ∧ ε = (FTy.arrow s D).toTag) ∨
      ∃ s0 D0 s3, b = .arrow s0 D0 ∧ tagMeetTy (π.pick s s0) (π.pick s0 s) = some s3 ∧
        ε = .arrow s3 (tagMeetD (π.pick D D0) (π.pick D0 D)) := by
  cases π <;> cases b with
  | real | bool => simp [Side.pick, tagMeetTy] at hm
  | unk =>
      refine .inl ⟨rfl, ?_⟩
      simp only [Side.pick, tagMeetTy_unk_right] at hm
      exact (Option.some.inj hm).symm
  | arrow s0 D0 =>
      refine .inr ⟨s0, D0, ?_⟩
      simp only [Side.pick, tagMeetTy] at hm
      split at hm
      · exact ⟨_, rfl, ‹_›, (Option.some.inj hm).symm⟩
      · exact nomatch hm

/-- `eprec_tagMeetTy_mono` along `π`. -/
theorem eprecTy_tagMeetTy_pick (π : Side) {a b a' b' : FTy} {ε ε' : TagTy}
    (hga : GoodTy a) (hgb : GoodTy b) (hga' : GoodTy a') (hgb' : GoodTy b')
    (ha : EPrecTy a a') (hb : EPrecTy b b')
    (hm : tagMeetTy (π.pick a b) (π.pick b a) = some ε)
    (hm' : tagMeetTy (π.pick a' b') (π.pick b' a') = some ε') (hgε : GoodTy ε.toF) :
    EPrecTy ε.toF ε'.toF := by
  cases π
  · exact eprec_tagMeetTy_mono hga hgb hga' hgb' ha hb hm hm' hgε
  · exact eprec_tagMeetTy_mono hgb hga hgb' hga' hb ha hm hm' hgε

/-- The distribution case of `tagPrecTy_tagMeetTy`, given the entrywise precision: the
coupling is that of Lemma 12 (`meetD_mono_core`) built from the two precision
couplings. -/
theorem tagPrecD_tagMeetD_of_cells {π : Side} {a b a' b' : FDist}
    (Ra : Fin a.n → Fin a'.n → Prop) (hRa : ∀ i j, Ra i j → PrecTy (a.ty i) (a'.ty j))
    (hca : SymLiftAll Ra a.C a'.C) (hb : PrecD b b')
    (hcell : ∀ c c', Ra (meetDTag π a b c) (meetDTag π a' b' c') →
      PrecTy (b.ty (meetDOther π a b c)) (b'.ty (meetDOther π a' b' c')) →
      TagPrecTy π (a.ty (meetDTag π a b c)) (a'.ty (meetDTag π a' b' c'))
        ((tagMeetD (π.pick a b) (π.pick b a)).ty c)
        ((tagMeetD (π.pick a' b') (π.pick b' a')).ty c')) :
    TagPrecD π (tagMeetD (π.pick a b) (π.pick b a)) (tagMeetD (π.pick a' b') (π.pick b' a'))
      a a' := by
  obtain ⟨Rb, -, -, hRb, hcb, -, -⟩ := hb
  have hEa : ∀ i j, Ra i j → EPrecTy (a.ty i) (a'.ty j) := fun i j h => eprecTy_of_precTy (hRa i j h)
  have hEb : ∀ i j, Rb i j → EPrecTy (b.ty i) (b'.ty j) := fun i j h => eprecTy_of_precTy (hRb i j h)
  cases π
  · exact .mk _ (fun c => (meetDL a b c).isLt) (fun c => (meetDL a' b' c).isLt)
      (fun _ _ h => hcell _ _ h.1 (hRb _ _ h.2)) (fun _ _ h => hRa _ _ h.1)
      (meetD_mono_core hEa hEb hca hcb)
  · exact .mk _ (fun c => (meetDR b a c).isLt) (fun c => (meetDR b' a' c).isLt)
      (fun _ _ h => hcell _ _ h.2 (hRb _ _ h.1)) (fun _ _ h => hRa _ _ h.2)
      (meetD_mono_core hEb hEa hcb hca)

/-- The distribution case of `tagPrecTy_tagMeetTy` with `b′ = ?`, given the
entrywise precision: the coupling goes from the more precise meet to `a′` along the tag `π`
of the meet. -/
theorem tagPrecD_tagMeetD_toTag_of_cells {π : Side} {a b a' : FDist}
    (hga : GoodD a) (hgb : GoodD b) (hgm : GoodD (meetD (π.pick a b) (π.pick b a)))
    (Ra : Fin a.n → Fin a'.n → Prop) (hRa : ∀ i j, Ra i j → PrecTy (a.ty i) (a'.ty j))
    (hca : SymLiftAll Ra a.C a'.C)
    (hcell : ∀ c c', Ra (meetDTag π a b c) c' →
      TagPrecTy π (a.ty (meetDTag π a b c)) (a'.ty c')
        ((tagMeetD (π.pick a b) (π.pick b a)).ty c) (a'.ty c').toTag) :
    TagPrecD π (tagMeetD (π.pick a b) (π.pick b a)) a'.toTag a a' := by
  obtain ⟨n', ty', C'⟩ := a'
  cases π
  · exact .mk _ (fun c => (meetDL a b c).isLt) (fun c => c.isLt) hcell (fun _ _ h => hRa _ _ h)
      (coup_comp_fun (Z := ⟨n', ty', C'⟩) (tagPrec_meetD .l hga hgb) hgm.good hca)
  · exact .mk _ (fun c => (meetDR b a c).isLt) (fun c => c.isLt) hcell (fun _ _ h => hRa _ _ h)
      (coup_comp_fun (Z := ⟨n', ty', C'⟩) (tagPrec_meetD .r hgb hga) hgm.good hca)

mutual
/-- Lemma 53 (tag-aware monotonicity of the meet), item 2, simple types:
if `a ⊑ a′` and `b ⊑ b′`, then the tagged meets of `a, b` and of `a′, b′` are
related by tag-aware precision against `a, a′` along the tag `π` that the meet
keeps from `a`. -/
theorem tagPrecTy_tagMeetTy {π : Side} : ∀ {a b a' b' : FTy} {ε ε' : TagTy},
    GoodTy a → GoodTy b → GoodTy a' → GoodTy b' →
    a ⊑ a' → b ⊑ b' →
    π.pick a b ⊓ᵗ π.pick b a = some ε →
    π.pick a' b' ⊓ᵗ π.pick b' a' = some ε' → GoodTy ε.toF →
    a ⊑ a' ⊢[π] ε ⊑̇ ε'
  | _, _, _, _, _, _, hga, hgb, hga', hgb', .real, hb, hm, hm', hgε =>
      .flat (fun h => h.1)
        (eprecTy_tagMeetTy_pick π hga hgb hga' hgb' .real (eprecTy_of_precTy hb) hm hm' hgε)
  | _, _, _, _, _, _, hga, hgb, hga', hgb', .bool, hb, hm, hm', hgε =>
      .flat (fun h => h.1)
        (eprecTy_tagMeetTy_pick π hga hgb hga' hgb' .bool (eprecTy_of_precTy hb) hm hm' hgε)
  | _, _, _, _, _, _, hga, hgb, hga', hgb', .unk, hb, hm, hm', hgε =>
      .flat (fun h => h.2.1)
        (eprecTy_tagMeetTy_pick π hga hgb hga' hgb' .unk (eprecTy_of_precTy hb) hm hm' hgε)
  | _, _, _, _, _, _, hga, hgb, hga', hgb', .arrow hs hD, hb, hm, hm', hgε => by
      obtain ⟨rfl, rfl⟩ | ⟨s0, D0, s3, rfl, hs3, rfl⟩ := tagMeetTy_pick_arrow hm
      · -- `b = ?`: both evidences are diagonal (`? ⊑ b′` forces `b′ = ?`)
        cases hb
        rw [tagMeetTy_pick_unk] at hm'
        obtain rfl := Option.some.inj hm'
        exact tagPrecTy_toTag π (.arrow hs hD)
      · cases hga with
        | arrow hgs hgD =>
        cases hgb with
        | arrow hgs0 hgD0 =>
        cases hga' with
        | arrow hgs' hgD' =>
        cases hgε with
        | arrow hgs3 hgd3 =>
        cases hb with
        | unk =>
            -- `b′ = ?`: the less precise evidence is the diagonal of `a′`
            rw [tagMeetTy_pick_unk] at hm'
            obtain rfl := Option.some.inj hm'
            exact .arrow
              (tagPrecTy_tagMeetTy hgs hgs0 hgs' .unk hs .unk hs3 (tagMeetTy_pick_unk π _) hgs3)
              (tagPrecD_tagMeetD_toTag hgD hgD0 hgD' hD ((tagMeetD_toF _ _) ▸ hgd3))
        | arrow hbs hbD =>
            cases hgb' with
            | arrow hgs0' hgD0' =>
            obtain ⟨⟨⟩, -⟩ | ⟨_, _, s3', ⟨⟩, hs3', rfl⟩ := tagMeetTy_pick_arrow hm'
            exact .arrow (tagPrecTy_tagMeetTy hgs hgs0 hgs' hgs0' hs hbs hs3 hs3' hgs3)
              (tagPrecD_tagMeetD hgD hgD0 hgD' hgD0' hD hbD ((tagMeetD_toF _ _) ▸ hgd3))
/-- Lemma 53 (tag-aware monotonicity of the meet), item 2, distribution
types: both sides tagged meets. -/
theorem tagPrecD_tagMeetD {π : Side} : ∀ {a b a' b' : FDist},
    GoodD a → GoodD b → GoodD a' → GoodD b' →
    a ⊑ a' → b ⊑ b' → GoodD (π.pick a b ⊓ π.pick b a) →
    a ⊑ a' ⊢[π] π.pick a b ⊓ᵗ π.pick b a ⊑̇ π.pick a' b' ⊓ᵗ π.pick b' a'
  | a, b, a', b', hga, hgb, hga', hgb', .mk Ra _ _ hRa hca _ _, hb, hgm =>
      tagPrecD_tagMeetD_of_cells Ra hRa hca hb fun c c' hR hRb =>
        tagPrecTy_tagMeetTy (hga.tys _) (hgb.tys _) (hga'.tys _) (hgb'.tys _) (hRa _ _ hR) hRb
          (tagMeetD_ty_pick π a b c) (tagMeetD_ty_pick π a' b' c')
          (by rw [tagMeetD_ty_toF]; exact hgm.tys c)
/-- Lemma 53 (tag-aware monotonicity of the meet), item 2, distribution
types with the less precise operand `b′ = ?`: the less precise evidence is the
diagonal evidence of `a′`. -/
theorem tagPrecD_tagMeetD_toTag {π : Side} : ∀ {a b a' : FDist},
    GoodD a → GoodD b → GoodD a' → a ⊑ a' → GoodD (π.pick a b ⊓ π.pick b a) →
    a ⊑ a' ⊢[π] π.pick a b ⊓ᵗ π.pick b a ⊑̇ a'.toTag
  | a, b, _, hga, hgb, hga', .mk Ra _ _ hRa hca _ _, hgm =>
      tagPrecD_tagMeetD_toTag_of_cells hga hgb hgm Ra hRa hca fun c _ hR =>
        tagPrecTy_tagMeetTy (hga.tys _) (hgb.tys _) (hga'.tys _) GoodTy.unk (hRa _ _ hR) .unk
          (tagMeetD_ty_pick π a b c) (tagMeetTy_pick_unk π _)
          (by rw [tagMeetD_ty_toF]; exact hgm.tys c)
end

/-! ## Single-body A-normal bindings

The elaboration of `app`, `+` and `if` binds each coerced operand with a
single-body `let`.  Its bound term is a value ascription, of a point type, so
the premises of the `let` rule of term precision reduce to the precision of
that one pair of types. -/

/-- Lemma 54 (precision of single-entry lets): if `s ⊑ s′` have the Dirac types
`pointF σ`, `pointF σ′` with `σ ⊑ σ′`, and the bodies are related under the
extended contexts, then the single-entry `let`s are related. -/
theorem prec_letin1 {Γ Γ' : List FTy} {s s' body body' : Tm} {σ σ' : FTy}
    (hs : Γ ⊑ Γ' ⊢ s ⊑ s')
    (hty : Γ ⊢ s : pointF σ) (hty' : Γ' ⊢ s' : pointF σ')
    (hb : σ :: Γ ⊑ σ' :: Γ' ⊢ body ⊑ body')
    (hσ : σ ⊑ σ') :
    Γ ⊑ Γ' ⊢ .letin s 1 (fun _ => body) ⊑ .letin s' 1 (fun _ => body') := by
  refine PrecT.letin hs ?_ ?_
  · intro D D' h h' i j hij hilen hjlen
    obtain rfl := det_tm h hty
    obtain rfl := det_tm h' hty'
    have hi : i = 0 := Subsingleton.elim i 0
    have hj : j = 0 := Subsingleton.elim j 0
    subst hi; subst hj
    simpa using hb
  · intro D D' h h' p hp
    obtain rfl := det_tm h hty
    obtain rfl := det_tm h' hty'
    exact ⟨fun _ => 1, rfl, .point hp rfl hσ⟩

/-! ## Monotone canonical elaboration

The induction is on the typing derivation of the less precise term.  Its
invariant: the canonical elaboration of that term lies above, in the
environments of the two judgments, every elaboration of every more precise
term under related contexts.  The `let` rule of term precision needs the
precision of the bound terms' elaborated types, which `precD_elab` provides. -/

mutual
/-- Lemma 55 (monotone canonical elaboration), for values: a well-typed GPLC
value `v′` has an elaboration `tv′` such that every elaboration `tv` of a more
precise value under a related well-formed context satisfies `Γ ⊑ Γ′ ⊢ tv ⊑ tv′`. -/
theorem elab_canon_val : ∀ {Γ' : List FTy} {v' : GPLC.Val} {σ' : FTy},
    Γ' ⊢ v' : σ' → CtxGood Γ' →
    ∃ tv', Γ' ⊢ v' : σ' ⇝ tv' ∧
      (∀ {Γ : List FTy} {v : GPLC.Val} {tv : Val} {σ : FTy},
        Γ ⊢ v : σ ⇝ tv → v ⊑ v' → Γ ⊑ Γ' → CtxGood Γ →
        Γ ⊑ Γ' ⊢ tv ⊑ tv')
  | Γ', _, _, .var hx', hΓ' => by
      refine ⟨_, .evar hx', ?_⟩
      intro Γ v tv σ helab hprec hctx hgΓ
      cases hprec with
      | var =>
        cases helab with
        | evar hx => exact .var
  | Γ', _, _, .real, hΓ' => by
      refine ⟨_, .ereal, ?_⟩
      intro Γ v tv σ helab hprec hctx hgΓ
      cases hprec with
      | real =>
        cases helab with
        | ereal =>
          exact .asc (.flat (fun h => h.1) .real)
            (fun hu hu' => by
              cases hu; cases hu'
              exact .flat (fun h => h.1) .real)
            .real .real
  | Γ', _, _, .bool, hΓ' => by
      refine ⟨_, .ebool, ?_⟩
      intro Γ v tv σ helab hprec hctx hgΓ
      cases hprec with
      | bool =>
        cases helab with
        | ebool =>
          exact .asc (.flat (fun h => h.1) .bool)
            (fun hu hu' => by
              cases hu; cases hu'
              exact .flat (fun h => h.1) .bool)
            .bool .bool
  | Γ', _, _, .lam (τ := τ') (D := D') hm' hτ', hΓ' => by
      obtain ⟨tmb', helb', hcompb'⟩ :=
        elab_canon_tm hm' (ctxGood_cons (goodTy_liftF hτ') hΓ')
      refine ⟨_, .elam helb' hτ', ?_⟩
      intro Γ v tv σ helab hprec hctx hgΓ
      cases hprec with
      | lam hττ' hpm =>
        cases helab with
        | @elam _ _ _ _ Db hm hτ =>
          have hgb' := ctxGood_cons (goodTy_liftF hτ') hΓ'
          have hctxb := precCtx_cons (hττ') hctx
          have hgb := ctxGood_cons (goodTy_liftF hτ) hgΓ
          have htpb := hcompb' hm hpm hctxb hgb
          have hDbD' : PrecD Db D' :=
            precD_elab hm helb' hpm hctxb hgb hgb'
          have harr := PrecTy.arrow (hττ') hDbD'
          refine .asc (tagPrecTy_toTag .r harr) ?_
            (.lam (hττ') htpb) harr
          -- the type of the raw λ in the judgment's environment is the
          -- elaborated one
          intro σv σv' hu hu'
          cases hu with
          | lam hbty _ =>
            cases hu' with
            | lam hbty' _ =>
              obtain rfl := det_tm hbty (elab_preserves_tm hm hgb)
              obtain rfl := det_tm hbty' (elab_preserves_tm helb' hgb')
              exact tagPrecTy_toTag .l harr

/-- Lemma 55 (monotone canonical elaboration), for terms: a well-typed GPLC
term `m′` has an elaboration `tm′` such that every elaboration `tm` of a more
precise term under a related well-formed context satisfies `Γ ⊑ Γ′ ⊢ tm ⊑ tm′`. -/
theorem elab_canon_tm : ∀ {Γ' : List FTy} {m' : GPLC.Tm} {D' : FDist},
    Γ' ⊢ m' : D' → CtxGood Γ' →
    ∃ tm', Γ' ⊢ m' : D' ⇝ tm' ∧
      (∀ {Γ : List FTy} {m : GPLC.Tm} {tm : Tm} {D : FDist},
        Γ ⊢ m : D ⇝ tm → m ⊑ m' → Γ ⊑ Γ' → CtxGood Γ →
        Γ ⊑ Γ' ⊢ tm ⊑ tm')
  | Γ', _, _, .val hv', hΓ' => by
      obtain ⟨tv', helv', hcompv'⟩ := elab_canon_val hv' hΓ'
      refine ⟨_, .eval helv', ?_⟩
      intro Γ m tm D helab hprec hctx hgΓ
      cases hprec with
      | val hpv =>
        cases helab with
        | eval hv => exact .val (hcompv' hv hpv hctx hgΓ)
  | Γ', _, _, .ascV (τ := τ') hv' hcons' hτ', hΓ' => by
      obtain ⟨tv', helv', hcompv'⟩ := elab_canon_val hv' hΓ'
      obtain ⟨ε', hpin', -, -⟩ :=
        hvtag_tagMeetTy (good_val hv' hΓ') (goodTy_liftF hτ')
          (econsTy_of_consTy hcons')
      refine ⟨_, .eascV helv' hcons' hτ' hpin', ?_⟩
      intro Γ m tm D helab hprec hctx hgΓ
      cases hprec with
      | ascV hpv hττ' =>
        cases helab with
        | @eascV _ _ _ σv ε _ hv hcons hτ hpin =>
          have htpv := hcompv' hv hpv hctx hgΓ
          have hgσv : GoodTy σv := good_val (elab_sound_val hv) hgΓ
          have hgσv' : GoodTy _ := good_val hv' hΓ'
          have hσvv' : PrecTy σv _ := precTy_elab hv helv' hpv hctx hgΓ hΓ'
          have hgε : GoodTy ε.toF :=
            (hvtag_of_tagMeetTy hgσv (goodTy_liftF hτ) hcons hpin).2
          refine .ascV
            (tagPrecTy_tagMeetTy (goodTy_liftF hτ) hgσv (goodTy_liftF hτ')
              hgσv' (hττ') hσvv' hpin hpin' hgε)
            ?_ htpv (hττ')
          intro σ0 σ0' hu hu'
          obtain rfl := det_val hu (elab_preserves_val hv hgΓ)
          obtain rfl := det_val hu' (elab_preserves_val helv' hΓ')
          exact tagPrecTy_tagMeetTy hgσv (goodTy_liftF hτ) hgσv'
            (goodTy_liftF hτ') hσvv' (hττ') hpin hpin' hgε
  | Γ', _, _, .ascT (D := Dm') (T := T') hm' hcons' hT', hΓ' => by
      obtain ⟨tms', helm', hcompm'⟩ := elab_canon_tm hm' hΓ'
      refine ⟨_, .eascT helm' hcons' hT', ?_⟩
      intro Γ m tm D helab hprec hctx hgΓ
      cases hprec with
      | @ascT _ _ T _ hpm hTT' =>
        cases helab with
        | @eascT _ _ _ Dm _ hm hcons hT =>
          have htpm := hcompm' hm hpm hctx hgΓ
          have hgDm : GoodD Dm := good_tm (elab_sound_tm hm) hgΓ
          have hgDm' : GoodD Dm' := good_tm hm' hΓ'
          have hDmDm' : PrecD Dm Dm' :=
            precD_elab hm helm' hpm hctx hgΓ hΓ'
          have hgme : GoodD (meetD Dm (liftFDist T)) :=
            goodD_meetD hgDm (goodD_liftFD hT) (econsD_of_consD hcons)
          refine .ascT (fun _ _ => tagPrecD_tagMeetD (goodD_liftFD hT) hgDm
              (goodD_liftFD hT') hgDm' (hTT') hDmDm' hgme)
            ?_ htpm (hTT')
          intro D0 D0' hu hu'
          obtain rfl := det_tm hu (elab_preserves_tm hm hgΓ)
          obtain rfl := det_tm hu' (elab_preserves_tm helm' hΓ')
          exact tagPrecD_tagMeetD hgDm (goodD_liftFD hT) hgDm'
            (goodD_liftFD hT') hDmDm' (hTT') hgme
  | Γ', _, _, .add hv' hc1' hw' hc2', hΓ' => by
      obtain ⟨tv', helv', hcompv'⟩ := elab_canon_val hv' hΓ'
      obtain ⟨tw', helw', hcompw'⟩ := elab_canon_val hw' hΓ'
      obtain ⟨ε1', hpin1', -, -⟩ :=
        hvtag_tagMeetTy (good_val hv' hΓ') .real (econsTy_of_consTy hc1')
      obtain ⟨ε2', hpin2', -, -⟩ :=
        hvtag_tagMeetTy (good_val hw' hΓ') .real (econsTy_of_consTy hc2')
      refine ⟨_, .eadd helv' helw' hc1' hc2' hpin1' hpin2', ?_⟩
      intro Γ m tm D helab hprec hctx hgΓ
      cases hprec with
      | add hpv hpw =>
        cases helab with
        | @eadd _ _ _ _ _ σ1 σ2 ε1 ε2 hv hw hc1 hc2 hpin1 hpin2 =>
          have htpv := hcompv' hv hpv hctx hgΓ
          have htpw := hcompw' hw hpw hctx hgΓ
          have hgσ1 : GoodTy σ1 := good_val (elab_sound_val hv) hgΓ
          have hgσ2 : GoodTy σ2 := good_val (elab_sound_val hw) hgΓ
          have hgσ1' : GoodTy _ := good_val hv' hΓ'
          have hgσ2' : GoodTy _ := good_val hw' hΓ'
          have hσ1 : PrecTy σ1 _ := precTy_elab hv helv' hpv hctx hgΓ hΓ'
          have hσ2 : PrecTy σ2 _ := precTy_elab hw helw' hpw hctx hgΓ hΓ'
          obtain ⟨hv1, hgε1⟩ := hvtag_of_tagMeetTy hgσ1 .real hc1 hpin1
          obtain ⟨hv2, hgε2⟩ := hvtag_of_tagMeetTy hgσ2 .real hc2 hpin2
          obtain ⟨hv1', hgε1'⟩ := hvtag_of_tagMeetTy hgσ1' .real hc1' hpin1'
          obtain ⟨hv2', hgε2'⟩ := hvtag_of_tagMeetTy hgσ2' .real hc2' hpin2'
          have hty1 : HasTyT Γ (.ascV ε1 _ .real) (pointF .real) :=
            .ascV (elab_preserves_val hv hgΓ) hv1 hgε1 .real
          have hty1' : HasTyT Γ' (.ascV ε1' _ .real) (pointF .real) :=
            .ascV (elab_preserves_val helv' hΓ') hv1' hgε1' .real
          have hty2 : HasTyT (.real :: Γ) (.ascV ε2 _ .real) (pointF .real) :=
            .ascV (hasTy_wk0_val (elab_preserves_val hw hgΓ)) hv2 hgε2 .real
          have hty2' : HasTyT (.real :: Γ') (.ascV ε2' _ .real)
              (pointF .real) :=
            .ascV (hasTy_wk0_val (elab_preserves_val helw' hΓ')) hv2' hgε2'
              .real
          refine prec_letin1 ?_ hty1 hty1' ?_ .real
          · refine .ascV (tagPrecTy_tagMeetTy .real hgσ1 .real hgσ1' .real
                hσ1 hpin1 hpin1' hgε1) ?_ htpv .real
            intro σ0 σ0' hu hu'
            obtain rfl := det_val hu (elab_preserves_val hv hgΓ)
            obtain rfl := det_val hu' (elab_preserves_val helv' hΓ')
            exact tagPrecTy_tagMeetTy hgσ1 .real hgσ1' .real hσ1 .real
              hpin1 hpin1' hgε1
          · refine prec_letin1 ?_ hty2 hty2' (.add .var .var) .real
            refine .ascV (tagPrecTy_tagMeetTy .real hgσ2 .real hgσ2' .real
                hσ2 hpin2 hpin2' hgε2) ?_
              (prec_rename_val htpw (Δ := []) (Δ' := []) rfl rfl rfl) .real
            intro σ0 σ0' hu hu'
            obtain rfl := det_val hu
              (hasTy_wk0_val (elab_preserves_val hw hgΓ))
            obtain rfl := det_val hu'
              (hasTy_wk0_val (elab_preserves_val helw' hΓ'))
            exact tagPrecTy_tagMeetTy hgσ2 .real hgσ2' .real hσ2 .real
              hpin2 hpin2' hgε2
  | Γ', _, _, .app hv' hw' hdc' hcons', hΓ' => by
      obtain ⟨tv', helv', hcompv'⟩ := elab_canon_val hv' hΓ'
      obtain ⟨tw', helw', hcompw'⟩ := elab_canon_val hw' hΓ'
      obtain ⟨hgs', hgD'⟩ := domcod_good hdc' (good_val hv' hΓ')
      obtain ⟨ε1', hpin1', -, -⟩ :=
        hvtag_tagMeetTy (good_val hw' hΓ') hgs' (econsTy_of_consTy hcons')
      obtain ⟨ε2', hpin2', -, -⟩ :=
        hvtag_tagMeetTy (good_val hv' hΓ') (.arrow hgs' hgD')
          (econsTy_of_consTy (domcod_cons hdc' (good_val hv' hΓ')))
      refine ⟨_, .eapp helv' helw' hdc' hcons' hpin1' hpin2', ?_⟩
      intro Γ m tm D helab hprec hctx hgΓ
      cases hprec with
      | app hpv hpw =>
        cases helab with
        | @eapp _ _ _ _ _ σv σw s Db ε1 ε2 hv hw hdc hcons hpin1 hpin2 =>
          have htpv := hcompv' hv hpv hctx hgΓ
          have htpw := hcompw' hw hpw hctx hgΓ
          have hgσv : GoodTy σv := good_val (elab_sound_val hv) hgΓ
          have hgσw : GoodTy σw := good_val (elab_sound_val hw) hgΓ
          have hσv : PrecTy σv _ := precTy_elab hv helv' hpv hctx hgΓ hΓ'
          have hσw : PrecTy σw _ := precTy_elab hw helw' hpw hctx hgΓ hΓ'
          obtain ⟨s2, d2, hdc2, hss, hdd⟩ := domcod_mono hσv hdc hgσv
          obtain ⟨hs_eq, hd_eq⟩ := domcod_det hdc2 hdc'
          subst hs_eq
          subst hd_eq
          obtain ⟨hgs, hgDb⟩ := domcod_good hdc hgσv
          obtain ⟨hva1, hgε1⟩ := hvtag_of_tagMeetTy hgσw hgs hcons hpin1
          obtain ⟨hva2, hgε2⟩ :=
            hvtag_of_tagMeetTy hgσv (.arrow hgs hgDb) (domcod_cons hdc hgσv) hpin2
          obtain ⟨hva1', hgε1'⟩ :=
            hvtag_of_tagMeetTy (good_val hw' hΓ') hgs' hcons' hpin1'
          obtain ⟨hva2', hgε2'⟩ :=
            hvtag_of_tagMeetTy (good_val hv' hΓ') (.arrow hgs' hgD')
              (domcod_cons hdc' (good_val hv' hΓ')) hpin2'
          have hty1 := HasTyT.ascV (elab_preserves_val hw hgΓ) hva1 hgε1 hgs
          have hty1' :=
            HasTyT.ascV (elab_preserves_val helw' hΓ') hva1' hgε1' hgs'
          have hty2 :=
            HasTyT.ascV (hasTy_wk0_val (τ := s)
              (elab_preserves_val hv hgΓ)) hva2 hgε2 (GoodTy.arrow hgs hgDb)
          have hty2' :=
            HasTyT.ascV (hasTy_wk0_val (τ := s2)
              (elab_preserves_val helv' hΓ')) hva2' hgε2'
              (GoodTy.arrow hgs' hgD')
          refine prec_letin1 ?_ hty1 hty1' ?_ hss
          · refine .ascV (tagPrecTy_tagMeetTy hgs hgσw hgs'
                (good_val hw' hΓ') hss hσw hpin1 hpin1' hgε1) ?_ htpw hss
            intro σ0 σ0' hu hu'
            obtain rfl := det_val hu (elab_preserves_val hw hgΓ)
            obtain rfl := det_val hu' (elab_preserves_val helw' hΓ')
            exact tagPrecTy_tagMeetTy hgσw hgs (good_val hw' hΓ') hgs' hσw
              hss hpin1 hpin1' hgε1
          · refine prec_letin1 ?_ hty2 hty2' (.app .var .var)
              (.arrow hss hdd)
            refine .ascV (tagPrecTy_tagMeetTy (.arrow hgs hgDb) hgσv
                (.arrow hgs' hgD') (good_val hv' hΓ') (.arrow hss hdd) hσv
                hpin2 hpin2' hgε2) ?_
              (prec_rename_val htpv (Δ := []) (Δ' := []) rfl rfl rfl) (.arrow hss hdd)
            intro σ0 σ0' hu hu'
            obtain rfl := det_val hu
              (hasTy_wk0_val (elab_preserves_val hv hgΓ))
            obtain rfl := det_val hu'
              (hasTy_wk0_val (elab_preserves_val helv' hΓ'))
            exact tagPrecTy_tagMeetTy hgσv (.arrow hgs hgDb)
              (good_val hv' hΓ') (.arrow hgs' hgD') hσv (.arrow hss hdd)
              hpin2 hpin2' hgε2
  | Γ', _, _, .ite hv' hcb' hm1' hm2' hc', hΓ' => by
      obtain ⟨tv', helv', hcompv'⟩ := elab_canon_val hv' hΓ'
      obtain ⟨tm1', helm1', hcomp1'⟩ := elab_canon_tm hm1' hΓ'
      obtain ⟨tm2', helm2', hcomp2'⟩ := elab_canon_tm hm2' hΓ'
      obtain ⟨ε', hpin', -, -⟩ :=
        hvtag_tagMeetTy (good_val hv' hΓ') .bool (econsTy_of_consTy hcb')
      refine ⟨_, .eite helv' helm1' helm2' hcb' hc' hpin', ?_⟩
      intro Γ m tm D helab hprec hctx hgΓ
      cases hprec with
      | ite hpv hp1 hp2 =>
        cases helab with
        | @eite _ _ _ _ _ _ _ σv _ _ ε hv h1 h2 hcb hcd hpin =>
          have htpv := hcompv' hv hpv hctx hgΓ
          have htp1 := hcomp1' h1 hp1 hctx hgΓ
          have htp2 := hcomp2' h2 hp2 hctx hgΓ
          have hgσv : GoodTy σv := good_val (elab_sound_val hv) hgΓ
          have hgσv' : GoodTy _ := good_val hv' hΓ'
          have hσv : PrecTy σv _ := precTy_elab hv helv' hpv hctx hgΓ hΓ'
          obtain ⟨hva, hgε⟩ := hvtag_of_tagMeetTy hgσv .bool hcb hpin
          obtain ⟨hva', hgε'⟩ := hvtag_of_tagMeetTy hgσv' .bool hcb' hpin'
          have hty : HasTyT Γ (.ascV ε _ .bool) (pointF .bool) :=
            .ascV (elab_preserves_val hv hgΓ) hva hgε .bool
          have hty' : HasTyT Γ' (.ascV ε' _ .bool) (pointF .bool) :=
            .ascV (elab_preserves_val helv' hΓ') hva' hgε' .bool
          refine prec_letin1 ?_ hty hty'
            (.ite .var (prec_rename_tm htp1 (Δ := []) (Δ' := []) rfl rfl rfl)
              (prec_rename_tm htp2 (Δ := []) (Δ' := []) rfl rfl rfl)) .bool
          refine .ascV (tagPrecTy_tagMeetTy .bool hgσv .bool hgσv' .bool
              hσv hpin hpin' hgε) ?_ htpv .bool
          intro σ0 σ0' hu hu'
          obtain rfl := det_val hu (elab_preserves_val hv hgΓ)
          obtain rfl := det_val hu' (elab_preserves_val helv' hΓ')
          exact tagPrecTy_tagMeetTy hgσv .bool hgσv' .bool hσv .bool
            hpin hpin' hgε
  | Γ', _, _, .choice ha0' ha1' hm1' hm2', hΓ' => by
      obtain ⟨tm1', helm1', hcomp1'⟩ := elab_canon_tm hm1' hΓ'
      obtain ⟨tm2', helm2', hcomp2'⟩ := elab_canon_tm hm2' hΓ'
      refine ⟨_, .echoice ha0' ha1' helm1' helm2', ?_⟩
      intro Γ m tm D helab hprec hctx hgΓ
      cases hprec with
      | choice hpp hp1 hp2 =>
        cases hpp with
        | refl =>
          cases helab with
          | @echoice _ _ _ _ _ _ _ _ ha0 ha1 h1 h2 =>
            exact .choice .refl (hcomp1' h1 hp1 hctx hgΓ)
              (hcomp2' h2 hp2 hctx hgΓ)
  | Γ', _, _, .choiceU hm1' hm2', hΓ' => by
      obtain ⟨tm1', helm1', hcomp1'⟩ := elab_canon_tm hm1' hΓ'
      obtain ⟨tm2', helm2', hcomp2'⟩ := elab_canon_tm hm2' hΓ'
      refine ⟨_, .echoiceU helm1' helm2', ?_⟩
      intro Γ m tm D helab hprec hctx hgΓ
      cases hprec with
      | choice hpp hp1 hp2 =>
        cases helab with
        | @echoice _ _ _ _ _ _ _ _ ha0 ha1 h1 h2 =>
          exact .choice .unk (hcomp1' h1 hp1 hctx hgΓ)
            (hcomp2' h2 hp2 hctx hgΓ)
        | @echoiceU _ _ _ _ _ _ _ h1 h2 =>
          exact .choice .refl (hcomp1' h1 hp1 hctx hgΓ)
            (hcomp2' h2 hp2 hctx hgΓ)
  | Γ', _, _, @GPLC.HasTyT.letin _ ms' nb' Dsc' F' hm' hbody', hΓ' => by
      obtain ⟨tms', helm', hcompm'⟩ := elab_canon_tm hm' hΓ'
      have hgD' : GoodD Dsc' := good_tm hm' hΓ'
      have hexb : ∀ j : Fin Dsc'.n,
          ∃ tn', ElabT (Dsc'.ty j :: Γ') nb' tn' (F' j) ∧
            (∀ {Γ : List FTy} {m : GPLC.Tm} {tm : Tm} {D : FDist},
              ElabT Γ m tm D → GPLC.PrecT m nb' →
              PrecCtx Γ (Dsc'.ty j :: Γ') → CtxGood Γ →
              PrecT Γ (Dsc'.ty j :: Γ') tm tn') :=
        fun j => elab_canon_tm (hbody' j) (ctxGood_cons (hgD'.tys j) hΓ')
      choose tns' helb' hcompb' using hexb
      refine ⟨_, .eletin' helm' helb', ?_⟩
      intro Γ m tm D helab hprec hctx hgΓ
      cases hprec with
      | letin hpms hpnb =>
        cases helab with
        | @eletin _ _ tmsP km tym Cm _ tns F hm hbody =>
          have hgDm : GoodD ⟨km, tym, Cm⟩ := good_tm (elab_sound_tm hm) hgΓ
          have htym : HasTyT Γ tmsP ⟨km, tym, Cm⟩ := elab_preserves_tm hm hgΓ
          have htym' : HasTyT Γ' tms' Dsc' := elab_preserves_tm helm' hΓ'
          have hDD' : PrecD ⟨km, tym, Cm⟩ Dsc' :=
            precD_elab hm helm' hpms hctx hgΓ hΓ'
          refine PrecT.letin (hcompm' hm hpms hctx hgΓ) ?_ ?_
          · intro E E' hty hty' i j hij hilen hjlen
            obtain rfl := det_tm hty htym
            obtain rfl := det_tm hty' htym'
            have hb := hcompb' j (hbody i) hpnb
              (precCtx_cons hij hctx) (ctxGood_cons (hgDm.tys i) hgΓ)
            simpa using hb
          · intro E E' hty hty' p hp
            obtain rfl := det_tm hty htym
            obtain rfl := det_tm hty' htym'
            exact hDD'.coup p hp
end

/-! ## The dynamic gradual guarantee for GPLC -/

/-- Theorem 6 (dynamic gradual guarantee for GPLC).  The semantics of a
source term is "elaborate from the typing, then reduce".  For closed source
terms `m ⊑ m′` with `m′` well typed, there is an elaboration `tm′` of `m′`
such that, for every elaboration `tm` of `m`, if `tm` reduces without errors
(`RedEF`) and `tm′` reduces, the resulting configurations are related
(`DConfPrec`).  Composition of `elab_canon_tm` (Lemma 55), `elab_preserves_tm`
(Lemma 11) and `TPLC.dynamic_gradual_guarantee` (Theorem 5). -/
theorem _root_.GradualProb.GPLC.dynamic_gradual_guarantee {m m' : GPLC.Tm} {D' : FDist}
    (hty' : ⊢ m' : D') (hprec : m ⊑ m') :
    ∃ tm', ⊢ m' : D' ⇝ tm' ∧
      ∀ {tm : Tm} {D : FDist}, ⊢ m : D ⇝ tm →
        ∀ {k k' : ℕ} {V V' : DConf}, RedEF tm k V → tm' ⇓[k'] V' →
          V ⊑ V' := by
  obtain ⟨tm', hel', hcomp⟩ := elab_canon_tm hty' ctxGood_nil
  refine ⟨tm', hel', ?_⟩
  intro tm D hel k k' V V' hred hred'
  exact TPLC.dynamic_gradual_guarantee hred hred' (elab_preserves_tm hel ctxGood_nil)
    (elab_preserves_tm hel' ctxGood_nil) (hcomp hel hprec List.Forall₂.nil ctxGood_nil)

end GradualProb.TPLC
