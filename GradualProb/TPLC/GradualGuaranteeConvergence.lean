import GradualProb.TPLC.GradualGuaranteeCases

/-!
# Convergence half of the dynamic gradual guarantee for TPLC

This module proves a result beyond the article: for every construct except
`let`, if the less precise of two related closed terms converges, the more
precise one converges too (equivalently, divergence of the more precise term
implies divergence of the less precise one). Theorem 5 (dynamic gradual
guarantee for TPLC) relates the results when both terms converge; this module
gives the existence of the precise reduction. It is stated over the full
reduction `Red`, with error propagation: an error in a redex position reduces
to the error at the redex's type, so the more precise term never gets stuck
on an error.

The restriction to reductions without rule (Dlet) is needed: the article's
discussion of Theorem 5 gives a pair of related `let` terms where the less
precise one converges and the more precise one has no reduction.

## Main results

* `dynamic_gradual_guarantee_convergence`: if the less precise term
  converges by a reduction that does not use rule (Dlet) (`RedNL`), the more
  precise term converges.
* `dgg_convergence_substFree`: the same, with no restriction on the derivation,
  for terms without application, `let` and distribution ascription.

## Reading guide

`RedNL` is `Red` without rule (Dlet). `add_total`, `ascV_step` (with
`ascV_total` and `dascD_total` of `TPLC/TypeSafety`) show that the redexes
that consume values always step. `dgg_convergence_app` is the application
case.
-/

namespace GradualProb.TPLC

open GradualProb.GPLC

open Classical

/-! ## Reduction without rule (Dlet) -/

/-- The reduction `Red` without rule (Dlet). A condition on the derivation is
stated as a separate inductive relation, since `Red` lives in `Prop` and
cannot be eliminated into data. -/
inductive RedNL : Tm → ℕ → DConf → Prop where
  | dv : ∀ {v}, RedNL (.val v) 1 (DConf.point v)
  | dchoice : ∀ {a m n k1 k2 V1 V2}, 0 ≤ a → a ≤ 1 →
      RedNL m k1 V1 → RedNL n k2 V2 →
      RedNL (.choice (.q a) m n) (k1+k2+1) (DConf.choose a V1 V2)
  | dchoiceU : ∀ {m n k1 k2 V1 V2},
      RedNL m k1 V1 → RedNL n k2 V2 →
      RedNL (.choice .unk m n) (k1+k2+1) (DConf.chooseU V1 V2)
  | dadd : ∀ {ε1 : TagTy} {r1 : ℝ} {ε2 : TagTy} {r2 : ℝ} {ε3 : TagTy},
      emeetTy ε1 ε2 = some ε3 →
      RedNL (.add (.asc ε1 (.real r1) .real) (.asc ε2 (.real r2) .real)) 1
          (DConf.point (.asc ε3 (.real (r1+r2)) .real))
  | dmon : ∀ {m k V}, RedNL m k V → RedNL m (k+1) V
  | dit : ∀ {ε m n k V}, RedNL m k V →
      RedNL (.ite (.asc ε (.bool true) .bool) m n) (k+1) V
  | dif : ∀ {ε m n k V}, RedNL n k V →
      RedNL (.ite (.asc ε (.bool false) .bool) m n) (k+1) V
  | derr : ∀ {μ : FDist}, RedNL (.errD μ) 1 (DConf.errAt μ)
  | dascOk : ∀ {ε1 : TagTy} {u σ} {ε2 : TagTy} {σ' ε3},
      emeetTy ε1 ε2 = some ε3 → GoodTy ε3.toF →
      RedNL (.ascV ε2 (.asc ε1 u σ) σ') 1 (DConf.point (.asc ε3 u σ'))
  | dascErr : ∀ {ε1 : TagTy} {u σ} {ε2 : TagTy} {σ'},
      ¬ (∃ ε3, emeetTy ε1 ε2 = some ε3 ∧ GoodTy ε3.toF) →
      RedNL (.ascV ε2 (.asc ε1 u σ) σ') 1 (DConf.point (.err σ'))
  | dapp : ∀ {ε : TagTy} {σ' m σa Dres v} {s : TagTy} {d : TagD} {k1 k2 w V},
      tagDom ε = some s → tagCod ε = some d →
      RedNL (.ascV s v σ') k1 (DConf.point w) →
      RedNL ((Tm.ascT d m Dres).subErr w Dres) k2 V →
      RedNL (.app (.asc ε (.lam σ' m) (.arrow σa Dres)) v) (k1+k2+1) V
  | dascD : ∀ {εd : TagD} {m μ μb k1} {V : DConf}
      {wv : Fin (emeetD (tagReorderD V.confF μ) εd).n → Val}
      (hval : εd.HValidFor μ μb),
      RedNL m k1 V → HasTyT [] m μ →
      (∃ w, (emeetD (tagReorderD V.confF μ) εd).toF.C w) →
      (∀ c, RedNL (.ascV ((emeetD (tagReorderD V.confF μ) εd).ty c)
        (V.val (reorderDL V.confF μ (meetDL (tagReorderD V.confF μ).toF εd.toF c)))
        (μb.ty ⟨_, emeetD_r_lt_of_hvalid hval.2 c⟩)) 1 (DConf.point (wv c))) →
      RedNL (.ascT εd m μb) (k1+1)
        (DConf.wsumPoint (emeetD (tagReorderD V.confF μ) εd).toF.C wv)
  | dascDErr : ∀ {εd : TagD} {m μ μb k1} {V : DConf},
      εd.HValidFor μ μb →
      RedNL m k1 V → HasTyT [] m μ →
      ¬ (∃ w, (emeetD (tagReorderD V.confF μ) εd).toF.C w) →
      RedNL (.ascT εd m μb) (k1+1) (DConf.errAt μb)
  | eAscV : ∀ {ε : TagTy} {σ σ'},
      RedNL (.ascV ε (.err σ) σ') 1 (DConf.point (.err σ'))
  | eAddL : ∀ {σ w}, RedNL (.add (.err σ) w) 1 (DConf.point (.err .real))
  | eAddR : ∀ {v σ}, RedNL (.add v (.err σ)) 1 (DConf.point (.err .real))
  | eApp : ∀ {σa} {D : FDist} {w},
      RedNL (.app (.err (.arrow σa D)) w) 1 (DConf.errAt D)
  | eIte : ∀ {σ m n} {D1 D2 : FDist},
      HasTyT [] m D1 → HasTyT [] n D2 →
      RedNL (.ite (.err σ) m n) 1 (DConf.errAt (chooseSemU D1 D2))

/-- Every reduction without rule (Dlet) is a reduction. -/
theorem redNL_to_red : ∀ {m : Tm} {k : ℕ} {V : DConf}, RedNL m k V → Red m k V
  | _, _, _, .dv => .dv
  | _, _, _, .dchoice ha0 ha1 h1 h2 =>
      .dchoice ha0 ha1 (redNL_to_red h1) (redNL_to_red h2)
  | _, _, _, .dchoiceU h1 h2 => .dchoiceU (redNL_to_red h1) (redNL_to_red h2)
  | _, _, _, .dadd hm => .dadd hm
  | _, _, _, .dmon h0 => .dmon (redNL_to_red h0)
  | _, _, _, .dit h => .dit (redNL_to_red h)
  | _, _, _, .dif h => .dif (redNL_to_red h)
  | _, _, _, .derr => .derr
  | _, _, _, .dascOk hm hg => .dascOk hm hg
  | _, _, _, .dascErr hd => .dascErr hd
  | _, _, _, .dapp hd hc h1 h2 =>
      .dapp hd hc (redNL_to_red h1) (redNL_to_red h2)
  | _, _, _, .dascD hvR hr ht hsat hcell =>
      .dascD hvR (redNL_to_red hr) ht hsat
        (fun c => redNL_to_red (hcell c))
  | _, _, _, .dascDErr hvR hr ht hns => .dascDErr hvR (redNL_to_red hr) ht hns
  | _, _, _, .eAscV => .eAscV
  | _, _, _, .eAddL => .eAddL
  | _, _, _, .eAddR => .eAddR
  | _, _, _, .eApp => .eApp
  | _, _, _, .eIte h1 h2 => .eIte h1 h2

/-! ## Shapes of closed values and totality of the value redexes -/


/-- Totality of addition: a closed well-typed addition always steps, by rule
(D+) on two literals (whose evidences are `TagTy.real`, so their composition is
defined) or by error propagation if an operand is an error. -/
theorem add_total {v w : Val} {D : FDist}
    (h : HasTyT [] (.add v w) D) : ∃ (k : ℕ) (V : DConf), Red (.add v w) k V := by
  cases h with
  | add hv hw =>
    rcases closed_real_val_shape hv with ⟨r1, rfl⟩ | ⟨σe, rfl⟩
    · rcases closed_real_val_shape hw with ⟨r2, rfl⟩ | ⟨σe, rfl⟩
      · exact ⟨1, _, Red.dadd rfl⟩
      · exact ⟨1, _, Red.eAddR⟩
    · exact ⟨1, _, Red.eAddL⟩

/-- Totality of value ascription: every closed well-typed value ascription steps. -/
theorem ascV_step {ε : TagTy} {v : Val} {σ' : FTy} {D : FDist}
    (ht : HasTyT [] (.ascV ε v σ') D) :
    ∃ (k : ℕ) (V : DConf), Red (.ascV ε v σ') k V := by
  cases ht with
  | ascV hv _ _ _ =>
    have hv0 : HasTyV [] v v.tyEntry := by rw [tyEntry_of_hasTy hv]; exact hv
    obtain ⟨w, hw⟩ := ascV_total hv0 _ _
    exact ⟨1, _, hw⟩

/-! ## The application case -/

/-- The application case of `dynamic_gradual_guarantee_convergence`. The more
precise side always steps: if its function is an error, the error
propagates; if it is an ascribed λ, the coercion of the argument is total
(`ascV_total`), its result is related to the less precise one (`dgg_cell_cond`),
and the substituted bodies are related by `prec_subst0`, so the induction
hypothesis on the body applies. If the precise coercion fails, `subErr` makes
the body an error, which reduces in one step. -/
theorem dgg_convergence_app {ε' : TagTy} {σf' : FTy} {mb' : Tm} {σa' : FTy}
    {Dres' : FDist} {w' : Val} {s' : TagTy} {d' : TagD} {k1' k2' : ℕ}
    {wc' : Val} {V' : DConf}
    (hd' : tagDom ε' = some s') (hc' : tagCod ε' = some d')
    (hargred' : Red (.ascV s' w' σf') k1' (DConf.point wc'))
    (hbodyred' : Red ((Tm.ascT d' mb' Dres').subErr wc' Dres') k2' V')
    {v w : Val} {D D' : FDist}
    (hty : HasTyT [] (.app v w) D)
    (hty' : HasTyT [] (.app (.asc ε' (.lam σf' mb') (.arrow σa' Dres')) w') D')
    (hpv : PrecV [] [] v (.asc ε' (.lam σf' mb') (.arrow σa' Dres')))
    (hpw : PrecV [] [] w w')
    (hIHb : ∀ {n : Tm} {Dx Dx' : FDist},
      HasTyT [] n Dx →
      HasTyT [] ((Tm.ascT d' mb' Dres').subErr wc' Dres') Dx' →
      PrecT [] [] n ((Tm.ascT d' mb' Dres').subErr wc' Dres') →
      ∃ (k : ℕ) (V : DConf), Red n k V) :
    ∃ (k : ℕ) (V : DConf), Red (.app v w) k V := by
  -- inversion of the less precise side
  cases hty' with
  | app hfn' hw' =>
  cases hfn' with
  | ascRaw hlam' hev' hgε' hgarr' =>
  cases hlam' with
  | lam hm'ty hgσf' =>
  obtain ⟨hevL', hevR'⟩ := hev'
  cases hevL' with
  | arrow hLs' hLd' =>
  cases hevR' with
  | arrow hRs' hRd' =>
  cases hgε' with
  | arrow hgs' hgd' =>
  cases hgarr' with
  | arrow hgσa' hgDres' =>
  obtain rfl : s' = _ := by
    simp only [tagDom, Option.some.injEq] at hd'; exact hd'.symm
  obtain rfl : d' = _ := by
    simp only [tagCod, Option.some.injEq] at hc'; exact hc'.symm
  obtain rfl : w'.tyEntry = σa' := tyEntry_of_hasTy hw'
  -- the more precise side
  cases hpv with
  | errV hty0 hσ0 =>
      -- the precise function is an error: it propagates
      cases hty with
      | app hv hw =>
        cases hv with
        | err hg => exact ⟨1, _, Red.eApp⟩
  | asc hε hεL hu hσ =>
      cases hu with
      | @lam _ _ σf _ mb _ hpσf hpm =>
      cases hty with
      | app hv hw =>
      cases hv with
      | ascRaw hlam hev hgε hgarr =>
      cases hlam with
      | lam hmty hgσf =>
      obtain ⟨hevL, hevR⟩ := hev
      cases hevL with
      | arrow hLs hLd =>
      cases hevR with
      | arrow hRs hRd =>
      cases hgε with
      | arrow hgs hgd =>
      cases hgarr with
      | arrow hgσa hgD =>
      cases hσ with
      | arrow hpσa hpDres =>
      obtain rfl : w.tyEntry = _ := tyEntry_of_hasTy hw
      -- the precise coercion of the argument always steps
      obtain ⟨wc, hstep⟩ := ascV_total hw _ σf
      have hargred1' := red_ascV_index_one hargred'
      have hflipR := TagPrecTy.flip (hεL (.lam hmty hgσf) (.lam hm'ty hgσf')).arrow_inv.1
      have hww' : PrecV [] [] wc wc' :=
        dgg_cell_cond hw hw' (hvtag_flip hLs)
          ⟨hvtag_flip hRs', hvtag_flip hLs'⟩
          (by rw [TagTy.flip_toF]; exact hgs)
          (by rw [TagTy.flip_toF]; exact hgs') hgσf' hpw hflipR hpσf
          hstep hargred1'
      have hwcty : HasTyV [] wc σf :=
        cell_coercion_typed hw ⟨hvtag_flip hRs, hvtag_flip hLs⟩
          (by rw [TagTy.flip_toF]; exact hgs) hgσf hstep
      have hwc'ty : HasTyV [] wc' σf' :=
        cell_coercion_typed hw' ⟨hvtag_flip hRs', hvtag_flip hLs'⟩
          (by rw [TagTy.flip_toF]; exact hgs') hgσf' hargred1'
      cases wc with
      | var x => cases hwcty with | var hx => simp at hx
      | err σe =>
          -- the precise coercion failed: the body is the error at the result type
          exact ⟨_, _, Red.dapp rfl rfl hstep (by
            rw [Tm.subErr_err]; exact Red.derr)⟩
      | asc εw uw σw =>
          obtain ⟨εw2, uw2, σw2, rfl, -, -, -, -⟩ := tprecV_asc_inv hww'
          rw [Tm.subErr_asc] at hbodyred'
          obtain ⟨kb, Vb, hbred⟩ :=
            hIHb (hasTy_subst0_tm hwcty (.ascT hmty ⟨hLd, hRd⟩ hgd hgD))
              (hasTy_subst0_tm hwc'ty (.ascT hm'ty ⟨hLd', hRd'⟩ hgd' hgDres'))
              (by
                simp only [Tm.subErr_asc, Tm.subst0, Tm.subst]
                refine PrecT.ascT ?_ ?_ ?_ hpDres
                · intro D1 D2x ht1 ht2
                  exact hε.arrow_inv.2
                · intro D1 D2x ht1 ht2
                  obtain rfl := hasTy_closed_det_tm
                    (hasTy_subst0_tm hwcty hmty) ht1
                  obtain rfl := hasTy_closed_det_tm
                    (hasTy_subst0_tm hwc'ty hm'ty) ht2
                  exact (hεL (.lam hmty hgσf) (.lam hm'ty hgσf')).arrow_inv.2
                · exact prec_subst0 hpm hww' hwcty hwc'ty)
          exact ⟨_, _, Red.dapp rfl rfl hstep hbred⟩

/-! ## Convergence for every construct except `let` -/

/-- Convergence half of the dynamic gradual guarantee for TPLC (beyond the
article; every construct except `let`): if the less precise term converges by a
reduction that does not use rule (Dlet), the more precise term converges.

By induction on the less precise reduction, inverting term precision on the
precise side. Ascriptions (`ascV_total`, `dascD_total`) and additions
(`add_total`) step by totality; a `?` probability on the less precise side is
matched by the precise probability; errors in redex position propagate; and
application goes through `dgg_convergence_app`. -/
theorem dynamic_gradual_guarantee_convergence : ∀ {m' : Tm} {k' : ℕ} {V' : DConf}, RedNL m' k' V' →
    ∀ {m : Tm} {D D' : FDist},
      HasTyT [] m D → HasTyT [] m' D' → PrecT [] [] m m' →
      ∃ (k : ℕ) (V : DConf), Red m k V := by
  intro m' k' V' hr
  induction hr with
  | dv =>
      intro m D D' _ _ hp
      cases hp with
      | val _ => exact ⟨1, _, Red.dv⟩
  | dchoice ha0 ha1 _ _ ih1 ih2 =>
      intro m D D' ht ht' hp
      cases hp with
      | choice hgp hp1 hp2 =>
        cases hgp with
        | refl =>
            cases ht with
            | choice hb0 hb1 ht1 ht2 =>
              cases ht' with
              | choice _ _ ht1' ht2' =>
                obtain ⟨k1, V1, hr1⟩ := ih1 ht1 ht1' hp1
                obtain ⟨k2, V2, hr2⟩ := ih2 ht2 ht2' hp2
                exact ⟨_, _, Red.dchoice hb0 hb1 hr1 hr2⟩
  | dchoiceU _ _ ih1 ih2 =>
      intro m D D' ht ht' hp
      cases hp with
      | choice hgp hp1 hp2 =>
        cases ht' with
        | choiceU ht1' ht2' =>
          cases ht with
          | choice hb0 hb1 ht1 ht2 =>
            obtain ⟨k1, V1, hr1⟩ := ih1 ht1 ht1' hp1
            obtain ⟨k2, V2, hr2⟩ := ih2 ht2 ht2' hp2
            exact ⟨_, _, Red.dchoice hb0 hb1 hr1 hr2⟩
          | choiceU ht1 ht2 =>
            obtain ⟨k1, V1, hr1⟩ := ih1 ht1 ht1' hp1
            obtain ⟨k2, V2, hr2⟩ := ih2 ht2 ht2' hp2
            exact ⟨_, _, Red.dchoiceU hr1 hr2⟩
  | dadd _ =>
      intro m D D' ht _ hp
      cases hp with
      | add _ _ => exact add_total ht
  | dmon _ ih => intro m D D' ht ht' hp; exact ih ht ht' hp
  | dit _ ih =>
      intro m D D' ht ht' hp
      cases hp with
      | ite hgv hp1 hp2 =>
        cases ht with
        | ite hvty ht1 ht2 =>
          cases hgv with
          | asc _ _ hu _ =>
              cases hu with
              | bool =>
                obtain rfl : _ = FTy.bool := tyEntry_of_hasTy hvty
                cases ht' with
                | ite _ ht1' _ =>
                  obtain ⟨k1, V1, hr1⟩ := ih ht1 ht1' hp1
                  exact ⟨_, _, Red.dit hr1⟩
          | errV _ _ => exact ⟨1, _, Red.eIte ht1 ht2⟩
  | dif _ ih =>
      intro m D D' ht ht' hp
      cases hp with
      | ite hgv hp1 hp2 =>
        cases ht with
        | ite hvty ht1 ht2 =>
          cases hgv with
          | asc _ _ hu _ =>
              cases hu with
              | bool =>
                obtain rfl : _ = FTy.bool := tyEntry_of_hasTy hvty
                cases ht' with
                | ite _ _ ht2' =>
                  obtain ⟨k2, V2, hr2⟩ := ih ht2 ht2' hp2
                  exact ⟨_, _, Red.dif hr2⟩
          | errV _ _ => exact ⟨1, _, Red.eIte ht1 ht2⟩
  | derr =>
      intro m D D' _ _ hp
      cases hp with
      | errD _ => exact ⟨1, _, Red.derr⟩
  | dascOk _ _ =>
      intro m D D' ht _ hp
      cases hp with
      | ascV _ _ _ _ =>
        exact ascV_step ht
  | dascErr _ =>
      intro m D D' ht _ hp
      cases hp with
      | ascV _ _ _ _ =>
        exact ascV_step ht
  | eAscV =>
      intro m D D' ht _ hp
      cases hp with
      | ascV _ _ _ _ =>
        exact ascV_step ht
  | eAddL => intro m D D' ht _ hp; cases hp with | add _ _ => exact add_total ht
  | eAddR => intro m D D' ht _ hp; cases hp with | add _ _ => exact add_total ht
  | eApp =>
      intro m D D' ht _ hp
      cases hp with
      | app hpv _ =>
        cases hpv with
        | errV _ _ =>
          cases ht with
          | app hv _ => cases hv with | err _ => exact ⟨1, _, Red.eApp⟩
  | eIte h1 h2 =>
      intro m D D' ht _ hp
      cases hp with
      | ite hgv _ _ =>
        cases ht with
        | ite hvty ht1 ht2 =>
          cases hgv with
          | errV _ _ => exact ⟨1, _, Red.eIte ht1 ht2⟩
  | dapp hd' hc' hargred' hbodyred' _ ihb =>
      intro m D D' ht ht' hp
      cases hp with
      | app hpv hpw =>
        exact dgg_convergence_app hd' hc' (redNL_to_red hargred') (redNL_to_red hbodyred')
          ht ht' hpv hpw (fun h1 h2 h3 => ihb h1 h2 h3)
  | dascD hvR _ htm hsat _ ihscr _ =>
      intro m D D' ht ht' hp
      cases hp with
      | ascT _ _ hpm _ =>
        cases ht with
        | ascT htm0 hval hgε hgμb =>
          cases ht' with
          | ascT htm0' _ _ _ =>
            obtain ⟨k1, V1, hred1⟩ := ihscr htm0 htm0' hpm
            exact dascD_total hred1 (.ascT htm0 hval hgε hgμb)
  | dascDErr _ _ htm hns ihscr =>
      intro m D D' ht ht' hp
      cases hp with
      | ascT _ _ hpm _ =>
        cases ht with
        | ascT htm0 hval hgε hgμb =>
          cases ht' with
          | ascT htm0' _ _ _ =>
            obtain ⟨k1, V1, hred1⟩ := ihscr htm0 htm0' hpm
            exact dascD_total hred1 (.ascT htm0 hval hgε hgμb)

/-! ## The fragment without substitution

On terms that never substitute a value nor route a distribution, the
restriction to `RedNL` is vacuous: no reduction of such a term uses rule
(Dlet), because the contracta are subterms. -/

/-- Terms without application, `let` and distribution ascription (errors
included). -/
inductive SubstFree : Tm → Prop where
  | val    : ∀ {v}, SubstFree (.val v)
  | choice : ∀ {p m n}, SubstFree m → SubstFree n → SubstFree (.choice p m n)
  | ite    : ∀ {v m n}, SubstFree m → SubstFree n → SubstFree (.ite v m n)
  | add    : ∀ {v w}, SubstFree (.add v w)
  | ascV   : ∀ {ε : TagTy} {v σ'}, SubstFree (.ascV ε v σ')
  | errD   : ∀ {γ}, SubstFree (.errD γ)

/-- A reduction of a term of the fragment does not use rule (Dlet). -/
theorem redNL_of_substFree : ∀ {m : Tm} {k : ℕ} {V : DConf}, Red m k V →
    SubstFree m → RedNL m k V
  | _, _, _, .dv, _ => .dv
  | _, _, _, .dchoice ha0 ha1 h1 h2, .choice f1 f2 =>
      .dchoice ha0 ha1 (redNL_of_substFree h1 f1) (redNL_of_substFree h2 f2)
  | _, _, _, .dchoiceU h1 h2, .choice f1 f2 =>
      .dchoiceU (redNL_of_substFree h1 f1) (redNL_of_substFree h2 f2)
  | _, _, _, .dadd hm, _ => .dadd hm
  | _, _, _, .dmon h0, f => .dmon (redNL_of_substFree h0 f)
  | _, _, _, .dit h, .ite f1 _ => .dit (redNL_of_substFree h f1)
  | _, _, _, .dif h, .ite _ f2 => .dif (redNL_of_substFree h f2)
  | _, _, _, .derr, _ => .derr
  | _, _, _, .dascOk hm hg, _ => .dascOk hm hg
  | _, _, _, .dascErr hd, _ => .dascErr hd
  | _, _, _, .eAscV, _ => .eAscV
  | _, _, _, .eAddL, _ => .eAddL
  | _, _, _, .eAddR, _ => .eAddR
  | _, _, _, .eIte h1 h2, _ => .eIte h1 h2

/-- Convergence for the fragment without substitution, with no restriction on
the less precise derivation: if the less precise term converges, so does the
more precise one. -/
theorem dgg_convergence_substFree {m m' : Tm} {k' : ℕ} {V' : DConf} {D D' : FDist}
    (hr' : Red m' k' V') (hf' : SubstFree m')
    (ht : HasTyT [] m D) (ht' : HasTyT [] m' D') (hp : PrecT [] [] m m') :
    ∃ (k : ℕ) (V : DConf), Red m k V :=
  dynamic_gradual_guarantee_convergence (redNL_of_substFree hr' hf') ht ht' hp


end GradualProb.TPLC
