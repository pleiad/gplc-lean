import GradualProb.TPLC.GradualGuaranteeCases

/-!
# The dynamic gradual guarantee for TPLC

This module proves Theorem 5 (dynamic gradual guarantee for TPLC): for
closed well-typed terms `m ⊑ m'`, if `m` reduces by a derivation that raises
no error and `m'` reduces, the two resulting configurations are related by
precision.

## Main results

* `dynamic_gradual_guarantee`: Theorem 5 (dynamic gradual guarantee for
  TPLC).
* `errFree_of_redEF`: an error-free reduction of a closed well-typed term
  produces an error-free configuration.

## Reading guide

`RedEF` expresses the hypothesis "by a reduction that raises no error". The
proof of the theorem is by induction on that reduction, inverting the given
reduction of the less precise term; the cases of rules (Dapp), (D::μ) and
(Dlet) are the lemmas `dgg_app_cond`, `dgg_dascD_cond` and `dgg_dlet_cond`
of `TPLC/GradualGuaranteeCases`.
-/

namespace GradualProb.TPLC

open GradualProb.GPLC

/-- The reduction `Red` restricted to derivations that raise no error: no
step takes the failure case of rule (D::σ) or of rule (D::μ), none is
rule (Derr) or an error-propagation rule, and rule (Dv) applies only to
ascriptions, not to error values. This is the hypothesis "by a reduction
that raises no error" of Theorem 5. It is a separate inductive relation
because `Red` lives in `Prop`, so a predicate on its derivations cannot be
defined by recursion. -/
inductive RedEF : Tm → ℕ → DConf → Prop where
  | dv : ∀ {ε : TagTy} {u : Raw} {σ : FTy},
      RedEF (.val (.asc ε u σ)) 1 (DConf.point (.asc ε u σ))
  | dchoice : ∀ {a m n k1 k2 V1 V2}, 0 ≤ a → a ≤ 1 →
      RedEF m k1 V1 → RedEF n k2 V2 →
      RedEF (.choice (.q a) m n) (k1+k2+1) (DConf.choose a V1 V2)
  | dchoiceU : ∀ {m n k1 k2 V1 V2},
      RedEF m k1 V1 → RedEF n k2 V2 →
      RedEF (.choice .unk m n) (k1+k2+1) (DConf.chooseU V1 V2)
  | dadd : ∀ {ε1 : TagTy} {r1 : ℝ} {ε2 : TagTy} {r2 : ℝ} {ε3 : TagTy},
      emeetTy ε1 ε2 = some ε3 →
      RedEF (.add (.asc ε1 (.real r1) .real) (.asc ε2 (.real r2) .real)) 1
          (DConf.point (.asc ε3 (.real (r1+r2)) .real))
  | dmon : ∀ {m k V}, RedEF m k V → RedEF m (k+1) V
  | dit : ∀ {ε m n k V}, RedEF m k V →
      RedEF (.ite (.asc ε (.bool true) .bool) m n) (k+1) V
  | dif : ∀ {ε m n k V}, RedEF n k V →
      RedEF (.ite (.asc ε (.bool false) .bool) m n) (k+1) V
  | dascOk : ∀ {ε1 : TagTy} {u σ} {ε2 : TagTy} {σ' ε3},
      emeetTy ε1 ε2 = some ε3 → GoodTy ε3.toF →
      RedEF (.ascV ε2 (.asc ε1 u σ) σ') 1 (DConf.point (.asc ε3 u σ'))
  | dapp : ∀ {ε : TagTy} {σ' m σa Dres v} {s : TagTy} {d : TagD} {k1 k2 w V},
      tagDom ε = some s → tagCod ε = some d →
      RedEF (.ascV s v σ') k1 (DConf.point w) →
      RedEF ((Tm.ascT d m Dres).subErr w Dres) k2 V →
      RedEF (.app (.asc ε (.lam σ' m) (.arrow σa Dres)) v) (k1+k2+1) V
  | dlet : ∀ {m n} {ty : Fin n → FTy} {C : (Fin n → ℝ) → Prop} {ns : Fin n → Tm}
      {k1 k2} {V : DConf}
      {wv : Fin (tagReorderD V.confF ⟨n, ty, C⟩).n → Val}
      {Vk : Fin (tagReorderD V.confF ⟨n, ty, C⟩).n → DConf}
      {Fb : Fin (tagReorderD V.confF ⟨n, ty, C⟩).n → FDist},
      RedEF m k1 V → HasTyT [] m ⟨n, ty, C⟩ →
      (∀ c, RedEF (.ascV ((tagReorderD V.confF ⟨n, ty, C⟩).ty c)
        (V.val (reorderDL V.confF ⟨n, ty, C⟩ c)) (ty (reorderDR V.confF ⟨n, ty, C⟩ c))) 1
        (DConf.point (wv c))) →
      (∀ c, HasTyT [ty (reorderDR V.confF ⟨n, ty, C⟩ c)]
        (ns (reorderDR V.confF ⟨n, ty, C⟩ c)) (Fb c)) →
      (∀ c, RedEF ((ns (reorderDR V.confF ⟨n, ty, C⟩ c)).subErr (wv c) (Fb c)) k2 (Vk c)) →
      RedEF (.letin m n ns) (k1+k2+1) (DConf.wsum (tagReorderD V.confF ⟨n, ty, C⟩).toF.C Vk)
  | dascD : ∀ {εd : TagD} {m μ μb k1} {V : DConf}
      {wv : Fin (emeetD (tagReorderD V.confF μ) εd).n → Val}
      (hval : εd.HValidFor μ μb),
      RedEF m k1 V → HasTyT [] m μ →
      (∃ w, (emeetD (tagReorderD V.confF μ) εd).toF.C w) →
      (∀ c, RedEF (.ascV ((emeetD (tagReorderD V.confF μ) εd).ty c)
        (V.val (reorderDL V.confF μ (meetDL (tagReorderD V.confF μ).toF εd.toF c)))
        (μb.ty ⟨_, emeetD_r_lt_of_hvalid hval.2 c⟩)) 1 (DConf.point (wv c))) →
      RedEF (.ascT εd m μb) (k1+1)
        (DConf.wsumPoint (emeetD (tagReorderD V.confF μ) εd).toF.C wv)

/-- Every error-free reduction is a reduction. -/
theorem redEF_to_red : ∀ {m : Tm} {k : ℕ} {V : DConf}, RedEF m k V →
    Red m k V
  | _, _, _, .dv => .dv
  | _, _, _, .dchoice ha0 ha1 h1 h2 =>
      .dchoice ha0 ha1 (redEF_to_red h1) (redEF_to_red h2)
  | _, _, _, .dchoiceU h1 h2 => .dchoiceU (redEF_to_red h1) (redEF_to_red h2)
  | _, _, _, .dadd hm => .dadd hm
  | _, _, _, .dmon h0 => .dmon (redEF_to_red h0)
  | _, _, _, .dit h => .dit (redEF_to_red h)
  | _, _, _, .dif h => .dif (redEF_to_red h)
  | _, _, _, .dascOk hm hg => .dascOk hm hg
  | _, _, _, .dapp hd hc h1 h2 =>
      .dapp hd hc (redEF_to_red h1) (redEF_to_red h2)
  | _, _, _, .dlet hr ht hcell hbty hbred =>
      .dlet (redEF_to_red hr) ht
        (fun c => redEF_to_red (hcell c)) hbty
        (fun c => redEF_to_red (hbred c))
  | _, _, _, .dascD hvR hr ht hsat hcell =>
      .dascD hvR (redEF_to_red hr) ht hsat
        (fun c => redEF_to_red (hcell c))

/-! ## Error-freeness of the result

The introduction lemmas for mixtures need the nonnegativity of the branches'
solutions, which the formulas of well-typed configurations satisfy. -/

/-- If both branches are error-free and their solutions nonnegative, then the
choice `DConf.choose a V1 V2` at a concrete probability is error-free. -/
theorem errFree_choose_intro {a : ℝ} {V1 V2 : DConf}
    (hn1 : ∀ p, V1.C p → ∀ i, 0 ≤ p i) (hn2 : ∀ q, V2.C q → ∀ j, 0 ≤ q j)
    (h1 : ErrFree V1) (h2 : ErrFree V2) : ErrFree (DConf.choose a V1 V2) := by
  rintro x ⟨p, q, hp, hq, rfl⟩ c hpos
  refine Fin.addCases (motive := fun c =>
    0 < Fin.append (fun i => a * p i) (fun j => (1 - a) * q j) c →
      ∃ (ε : TagTy) (u : Raw) (σ : FTy),
        (DConf.choose a V1 V2).val c = .asc ε u σ) ?_ ?_ c hpos
  · intro c1 hc1
    rw [Fin.append_left] at hc1
    have hp1 : 0 < p c1 := (hn1 p hp c1).lt_of_ne fun h => by simp [← h] at hc1
    obtain ⟨ε, u, σ, hv⟩ := h1 p hp c1 hp1
    exact ⟨ε, u, σ, by simpa using hv⟩
  · intro c2 hc2
    rw [Fin.append_right] at hc2
    have hq2 : 0 < q c2 := (hn2 q hq c2).lt_of_ne fun h => by simp [← h] at hc2
    obtain ⟨ε, u, σ, hv⟩ := h2 q hq c2 hq2
    exact ⟨ε, u, σ, by simpa using hv⟩

/-- If both branches are error-free and their solutions nonnegative, then the
choice `DConf.chooseU V1 V2` at an unknown probability is error-free. -/
theorem errFree_chooseU_intro {V1 V2 : DConf}
    (hn1 : ∀ p, V1.C p → ∀ i, 0 ≤ p i) (hn2 : ∀ q, V2.C q → ∀ j, 0 ≤ q j)
    (h1 : ErrFree V1) (h2 : ErrFree V2) : ErrFree (DConf.chooseU V1 V2) := by
  rintro x ⟨a, -, -, p, q, hp, hq, rfl⟩ c hpos
  exact errFree_choose_intro hn1 hn2 h1 h2 _ ⟨p, q, hp, hq, rfl⟩ c hpos

/-- If every summand is error-free and the weights are nonnegative, then the
weighted mixture `DConf.wsum W Vk` is error-free. -/
theorem errFree_wsum_intro {K : ℕ} {W : (Fin K → ℝ) → Prop}
    {Vk : Fin K → DConf} (hnW : ∀ ω, W ω → ∀ k, 0 ≤ ω k)
    (h : ∀ k, ErrFree (Vk k)) : ErrFree (DConf.wsum W Vk) := by
  rintro x ⟨ω, hω, b, hb, hx⟩ c hpos
  rw [hx c] at hpos
  have hωk : 0 < ω (finSigmaFinEquiv.symm c).1 :=
    (hnW ω hω _).lt_of_ne fun h' => by simp [← h'] at hpos
  exact h _ _ (hb _ hωk) _ (pos_of_mul_pos_right hpos hωk.le)

/-- The result of an error-free value ascription is an ascription. -/
theorem redEF_ascV_asc : ∀ {e : TagTy} {v : Val} {σ : FTy} {k : ℕ}
    {V : DConf}, RedEF (.ascV e v σ) k V →
    ∃ (ε : TagTy) (u : Raw) (σ' : FTy), V = DConf.point (.asc ε u σ')
  | _, _, _, _, _, .dascOk _ _ => ⟨_, _, _, rfl⟩
  | _, _, _, _, _, .dmon h0 => redEF_ascV_asc h0

/-- The value produced by an error-free coercion at a single entry is an ascription. -/
theorem redEF_ascV_val_asc {e : TagTy} {v : Val} {σ : FTy} {k : ℕ} {w : Val}
    (h : RedEF (.ascV e v σ) k (DConf.point w)) :
    ∃ (ε : TagTy) (u : Raw) (σ' : FTy), w = .asc ε u σ' := by
  obtain ⟨ε, u, σ', heq⟩ := redEF_ascV_asc h
  exact ⟨ε, u, σ', DConf.point_inj heq⟩

/-- Every error-free reduction of a closed well-typed term produces an
error-free configuration. Nonnegativity of the weights comes from type safety
applied to the underlying reduction, and the typings of the contracta of
rules (Dapp) and (Dlet) from the lemmas of `TPLC/TypeSafety`. -/
theorem errFree_of_redEF : ∀ {m : Tm} {k : ℕ} {V : DConf}, RedEF m k V →
    ∀ {D : FDist}, HasTyT [] m D → ErrFree V
  | _, _, _, .dv, _, _ => errFree_point
  | _, _, _, .dchoice _ _ h1 h2, _, ht => by
      cases ht with
      | choice _ _ ht1 ht2 =>
        exact errFree_choose_intro
          (fun p hp => (type_safety (redEF_to_red h1) ht1).good.good.nonneg p hp)
          (fun q hq => (type_safety (redEF_to_red h2) ht2).good.good.nonneg q hq)
          (errFree_of_redEF h1 ht1) (errFree_of_redEF h2 ht2)
  | _, _, _, .dchoiceU h1 h2, _, ht => by
      cases ht with
      | choiceU ht1 ht2 =>
        exact errFree_chooseU_intro
          (fun p hp => (type_safety (redEF_to_red h1) ht1).good.good.nonneg p hp)
          (fun q hq => (type_safety (redEF_to_red h2) ht2).good.good.nonneg q hq)
          (errFree_of_redEF h1 ht1) (errFree_of_redEF h2 ht2)
  | _, _, _, .dadd _, _, _ => errFree_point
  | _, _, _, .dmon h0, _, ht => errFree_of_redEF h0 ht
  | _, _, _, .dit h, _, ht => by
      cases ht with
      | ite _ ht1 _ => exact errFree_of_redEF h ht1
  | _, _, _, .dif h, _, ht => by
      cases ht with
      | ite _ _ ht2 => exact errFree_of_redEF h ht2
  | _, _, _, .dascOk _ _, _, _ => errFree_point
  | _, _, _, .dapp hdom hcod h1 h2, _, ht => by
      cases ht with
      | app hv hw =>
        exact errFree_of_redEF h2
          (dapp_contractum_typed hv hw hdom hcod (redEF_to_red h1))
  | _, _, _, @RedEF.dlet _ n ty C ns _ _ V _ _ _ hr htμ hcell hbty
      hbred, _, ht => by
      cases ht with
      | @letin _ _ _ ty2 C2 _ F hm hbodyty =>
        injection det_tm htμ hm with _ hty hC
        subst hty hC
        have hgμ := wf_tm hm ctxGood_nil
        have hVvals := (type_safety (redEF_to_red hr) hm).vals
        have hbtyc : ∀ c, HasTyT [] ((ns (reorderDR V.confF ⟨n, ty, C⟩ c)).subErr _ _) _ :=
          fun c => subErr_typed
            (dlet_cell_typed hVvals hgμ (redEF_to_red (hcell c)))
            (hbty c)
            (wf_tm (hbty c) (ctxGood_cons (hgμ.tys _) ctxGood_nil))
        refine errFree_wsum_intro ?_ (fun c => errFree_of_redEF (hbred c) (hbtyc c))
        intro ω hω k
        have hsafe := type_safety (redEF_to_red hr) hm
        have hg : GoodD (tagReorderD V.confF ⟨n, ty, C⟩).toF := by
          rw [tagReorderD_toF]
          exact goodD_reorderD_sat hsafe.good hgμ
            (reorderD_sat_of_refDist hsafe.good.good.sat hsafe.reord)
        exact hg.good.nonneg ω hω k
  | _, _, _, .dascD _ _ _ _ hcell, _, _ => by
      intro p hp c hpos
      exact redEF_ascV_val_asc (hcell c)

/-! ## The dynamic gradual guarantee -/

/-- Theorem 5 (dynamic gradual guarantee for TPLC). For closed well-typed terms
`m ⊑ m'`, if `m` reduces to `V` by a reduction that raises no error (`RedEF`)
and `m'` reduces to `V'`, then `V ⊑ V'` (`DConfPrec`). -/
theorem dynamic_gradual_guarantee : ∀ {m : Tm} {k : ℕ} {V : DConf}, RedEF m k V →
    ∀ {m' : Tm} {k' : ℕ} {V' : DConf} {D D' : FDist}, m' ⇓[k'] V' →
    ⊢ m : D → ⊢ m' : D' → m ⊑ m' → V ⊑ V'
  | _, _, _, .dv, _, _, _, _, _, hr', ht, ht', hp => by
      cases hp with
      | val hv =>
        rw [red_val_inv hr']
        exact dconfprec_point hv
  | _, _, _, .dchoice ha0 ha1 hr1 hr2, _, _, _, _, _, hr', ht, ht',
      hp => by
        cases ht with
        | choice _ _ ht1 ht2 =>
          cases hp with
          | choice hpp hp1 hp2 =>
            rcases red_choice_inv hr' with
              ⟨a', k1', k2', V1', V2', hb0, hb1, hpq, hr1', hr2', rfl⟩ |
              ⟨k1', k2', V1', V2', hpu, hr1', hr2', rfl⟩
            · -- the less precise choice also has a concrete probability
              cases hpp with
              | refl =>
                cases ht' with
                | choice _ _ ht1' ht2' =>
                  obtain rfl : a' = _ := by cases hpq; rfl
                  exact dconfprec_choose_cond ha0 ha1
                    (type_safety (redEF_to_red hr1) ht1).good (type_safety hr1' ht1').good
                    (type_safety (redEF_to_red hr2) ht2).good (type_safety hr2' ht2').good
                    (fun _ => dynamic_gradual_guarantee hr1 hr1' ht1 ht1' hp1)
                    (fun _ => dynamic_gradual_guarantee hr2 hr2' ht2 ht2' hp2)
              | unk => exact nomatch hpq
            · cases ht' with
              | choice _ _ ht1' ht2' => exact nomatch hpu
              | choiceU ht1' ht2' =>
                exact dconfprec_choose_unk_cond ha0 ha1
                  (type_safety (redEF_to_red hr1) ht1).good (type_safety hr1' ht1').good
                  (type_safety (redEF_to_red hr2) ht2).good (type_safety hr2' ht2').good
                  (fun _ => dynamic_gradual_guarantee hr1 hr1' ht1 ht1' hp1)
                  (fun _ => dynamic_gradual_guarantee hr2 hr2' ht2 ht2' hp2)
  | _, _, _, .dchoiceU hr1 hr2, _, _, _, _, _, hr', ht, ht', hp => by
        cases ht with
        | choiceU ht1 ht2 =>
          cases hp with
          | choice hpp hp1 hp2 =>
            rcases red_choice_inv hr' with
              ⟨a', k1', k2', V1', V2', hb0, hb1, hpq, hr1', hr2', rfl⟩ |
              ⟨k1', k2', V1', V2', hpu, hr1', hr2', rfl⟩
            · cases hpp with
              | refl => exact nomatch hpq
              | unk => exact nomatch hpq
            · cases ht' with
              | choice _ _ ht1' ht2' => exact nomatch hpu
              | choiceU ht1' ht2' =>
                exact dconfprec_chooseU
                  (dynamic_gradual_guarantee hr1 hr1' ht1 ht1' hp1)
                  (dynamic_gradual_guarantee hr2 hr2' ht2 ht2' hp2)
  | _, _, _, .dmon h0, _, _, _, _, _, hr', ht, ht', hp =>
      dynamic_gradual_guarantee h0 hr' ht ht' hp
  | _, _, _, .dit hr, _, _, _, _, _, hr', ht, ht', hp => by
        cases ht with
        | ite htv ht1 ht2 =>
          cases hp with
          | ite hpv hp1 hp2 =>
            cases ht' with
            | ite htv' ht1' ht2' =>
              obtain ⟨ε', u', σ', hveq, -, -, hu, -⟩ := tprecV_asc_inv hpv
              subst hveq
              cases hu with
              | bool =>
                rcases red_ite_inv hr' with ⟨ε2, k2', heq, hrb⟩ |
                  ⟨ε2, k2', heq, hrb⟩ | ⟨σ2, D1, D2, heq, -⟩
                · exact dynamic_gradual_guarantee hr hrb ht1 ht1' hp1
                · exact nomatch heq
                · exact nomatch heq
  | _, _, _, .dif hr, _, _, _, _, _, hr', ht, ht', hp => by
        cases ht with
        | ite htv ht1 ht2 =>
          cases hp with
          | ite hpv hp1 hp2 =>
            cases ht' with
            | ite htv' ht1' ht2' =>
              obtain ⟨ε', u', σ', hveq, -, -, hu, -⟩ := tprecV_asc_inv hpv
              subst hveq
              cases hu with
              | bool =>
                rcases red_ite_inv hr' with ⟨ε2, k2', heq, hrb⟩ |
                  ⟨ε2, k2', heq, hrb⟩ | ⟨σ2, D1, D2, heq, -⟩
                · exact nomatch heq
                · exact dynamic_gradual_guarantee hr hrb ht2 ht2' hp2
                · exact nomatch heq
  | _, _, _, .dadd hmeet, _, _, _, _, _, hr', ht, ht', hp => by
      cases ht with
      | add htv htw =>
        cases htv with
        | ascRaw hu1 hev1 hge1 hgσ1 =>
          cases htw with
          | ascRaw hu2 hev2 hge2 hgσ2 =>
            obtain rfl := hvtag_real hev1.right
            obtain rfl := hvtag_real hev2.right
            simp only [emeetTy] at hmeet
            obtain rfl := Option.some.inj hmeet
            cases hp with
            | add hpv hpw =>
              obtain ⟨ε1', u1', σ1', hv'eq, -, -, hpu1, -⟩ := tprecV_asc_inv hpv
              obtain ⟨ε2', u2', σ2', hw'eq, -, -, hpu2, -⟩ := tprecV_asc_inv hpw
              subst hv'eq; subst hw'eq
              cases hpu1 with
              | real =>
                cases hpu2 with
                | real =>
                  cases ht' with
                  | add htv' htw' =>
                    cases htv' with
                    | ascRaw hu1' hev1' hge1' hgσ1' =>
                      cases htw' with
                      | ascRaw hu2' hev2' hge2' hgσ2' =>
                        obtain rfl := hvtag_real hev1'.right
                        obtain rfl := hvtag_real hev2'.right
                        obtain ⟨ε3', hm3', rfl⟩ := red_add_real_inv hr'
                        simp only [emeetTy] at hm3'
                        obtain rfl := Option.some.inj hm3'
                        exact dconfprec_point
                          (PrecV.asc TagPrecTy.real_real
                            (fun _ _ => TagPrecTy.real_real) .real PrecTy.real)
  | _, _, _, .dascOk hmeet hgε3, _, _, _, _, _, hr', ht, ht', hp => by
      cases ht with
      | ascV htv hev2 hge2 hgσ' =>
        cases hp with
        | ascV hpε hpεL hpv hσ =>
          cases ht' with
          | ascV htv' hev2' hge2' hgσ'' =>
            obtain ⟨w'', hstep'', hww'', -⟩ :=
              dgg_cell_ef (tyEntry_of_hasTy htv ▸ htv)
                (tyEntry_of_hasTy htv' ▸ htv')
                hev2.right (tyEntry_of_hasTy htv' ▸ hev2') hge2 hge2'
                hpv hpε hσ (Red.dascOk hmeet hgε3) ⟨_, _, _, rfl⟩
            obtain ⟨w', rfl⟩ := red_ascV_point_inv hr'
            obtain rfl := red_ascV_det (red_ascV_index_one hr') hstep''
            exact dconfprec_point hww''

  | _, _, _, .dapp hdom hcod hargred hbodyred, _, _, _, _, _, hr', ht,
      ht', hp => by
      cases hp with
      | app hpf hpv =>
      obtain ⟨s0, rfl, rfl⟩ := tagDom_arrow hdom hcod
      exact dgg_app_cond (redEF_to_red hargred) (redEF_to_red hbodyred)
          (errFree_of_redEF hbodyred (by
            cases ht with
            | app hv hw =>
              exact dapp_contractum_typed hv hw hdom hcod
                (redEF_to_red hargred)))
          hr' ht ht' hpf hpv
          (fun {n2} {kb} {Vb} {Dm} {Dm'} hrx ht2 ht2' hp2 =>
            dynamic_gradual_guarantee hbodyred hrx ht2 ht2' hp2)
  | _, _, _, .dascD hvR hrm htm hsat hcell, _, _, _, _, _, hr', ht,
      ht', hp => by
      cases hp with
      | ascT hpεR hpεL hpm hγ =>
        cases ht with
        | ascT htm0 hv0 hg0 hgγ0 =>
        cases ht' with
        | ascT htm1 hv1 hg1 hgγ1 =>
          exact dgg_dascD_cond (fun c => emeetD_r_lt_of_hvalid hvR.2 c) (redEF_to_red hrm) htm hsat
            (fun c => redEF_to_red (hcell c)) hr'
            (HasTyT.ascT htm0 hv0 hg0 hgγ0) (HasTyT.ascT htm1 hv1 hg1 hgγ1)
            hpεR (fun hrx => dynamic_gradual_guarantee hrm hrx htm htm1 hpm)
  | _, _, _, .dlet hrm htm hcell hbty hbred, _, _, _, _, _,
      hr', ht, ht', hp => by
      cases hp with
      | @letin _ _ _ m2 _ _ _ ns2 hm hbodies hcoup =>
        cases ht' with
        | @letin _ _ _ ty2 C2 _ F2 htm2 hbty2 =>
          exact dgg_dlet_cond (redEF_to_red hrm) htm
            (fun c => redEF_to_red (hcell c)) hbty
            (fun c => redEF_to_red (hbred c))
            (errFree_of_redEF
              (.dlet hrm htm hcell hbty hbred) ht)
            htm2 hr' (PrecT.letin hm hbodies hcoup)
            (fun {kx} {Vx} hrx => dynamic_gradual_guarantee hrm hrx htm htm2 hm)
            (fun c {n2} {ky} {Vy} {Dx} {Dx'} hrx ht2 ht2' hp2 => by
              obtain ⟨ε0, u0, σ0, hw0⟩ := redEF_ascV_val_asc (hcell c)
              have hb := hbred c
              rw [hw0, Tm.subErr_asc, ← hw0] at hb
              exact dynamic_gradual_guarantee hb hrx ht2 ht2' hp2)

end GradualProb.TPLC
