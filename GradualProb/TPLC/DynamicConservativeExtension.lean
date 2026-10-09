import GradualProb.GPLC.ConservativeExtension
import GradualProb.SPLC.Semantics
import GradualProb.SPLC.TypeSafety
import GradualProb.TPLC.Normalization

/-!
# Dynamic conservative extension

This module proves Theorem 7 (dynamic conservative extension of TPLC with
respect to SPLC) by erasure, following Section C.7 of the appendix. The erasure
of Figure 19 (`ErVal`, `ErTm`) sends a TPLC value back to the SPLC value it came
from, and the two measures it compares are `erMass` (target) and `srcMass`
(source). The module also formalizes weak realization (Definition 15), the
realizing-types judgment (Definition 16) and the normalization of source terms
(`anfV`, `anfT`), and proves Lemmas 56 to 38 and Theorem 8.

## Main results

* `red_ascV_static_ok`: Lemma 57 (static composition defined).
* `ascV_rawOf`, `erVal_of_raw_eq`, `erVal_ascV`: Lemma 58 (coercion invariance).
* `elab_erVal`, `elab_erTm`: Lemma 60 (elaboration erases to the normalized
  source).
* `red_anf`: Lemma 65 (normalization preserves the measure).
* `srT_of_elab`, `srT_closed`: Lemma 61 (static realization).
* `redSt_of_red`, with `red_ascV_below_ok`, `not_dascErr_below`,
  `econsD_below`, `routing_sat_below`: Lemma 62 (no failure).
* `meetD_left_marginal`, `reorderD_left_marginal`, `routing_left_marginal`:
  Lemma 66 (routing preserves marginals).
* `erasure_cover_red`, `erasure_cover`: Lemma 67 (coverage).
* `red_srcMass_det`: Lemma 64 (source determinism modulo measure).
* `erasure_meas_red`, `erasure_meas`: Theorem 8 (erasure preserves measure).
* `dynamic_conservative_extension`, `dynamic_conservative_extension_obs`:
  Theorem 7 (dynamic conservative extension), items 1 and 2.

## Reading guide

Weak realization and Lemma 57 come first, then renaming identities for TPLC
terms, the raw value under a coercion and the marginals of the routing
(Lemma 66). Next come the erasure and
its invariance under coercion (Lemma 58), the two measures, and `RedSt`, the
reduction `Red` without the two rules that raise an error at a coercion, over
which coverage (`erasure_cover`) and the measure equation (`erasure_meas`) are
proved. The normalization `anfT` links the elaboration to the source (Lemmas 60, 64
and 65). The last part lifts the restriction to `RedSt`: the judgment `SRT`
(Definition 16), its inhabitation by elaborated static programs (Lemma 61) and
Lemma 62, from which Theorem 7 follows.
-/


namespace GradualProb.TPLC

open GradualProb.SPLC GradualProb.GPLC
open scoped BigOperators
open GradualProb.CouplingLemma


/-! ## Weak realization (Definition 15) and static composition (Lemma 57)

The evidences that reach a composition during the run of an elaborated static
program lie below an annotation that realizes a static type, and a type below a
realizing one may carry entries of probability zero with no partner. Such
evidences satisfy weak realization (Definition 15), which differs from
realization (Definition 7, `RealizesD`) in two ways at distribution types. It
drops the two coverage clauses. And it moves `=ₛ` from the support clause into
the relation: `RealizesD` relates `i` and `j` when entry `i` realizes the static
entry `j` itself, and its last premise lifts the relation that holds of `(i, j)`
when some related pair `(i, j')` has `j'` and `j` of `=ₛ` types, while
`WeakRealizesD` relates `i` and `j` when entry `i` weakly realizes some type
`=ₛ` to entry `j`, and its last premise is the lifting (`Lift`, Definition 2)
of that relation between each solution and the static probabilities. Weak
realization descends along precision (`weakRealizesTy_of_prec`),
and two weak realizations of `=ₛ`-related static types are consistent
(`econs_of_weakRealizes_ty`), which gives Lemma 57. -/

mutual
/-- Definition 15 (weak realization), simple types. -/
inductive WeakRealizesTy : FTy → Ty → Prop where
  | real : WeakRealizesTy .real .real
  | bool : WeakRealizesTy .bool .bool
  | arrow : ∀ {s τ d T}, WeakRealizesTy s τ → WeakRealizesD d T →
      WeakRealizesTy (.arrow s d) (.arrow τ T)
/-- Definition 15 (weak realization), distribution types: the formula is
satisfiable, and every solution is related to the static probabilities by the
lifting (`Lift`, Definition 2) of a relation `R` whose pairs `(i, j)` have
entry `i` weakly realizing a type `t i j` that is `=ₛ` to the static entry `j`.
No coverage clauses. The article's existential over that type is the witness
function `t`: an existential nested in the rule would hide the sub-derivation
from the structural recursion of `econs_of_weakRealizes_d`. -/
inductive WeakRealizesD : FDist → DTy → Prop where
  | dist : ∀ {D : FDist} {es : List (Ty × GProb)}
      (R : Fin D.n → Fin es.length → Prop)
      (t : Fin D.n → Fin es.length → Ty),
      (∀ i j, R i j → WeakRealizesTy (D.ty i) (t i j)) →
      (∀ i j, R i j → EqTy (t i j) (es.get j).1) →
      (∃ p, D.C p) →
      (∀ p, D.C p → Lift R p (fun j => pval (es.get j).2)) →
      WeakRealizesD D (.dist es)
end

/-- `σ ⇝ʷ τ`, the formula simple type `σ` weakly realizes the static type `τ`
(Definition 15). -/
scoped infix:50 (name := weakRealizesTyStx) " ⇝ʷ " => WeakRealizesTy
/-- `D ⇝ʷ T`, the formula distribution type `D` weakly realizes the static type
`T` (Definition 15). -/
scoped infix:50 (name := weakRealizesDStx) " ⇝ʷ " => WeakRealizesD

mutual
/-- Lemma 56 (weak realization), item 1, simple types: if `σ` realizes `τ`, then
`σ` weakly realizes `τ`. -/
theorem weakRealizesTy_of_realizes : ∀ {σ : FTy} {τ : Ty}, σ ⇝ τ → σ ⇝ʷ τ
  | _, _, .real => .real
  | _, _, .bool => .bool
  | _, _, .arrow hs hd => .arrow (weakRealizesTy_of_realizes hs) (weakRealizesD_of_realizes hd)
/-- Lemma 56 (weak realization), item 1, distribution types: if `D` realizes
`T`, then `D` weakly realizes `T`. -/
theorem weakRealizesD_of_realizes : ∀ {D : FDist} {T : DTy}, D ⇝ T → D ⇝ʷ T
  | _, _, @RealizesD.dist D es R hR _ _ hsat hc => by
      classical
      refine .dist
        (fun i j => ∃ j', R i j' ∧ EqTy (es.get j').1 (es.get j).1)
        (fun i j => if h : ∃ j', R i j' ∧ EqTy (es.get j').1 (es.get j).1
          then (es.get h.choose).1 else .real) ?_ ?_ hsat hc
      · intro i j hij
        simp only [dif_pos hij]
        exact weakRealizesTy_of_realizes (hR i hij.choose hij.choose_spec.1)
      · intro i j hij
        simp only [dif_pos hij]
        exact hij.choose_spec.2
end

mutual
/-- Lemma 56 (weak realization), item 2, simple types: if `X` is well-formed,
`X ⊑̇ A` and `A` weakly realizes `τ`, then `X` weakly realizes `τ`. -/
theorem weakRealizesTy_of_prec : ∀ {X A : FTy} {τ : Ty}, GoodTy X → X ⊑̇ A →
    A ⇝ʷ τ → X ⇝ʷ τ
  | _, _, _, _, .real, h => h
  | _, _, _, _, .bool, h => h
  | _, _, _, _, .unk, h => nomatch h
  | _, _, _, hg, .arrow hps hpd, h => by
      cases h with
      | arrow hs hd =>
        cases hg with
        | arrow hgs hgd =>
          exact .arrow (weakRealizesTy_of_prec hgs hps hs)
            (weakRealizesD_of_prec hgd hpd hd)
/-- Lemma 56 (weak realization), item 2, distribution types: if `X` is
well-formed, `X ⊑̇ A` and `A` weakly realizes `T`, then `X` weakly realizes `T`. -/
theorem weakRealizesD_of_prec : ∀ {X A : FDist} {T : DTy}, GoodD X → X ⊑̇ A →
    A ⇝ʷ T → X ⇝ʷ T
  | _, _, _, hg, .mk RP hRP hcp, h => by
      classical
      cases h with
      | dist RA tA hRA hCA hsatA hcA =>
        refine .dist (fun i j => ∃ mid, RP i mid ∧ RA mid j)
          (fun i j => if hm : ∃ mid, RP i mid ∧ RA mid j
            then tA hm.choose j else .real) ?_ ?_ hg.good.sat ?_
        · intro i j hij
          simp only [dif_pos hij]
          exact weakRealizesTy_of_prec (hg.tys i)
            (hRP i hij.choose hij.choose_spec.1)
            (hRA hij.choose j hij.choose_spec.2)
        · intro i j hij
          simp only [dif_pos hij]
          exact hCA hij.choose j hij.choose_spec.2
        · intro p hp
          obtain ⟨q, hq, hl⟩ := hcp p hp
          exact hl.trans (hcA q hq) fun _ mid _ h1 h2 => ⟨mid, h1, h2⟩
end

mutual
/-- Lemma 57 (static composition defined), item 1, consistency: if `τ1 =ₛ τ2`,
`σ1` weakly realizes `τ1` and `σ2` weakly realizes `τ2`, then `σ1` and `σ2` are
consistent (`EConsTy`). -/
theorem econs_of_weakRealizes_ty : ∀ {σ1 σ2 : FTy} {τ1 τ2 : Ty},
    σ1 ⇝ʷ τ1 → τ1 =ₛ τ2 → σ2 ⇝ʷ τ2 → σ1 ∼̇ σ2
  | _, _, _, _, .real, hc, h2 => by
      cases hc
      cases h2
      exact .real
  | _, _, _, _, .bool, hc, h2 => by
      cases hc
      cases h2
      exact .bool
  | _, _, _, _, .arrow hs1 hd1, hc, h2 => by
      cases hc with
      | arrow hcs hcd =>
        cases h2 with
        | arrow hs2 hd2 =>
          exact .arrow (econs_of_weakRealizes_ty hs1 hcs hs2)
            (econs_of_weakRealizes_d hd1 hcd hd2)
/-- Lemma 57 (static composition defined), item 2: if `T1 =ₛ T2`, `D1` weakly
realizes `T1` and `D2` weakly realizes `T2`, then `D1` and `D2` are consistent
(`EConsD`). -/
theorem econs_of_weakRealizes_d : ∀ {D1 D2 : FDist} {T1 T2 : DTy},
    D1 ⇝ʷ T1 → T1 =ₛ T2 → D2 ⇝ʷ T2 → D1 ∼̇ D2
  | _, _, _, _, .dist R1 t1 hR1 hC1 hsat1 hc1, hc, h2 => by
      cases h2 with
      | dist R2 t2 hR2 hC2 hsat2 hc2 =>
        obtain ⟨p, hp⟩ := hsat1
        obtain ⟨q, hq⟩ := hsat2
        cases hc with
        | dist Rc fLc fRc hRc hlc hcfL hcfR =>
          have hl : Lift (fun i1 i2 => ∃ j1 j2, R1 i1 j1 ∧ Rc j1 j2 ∧ R2 i2 j2) p q :=
            ((hc1 p hp).comp hlc).trans (hc2 q hq).symm
              fun _ _ _ ⟨j1, h1, hj⟩ h2 => ⟨j1, _, h1, hj, h2⟩
          refine EConsD.mk _ ?_ ⟨p, q, hp, hq, hl⟩
          rintro i1 i2 ⟨j1, j2, hRp1, hj1j2, hRp2⟩
          exact econs_of_weakRealizes_ty (hR1 i1 j1 hRp1)
            (EqTy.trans ((hC1 i1 j1 hRp1))
              (EqTy.trans (hRc j1 j2 hj1j2)
                (EqTy.symm ((hC2 i2 j2 hRp2)))))
            (hR2 i2 j2 hRp2)
end


/-- Weak realization transports to a defined meet: the meet is more precise
than its left operand (Lemma 8), and weak realization descends along
precision. -/
theorem weakRealizes_emeetTy {e1 e2 e3 : TagTy} {τ : Ty}
    (hg1 : GoodTy e1.toF) (hg2 : GoodTy e2.toF) (hc : EConsTy e1.toF e2.toF)
    (hm : emeetTy e1 e2 = some e3) (h1 : WeakRealizesTy e1.toF τ) :
    WeakRealizesTy e3.toF τ :=
  weakRealizesTy_of_prec (goodTy_emeetTy_some hg1 hg2 hc hm)
    (eprec_meetTy .l hg1 hg2 (emeetTy_toF_some hm)) h1


/-- Lemma 57 (static composition defined), item 1: two good evidences that weakly
realize `=ₛ`-related static types compose. The value ascription fires its
success case, and the composed evidence is good and weakly realizes the first
static type. -/
theorem red_ascV_static_ok {ε1 ε2 : TagTy} {u : Raw} {σ σ' : FTy}
    {τ1 τ2 : Ty}
    (hg1 : GoodTy ε1.toF) (hg2 : GoodTy ε2.toF)
    (h1 : ε1.toF ⇝ʷ τ1) (h2 : ε2.toF ⇝ʷ τ2) (hceq : τ1 =ₛ τ2) :
    ∃ ε3, ε1 ∘ ε2 = some ε3 ∧
      .ascV ε2 (.asc ε1 u σ) σ' ⇓[1] DConf.point (.asc ε3 u σ') ∧
      ε3.toF ⇝ʷ τ1 ∧ GoodTy ε3.toF := by
  have hc : EConsTy ε1.toF ε2.toF := econs_of_weakRealizes_ty h1 hceq h2
  obtain ⟨ε3, hm⟩ := cons_emeetTy_isSome hc
  exact ⟨ε3, hm, Red.dascOk hm (goodTy_emeetTy_some hg1 hg2 hc hm),
    weakRealizes_emeetTy hg1 hg2 hc hm h1, goodTy_emeetTy_some hg1 hg2 hc hm⟩


/-! ## Renaming and substitution identities for TPLC terms

`subst_rename_cancel`: substituting at the index of a weakening cancels it
(`(t.rename c).subst c w = t`). `rename_subst`: for a closed substituend,
substitution commutes with a weakening below it. -/

mutual
/-- Substituting at the index of a weakening cancels it (raw values). -/
theorem Raw.subst_rename_cancel : ∀ (u : Raw) (c : ℕ) (w : Val),
    (u.rename c).subst c w = u
  | .real r, _, _ => by simp [Raw.rename, Raw.subst]
  | .bool b, _, _ => by simp [Raw.rename, Raw.subst]
  | .lam σ m, c, w => by
      simp only [Raw.rename, Raw.subst]
      rw [Tm.subst_rename_cancel m (c + 1) (w.rename 0)]
/-- Substituting at the index of a weakening cancels it (values). -/
theorem Val.subst_rename_cancel : ∀ (v : Val) (c : ℕ) (w : Val),
    (v.rename c).subst c w = v
  | .var x, c, w => by
      by_cases hx : x < c
      · simp only [Val.rename, if_pos hx, Val.subst,
          if_neg (by omega : ¬ x = c), if_neg (by omega : ¬ x > c)]
      · simp only [Val.rename, if_neg hx, Val.subst,
          if_neg (by omega : ¬ x + 1 = c), if_pos (by omega : x + 1 > c),
          Nat.add_sub_cancel]
  | .asc ε u σ, c, w => by
      simp only [Val.rename, Val.subst]
      rw [Raw.subst_rename_cancel u c w]
  | .err σ, _, _ => by simp [Val.rename, Val.subst]
/-- Substituting at the index of a weakening cancels it (terms). -/
theorem Tm.subst_rename_cancel : ∀ (m : Tm) (c : ℕ) (w : Val),
    (m.rename c).subst c w = m
  | .val v, c, w => by
      simp only [Tm.rename, Tm.subst]
      rw [Val.subst_rename_cancel v c w]
  | .app v u, c, w => by
      simp only [Tm.rename, Tm.subst]
      rw [Val.subst_rename_cancel v c w, Val.subst_rename_cancel u c w]
  | .letin m _ ns, c, w => by
      rw [Tm.rename_letin, Tm.subst_letin, Tm.subst_rename_cancel m c w]
      congr 1; funext i
      exact Tm.subst_rename_cancel (ns i) (c + 1) (w.rename 0)
  | .choice p m n, c, w => by
      simp only [Tm.rename, Tm.subst]
      rw [Tm.subst_rename_cancel m c w, Tm.subst_rename_cancel n c w]
  | .ascT ε m D, c, w => by
      simp only [Tm.rename, Tm.subst]
      rw [Tm.subst_rename_cancel m c w]
  | .ascV ε v σ, c, w => by
      simp only [Tm.rename, Tm.subst]
      rw [Val.subst_rename_cancel v c w]
  | .ite v m n, c, w => by
      simp only [Tm.rename, Tm.subst]
      rw [Val.subst_rename_cancel v c w, Tm.subst_rename_cancel m c w,
        Tm.subst_rename_cancel n c w]
  | .add v u, c, w => by
      simp only [Tm.rename, Tm.subst]
      rw [Val.subst_rename_cancel v c w, Val.subst_rename_cancel u c w]
  | .errD D, _, _ => by simp [Tm.rename, Tm.subst]
end

mutual
/-- Weaken, then substitute above: for a closed substituend, substituting at
`k + 1` after weakening at `c ≤ k` equals substituting at `k` before
weakening. -/
theorem Raw.rename_subst : ∀ (u : Raw) (c k : ℕ), c ≤ k → ∀ {w : Val},
    w.FvBelow 0 → (u.rename c).subst (k + 1) w = (u.subst k w).rename c
  | .real r, _, _, _, _, _ => by simp [Raw.rename, Raw.subst]
  | .bool b, _, _, _, _, _ => by simp [Raw.rename, Raw.subst]
  | .lam σ m, c, k, hck, w, hw => by
      simp only [Raw.rename, Raw.subst]
      rw [Val.rename_below hw (Nat.zero_le 0)]
      rw [Tm.rename_subst m (c + 1) (k + 1) (by omega) hw]
/-- For `c ≤ k` and a closed `w`, weakening at `c` commutes with substituting
`w` at `k` (values). -/
theorem Val.rename_subst : ∀ (v : Val) (c k : ℕ), c ≤ k → ∀ {w : Val},
    w.FvBelow 0 → (v.rename c).subst (k + 1) w = (v.subst k w).rename c
  | .var x, c, k, hck, w, hw => by
      by_cases hx : x < c
      · simp only [Val.rename, if_pos hx, Val.subst,
          if_neg (by omega : ¬ x = k + 1), if_neg (by omega : ¬ x > k + 1),
          if_neg (by omega : ¬ x = k), if_neg (by omega : ¬ x > k)]
      · by_cases hxk : x = k
        · simp only [Val.rename, if_neg hx, Val.subst,
            if_pos (by omega : x + 1 = k + 1), if_pos hxk]
          rw [Val.rename_below hw (Nat.zero_le c)]
        · by_cases hx2 : x > k
          · simp only [Val.rename, if_neg hx, Val.subst,
              if_neg (by omega : ¬ x + 1 = k + 1),
              if_pos (by omega : x + 1 > k + 1), if_neg hxk, if_pos hx2,
              Nat.add_sub_cancel, if_neg (by omega : ¬ x - 1 < c)]
            congr 1
            omega
          · simp only [Val.rename, if_neg hx, Val.subst,
              if_neg (by omega : ¬ x + 1 = k + 1),
              if_neg (by omega : ¬ x + 1 > k + 1), if_neg hxk, if_neg hx2,
              if_neg (by omega : ¬ x < c)]
  | .asc ε u σ, c, k, hck, w, hw => by
      simp only [Val.rename, Val.subst]
      rw [Raw.rename_subst u c k hck hw]
  | .err σ, _, _, _, _, _ => by simp [Val.rename, Val.subst]
/-- For `c ≤ k` and a closed `w`, weakening at `c` commutes with substituting
`w` at `k` (terms). -/
theorem Tm.rename_subst : ∀ (m : Tm) (c k : ℕ), c ≤ k → ∀ {w : Val},
    w.FvBelow 0 → (m.rename c).subst (k + 1) w = (m.subst k w).rename c
  | .val v, c, k, hck, w, hw => by
      simp only [Tm.rename, Tm.subst]
      rw [Val.rename_subst v c k hck hw]
  | .app v u, c, k, hck, w, hw => by
      simp only [Tm.rename, Tm.subst]
      rw [Val.rename_subst v c k hck hw, Val.rename_subst u c k hck hw]
  | .letin m _ ns, c, k, hck, w, hw => by
      simp only [Tm.rename_letin, Tm.subst_letin]
      rw [Tm.rename_subst m c k hck hw, Val.rename_below hw (Nat.zero_le 0)]
      congr 1; funext i
      exact Tm.rename_subst (ns i) (c + 1) (k + 1) (by omega) hw
  | .choice p m n, c, k, hck, w, hw => by
      simp only [Tm.rename, Tm.subst]
      rw [Tm.rename_subst m c k hck hw, Tm.rename_subst n c k hck hw]
  | .ascT ε m D, c, k, hck, w, hw => by
      simp only [Tm.rename, Tm.subst]
      rw [Tm.rename_subst m c k hck hw]
  | .ascV ε v σ, c, k, hck, w, hw => by
      simp only [Tm.rename, Tm.subst]
      rw [Val.rename_subst v c k hck hw]
  | .ite v m n, c, k, hck, w, hw => by
      simp only [Tm.rename, Tm.subst]
      rw [Val.rename_subst v c k hck hw, Tm.rename_subst m c k hck hw,
        Tm.rename_subst n c k hck hw]
  | .add v u, c, k, hck, w, hw => by
      simp only [Tm.rename, Tm.subst]
      rw [Val.rename_subst v c k hck hw, Val.rename_subst u c k hck hw]
  | .errD D, _, _, _, _, _ => by simp [Tm.rename, Tm.subst]
end


attribute [local instance] Classical.propDecidable


/-! ## Coercion keeps the raw value

Rule (D::σ) rewrites `⟨ε₁ u⟩::σ` into `⟨ε₃ u⟩::σ′`: it changes the evidence
and the annotation, never the raw value `u`. Only the error case loses it. -/

/-- The raw value under an ascription, if any. -/
def Val.rawOf : Val → Option Raw
  | .asc _ u _ => some u
  | .err _ => none
  | .var _ => none

/-- The coercion of a value keeps its raw value, or errs. A variable has no
raw value, so equality of `rawOf` alone does not exclude it; the coercion does,
since it is undefined on variables. -/
theorem Val.coerce_rawOf {ε : TagTy} {v : Val} {σ' : FTy} {w : Val}
    (h : v.coerce ε σ' = some w) :
    (∃ u, w.rawOf = some u ∧ v.rawOf = some u) ∨ w = .err σ' := by
  cases v with
  | var x => exact nomatch h
  | err σ => cases h; exact .inr rfl
  | asc ε1 u σ =>
    rcases Val.coerce_asc_inv h with ⟨ε3, -, -, rfl⟩ | ⟨-, rfl⟩
    · exact .inl ⟨u, rfl, rfl⟩
    · exact .inr rfl

/-- Lemma 58 (coercion invariance), reduction step: a value ascription reduces
to a Dirac on a value with the raw value of the original, or on an error. -/
theorem ascV_rawOf {ε : TagTy} {v : Val} {σ' : FTy} {k} {V : DConf}
    (h : .ascV ε v σ' ⇓[k] V) :
    ∃ w, V = DConf.point w ∧ (w.rawOf = v.rawOf ∨ w = .err σ') := by
  obtain ⟨w, hw, rfl⟩ := red_ascV_coerce h
  refine ⟨w, rfl, ?_⟩
  rcases Val.coerce_rawOf hw with ⟨u, h1, h2⟩ | h
  · exact .inl (h1.trans h2.symm)
  · exact .inr h

/-! ## Routing preserves marginals (Lemma 66)

The routing evidence of rule (Dlet) is the initial reordering `tagReorderD`; that
of rule (D::μ) is its meet with the ascription evidence. The formulas of
`reorderD` and `meetD` state their marginal equations literally: the push-forward
(`pushfwd`) of every solution along its left projection is a solution of the
left operand. `pushfwd_comp` composes the two push-forwards. -/

/-- Lemma 66 (routing preserves marginals), meet: every solution of
`meetD D1 D2` aggregates along its left projection to a solution of `D1`. The
formula of `meetD` states it literally. -/
theorem meetD_left_marginal (D1 D2 : FDist) {ω : Fin (D1 ⊓ D2).n → ℝ}
    (hω : (D1 ⊓ D2).C ω) :
    ∃ pp, D1.C pp ∧ ∀ i, (∑ c, if meetDL D1 D2 c = i then ω c else 0) = pp i :=
  ⟨_, ((meetD_C_iff D1 D2 ω).1 hω).1, fun _ => rfl⟩

/-- Lemma 66 (routing preserves marginals), initial reordering: the same for
`reorderD D1 D2`, the routing of rule (Dlet). -/
theorem reorderD_left_marginal (D1 D2 : FDist) {ω : Fin (D1 ∥ D2).n → ℝ}
    (hω : (D1 ∥ D2).C ω) :
    ∃ pp, D1.C pp ∧ ∀ i, (∑ c, if reorderDL D1 D2 c = i then ω c else 0) = pp i :=
  ⟨_, ((reorderD_C_iff D1 D2 ω).1 hω).1, fun _ => rfl⟩

/-- Lemma 66 (routing preserves marginals), rule (D::μ): the routing evidence
`emeetD (tagReorderD D1 D2) ξ` has formula `meetD (reorderD D1 D2) ξ.toF`
(`routing_toF`) and left projection `reorderDL ∘ meetDL`, so the
probability the entries of the routing evidence draw from each outcome `i` of `D1` adds up to the
probability of `i` in a solution of `D1`, by `pushfwd_comp`. -/
theorem routing_left_marginal (D1 D2 : FDist) (ξ : TagD)
    {ω : Fin ((D1 ∥ D2) ⊓ ξ.toF).n → ℝ}
    (hω : ((D1 ∥ D2) ⊓ ξ.toF).C ω) :
    ∃ q, D1.C q ∧ ∀ i : Fin D1.n,
      (∑ c, if reorderDL D1 D2 (meetDL (D1 ∥ D2) ξ.toF c) = i
            then ω c else 0) = q i := by
  obtain ⟨pp, hpp, h1⟩ := meetD_left_marginal (reorderD D1 D2) ξ.toF hω
  obtain ⟨q, hq, h2⟩ := reorderD_left_marginal D1 D2 hpp
  obtain rfl : pushfwd (meetDL (reorderD D1 D2) ξ.toF) ω = pp := funext h1
  exact ⟨q, hq, fun i => (congrFun (pushfwd_comp _ _ ω) i).symm.trans (h2 i)⟩


/-! ## The measure of an SPLC distribution value -/

/-- The measure `V(w)` of Figure 19: the total probability the SPLC distribution
value `V` gives to the value `w`, that is, the weight (`massOf`) of the
predicate `· = w`. -/
noncomputable def srcMass (V : DistVal) (w : SPLC.Val) : ℝ :=
  massOf (· = w) V.val V.mass

/-- The measure of a Dirac distribution value `point v` at `w`: `1` if `v = w`,
`0` otherwise. -/
@[simp] theorem srcMass_point (v w : SPLC.Val) :
    srcMass (DistVal.point v) w = if v = w then 1 else 0 :=
  massOf_fin_one _ _ _


/-! ## The erasure (Figure 19)

The erasure forgets everything a coercion can change: evidences, annotations
and target types appear in the shapes of its clauses and in no premise. Its
invariance under coercion (Lemma 58) follows directly. Source annotations cannot
be recovered from the target, the lifting of types not being injective, so the
source side carries a placeholder in their place; `anfV`/`anfT` rewrite a source
term into that form. -/

mutual
/-- Erasure of TPLC values (Figure 19), as a relation: `ErVal tv v` says that
`v` is the erasure of `tv`. Evidences and annotations are free in every clause,
and an error value has no erasure. The placeholder (the article's `_`) that
replaces a discarded annotation is `.unk` at simple types (binders of `λ`, value
ascriptions) and `.dist []` at distribution types (term ascriptions). -/
inductive ErVal : Val → SPLC.Val → Prop where
  /-- A variable erases to itself. -/
  | evar  : ∀ {x}, ErVal (.var x) (.var x)
  /-- A real literal, under any evidence and annotation. -/
  | ereal : ∀ {ε σ r}, ErVal (.asc ε (.real r) σ) (.real r)
  /-- A boolean literal, under any evidence and annotation. -/
  | ebool : ∀ {ε σ b}, ErVal (.asc ε (.bool b) σ) (.bool b)
  /-- A `λ`: its body erases to the source body, and the binder's annotation
  becomes the placeholder. -/
  | elam  : ∀ {ε σ σ0 tm m}, ErTm tm m →
              ErVal (.asc ε (.lam σ0 tm) σ) (.lam .unk m)
/-- Erasure of TPLC terms (Figure 19), as a relation `ErTm tm m`. -/
inductive ErTm : Tm → SPLC.Tm → Prop where
  | eval    : ∀ {tv v}, ErVal tv v → ErTm (.val tv) (.val v)
  | eapp    : ∀ {tv v tw w}, ErVal tv v → ErVal tw w →
                ErTm (.app tv tw) (.app v w)
  | eadd    : ∀ {tv v tw w}, ErVal tv v → ErVal tw w →
                ErTm (.add tv tw) (.add v w)
  | eite    : ∀ {tv v tm m tn n}, ErVal tv v → ErTm tm m → ErTm tn n →
                ErTm (.ite tv tm tn) (.ite v m n)
  /-- A choice with a concrete probability in `[0,1]` (the grammar's
  condition); a choice with probability `?` has no erasure. -/
  | echoice : ∀ {p tm m tn n}, 0 ≤ p → p ≤ 1 → ErTm tm m → ErTm tn n →
                ErTm (.choice (.q p) tm tn) (.choice p m n)
  /-- The exhaustive `let`: the family of bodies is non-empty and every body
  erases to the same source body, the side condition of Figure 19. -/
  | eletin  : ∀ {tm m k} {tns : Fin k → Tm} {n}, 0 < k → ErTm tm m →
                (∀ i, ErTm (tns i) n) → ErTm (.letin tm k tns) (.letin m n)
  | eascV   : ∀ {ε σ tv v}, ErVal tv v → ErTm (.ascV ε tv σ) (.ascV v .unk)
  | eascT   : ∀ {ε D tm m}, ErTm tm m → ErTm (.ascT ε tm D) (.ascT m (.dist []))
end

/-! ### The erasure is functional

Without functionality the measure equation would fail: a target value erasing
to two source values would give probability to both. -/

mutual
/-- The erasure of values is functional. -/
theorem erVal_det : ∀ {tv : Val} {v v' : SPLC.Val}, ErVal tv v → ErVal tv v' → v = v'
  | _, _, _, .evar, .evar => rfl
  | _, _, _, .ereal, .ereal => rfl
  | _, _, _, .ebool, .ebool => rfl
  | _, _, _, .elam h, .elam h' => by rw [erTm_det h h']
/-- The erasure of terms is functional. -/
theorem erTm_det : ∀ {tm : Tm} {m m' : SPLC.Tm}, ErTm tm m → ErTm tm m' → m = m'
  | _, _, _, .eval h, .eval h' => by rw [erVal_det h h']
  | _, _, _, .eapp h1 h2, .eapp h1' h2' => by
      rw [erVal_det h1 h1', erVal_det h2 h2']
  | _, _, _, .eadd h1 h2, .eadd h1' h2' => by
      rw [erVal_det h1 h1', erVal_det h2 h2']
  | _, _, _, .eite h1 h2 h3, .eite h1' h2' h3' => by
      rw [erVal_det h1 h1', erTm_det h2 h2', erTm_det h3 h3']
  | _, _, _, .echoice _ _ h1 h2, .echoice _ _ h1' h2' => by
      rw [erTm_det h1 h1', erTm_det h2 h2']
  | _, _, _, .eletin hpos h1 h2, .eletin _ h1' h2' => by
      rw [erTm_det h1 h1', erTm_det (h2 ⟨0, hpos⟩) (h2' ⟨0, hpos⟩)]
  | _, _, _, .eascV h, .eascV h' => by rw [erVal_det h h']
  | _, _, _, .eascT h, .eascT h' => by rw [erTm_det h h']
end

/-! ### The erasure reads only the raw value -/

/-- Lemma 58 (coercion invariance): two values with the same raw value have the
same erasure. -/
theorem erVal_of_raw_eq {tv tw : Val} {v : SPLC.Val} {u : Raw}
    (h : ErVal tv v) (h1 : tv.rawOf = some u) (h2 : tw.rawOf = some u) :
    ErVal tw v := by
  cases tw with
  | var x => simp [Val.rawOf] at h2
  | err σ => simp [Val.rawOf] at h2
  | asc ε' u' σ' =>
    simp only [Val.rawOf] at h2
    obtain rfl : u' = u := Option.some.inj h2
    cases h with
    | evar => simp [Val.rawOf] at h1
    | ereal =>
      simp only [Val.rawOf] at h1
      obtain rfl := Option.some.inj h1
      exact .ereal
    | ebool =>
      simp only [Val.rawOf] at h1
      obtain rfl := Option.some.inj h1
      exact .ebool
    | elam hb =>
      simp only [Val.rawOf] at h1
      obtain rfl := Option.some.inj h1
      exact .elam hb

/-- `ascV_rawOf` with the raw value exhibited in the success case
(`Val.coerce_rawOf`). -/
theorem ascV_rawOf_some {ε : TagTy} {v : Val} {σ' : FTy} {k} {V : DConf}
    (h : Red (.ascV ε v σ') k V) :
    ∃ w, V = DConf.point w ∧
      ((∃ u, w.rawOf = some u ∧ v.rawOf = some u) ∨ w = .err σ') := by
  obtain ⟨w, hw, rfl⟩ := red_ascV_coerce h
  exact ⟨w, rfl, Val.coerce_rawOf hw⟩

/-- Lemma 58 (coercion invariance): a value ascription that does not fail
yields a value with the erasure of the original. -/
theorem erVal_ascV {ε : TagTy} {tv : Val} {σ' : FTy} {k} {w : Val}
    (h : .ascV ε tv σ' ⇓[k] DConf.point w)
    (hne : w ≠ .err σ') {v : SPLC.Val} (hEr : ErVal tv v) : ErVal w v := by
  obtain ⟨w', hpt, hcase⟩ := ascV_rawOf_some h
  obtain rfl : w' = w := (DConf.point_inj hpt).symm
  rcases hcase with ⟨u, hwu, hvu⟩ | hbad
  · exact erVal_of_raw_eq hEr hvu hwu
  · exact absurd hbad hne

/-! ### Renaming and substitution

The `app` and `let` cases of the inductions substitute under binders, so the
lemmas are stated at an arbitrary index. -/

mutual
/-- Erasure commutes with renaming (values). -/
theorem erVal_rename : ∀ {tv : Val} {v : SPLC.Val}, ErVal tv v →
    ∀ c, ErVal (tv.rename c) (v.rename c)
  | _, _, .evar (x := x), c => by
      by_cases h : x < c
      · simp only [Val.rename, SPLC.Val.rename, if_pos h]; exact .evar
      · simp only [Val.rename, SPLC.Val.rename, if_neg h]; exact .evar
  | _, _, .ereal, _ => by simp only [Val.rename, SPLC.Val.rename, Raw.rename]; exact .ereal
  | _, _, .ebool, _ => by simp only [Val.rename, SPLC.Val.rename, Raw.rename]; exact .ebool
  | _, _, .elam hb, c => by
      simp only [Val.rename, SPLC.Val.rename, Raw.rename]
      exact .elam (erTm_rename hb (c + 1))
/-- Erasure commutes with renaming (terms). -/
theorem erTm_rename : ∀ {tm : Tm} {m : SPLC.Tm}, ErTm tm m →
    ∀ c, ErTm (tm.rename c) (m.rename c)
  | _, _, .eval hv, c => by
      simp only [Tm.rename, SPLC.Tm.rename]; exact .eval (erVal_rename hv c)
  | _, _, .eapp h1 h2, c => by
      simp only [Tm.rename, SPLC.Tm.rename]
      exact .eapp (erVal_rename h1 c) (erVal_rename h2 c)
  | _, _, .eadd h1 h2, c => by
      simp only [Tm.rename, SPLC.Tm.rename]
      exact .eadd (erVal_rename h1 c) (erVal_rename h2 c)
  | _, _, .eite h1 h2 h3, c => by
      simp only [Tm.rename, SPLC.Tm.rename]
      exact .eite (erVal_rename h1 c) (erTm_rename h2 c) (erTm_rename h3 c)
  | _, _, .echoice hp0 hp1 h1 h2, c => by
      simp only [Tm.rename, SPLC.Tm.rename]
      exact .echoice hp0 hp1 (erTm_rename h1 c) (erTm_rename h2 c)
  | _, _, .eletin hpos h1 h2, c => by
      rw [Tm.rename_letin]
      simp only [SPLC.Tm.rename]
      exact .eletin hpos (erTm_rename h1 c) (fun i => erTm_rename (h2 i) (c + 1))
  | _, _, .eascV hv, c => by
      simp only [Tm.rename, SPLC.Tm.rename]; exact .eascV (erVal_rename hv c)
  | _, _, .eascT hm, c => by
      simp only [Tm.rename, SPLC.Tm.rename]; exact .eascT (erTm_rename hm c)
end

mutual
/-- Lemma 59 (erasure and substitution), values: if `tv` erases to `v` and `tsub`
erases to `wsub`, then `tv.subst k tsub` erases to `v.subst k wsub`. -/
theorem erVal_subst : ∀ {tv : Val} {v : SPLC.Val}, ErVal tv v →
    ∀ {tsub : Val} {wsub : SPLC.Val}, ErVal tsub wsub →
      ∀ k, ErVal (tv.subst k tsub) (v.subst k wsub)
  | _, _, .evar (x := x), _, _, hsub, k => by
      by_cases h1 : x = k
      · simp only [Val.subst, SPLC.Val.subst, if_pos h1]; exact hsub
      · by_cases h2 : x > k
        · simp only [Val.subst, SPLC.Val.subst, if_neg h1, if_pos h2]; exact .evar
        · simp only [Val.subst, SPLC.Val.subst, if_neg h1, if_neg h2]; exact .evar
  | _, _, .ereal, _, _, _, _ => by
      simp only [Val.subst, SPLC.Val.subst, Raw.subst]; exact .ereal
  | _, _, .ebool, _, _, _, _ => by
      simp only [Val.subst, SPLC.Val.subst, Raw.subst]; exact .ebool
  | _, _, .elam hb, _, _, hsub, k => by
      simp only [Val.subst, SPLC.Val.subst, Raw.subst]
      exact .elam (erTm_subst hb (erVal_rename hsub 0) (k + 1))
/-- Lemma 59 (erasure and substitution), terms: if `tm` erases to `m` and `tsub`
erases to `wsub`, then `tm.subst k tsub` erases to `m.subst k wsub`. -/
theorem erTm_subst : ∀ {tm : Tm} {m : SPLC.Tm}, ErTm tm m →
    ∀ {tsub : Val} {wsub : SPLC.Val}, ErVal tsub wsub →
      ∀ k, ErTm (tm.subst k tsub) (m.subst k wsub)
  | _, _, .eval hv, _, _, hsub, k => by
      simp only [Tm.subst, SPLC.Tm.subst]
      exact .eval (erVal_subst hv hsub k)
  | _, _, .eapp h1 h2, _, _, hsub, k => by
      simp only [Tm.subst, SPLC.Tm.subst]
      exact .eapp (erVal_subst h1 hsub k) (erVal_subst h2 hsub k)
  | _, _, .eadd h1 h2, _, _, hsub, k => by
      simp only [Tm.subst, SPLC.Tm.subst]
      exact .eadd (erVal_subst h1 hsub k) (erVal_subst h2 hsub k)
  | _, _, .eite h1 h2 h3, _, _, hsub, k => by
      simp only [Tm.subst, SPLC.Tm.subst]
      exact .eite (erVal_subst h1 hsub k) (erTm_subst h2 hsub k)
        (erTm_subst h3 hsub k)
  | _, _, .echoice hp0 hp1 h1 h2, _, _, hsub, k => by
      simp only [Tm.subst, SPLC.Tm.subst]
      exact .echoice hp0 hp1 (erTm_subst h1 hsub k) (erTm_subst h2 hsub k)
  | _, _, .eletin hpos h1 h2, _, _, hsub, k => by
      rw [Tm.subst_letin]
      simp only [SPLC.Tm.subst]
      exact .eletin hpos (erTm_subst h1 hsub k)
        (fun i => erTm_subst (h2 i) (erVal_rename hsub 0) (k + 1))
  | _, _, .eascV hv, _, _, hsub, k => by
      simp only [Tm.subst, SPLC.Tm.subst]
      exact .eascV (erVal_subst hv hsub k)
  | _, _, .eascT hm, _, _, hsub, k => by
      simp only [Tm.subst, SPLC.Tm.subst]
      exact .eascT (erTm_subst hm hsub k)
end

/-- Substitution at the outermost binder. -/
theorem erTm_subst0 {tm : Tm} {m : SPLC.Tm} (h : ErTm tm m) {tw : Val} {w : SPLC.Val}
    (hw : ErVal tw w) : ErTm (tm.subst0 tw) (m.subst0 w) :=
  erTm_subst h hw 0


/-! ## The two measures

The erasure compares a TPLC configuration (symbolic probabilities closed by a
formula) with an SPLC distribution value (concrete probabilities). For a
solution `q` of the configuration's formula, the target gives an SPLC value `w`
the total probability of its outcomes that erase to `w`. -/

/-- The probability that the configuration `V`, under the solution `q` of its
formula, gives to the values satisfying `P`: the weight (`massOf`) of `P`. -/
noncomputable def pMass (P : Val → Prop) (V : DConf) (q : Fin V.n → ℝ) : ℝ :=
  massOf P V.val q

/-- The erased measure of Figure 19: the probability of the outcomes of `V` that
erase to `w`, under the solution `q`. -/
noncomputable def erMass (V : DConf) (q : Fin V.n → ℝ) (w : SPLC.Val) : ℝ :=
  pMass (fun tv => ErVal tv w) V q

/-! ### `pMass` on the result shapes of `Red`

Dirac, binary choice and weighted sum, by `massOf_fin_one`, `massOf_append` and
`massOf_sigmaFin`, and the push-forward along a routing, by `massOf_pushfwd`. -/

/-- `pMass` of a Dirac configuration `point v`: `1` if `v` satisfies `P`, `0`
otherwise. -/
theorem pMass_point (P : Val → Prop) (v : Val) (q : Fin (DConf.point v).n → ℝ)
    (hq : (DConf.point v).C q) : pMass P (DConf.point v) q = if P v then 1 else 0 := by
  rw [pMass, massOf_fin_one, show q 0 = 1 from hq]

/-- `pMass` of a binary choice `choose a V1 V2` at the solution built from
solutions `p` and `q` of the branches is the `a`-weighted sum of the branches'. -/
theorem pMass_choose (P : Val → Prop) (a : ℝ) (V1 V2 : DConf)
    (p : Fin V1.n → ℝ) (q : Fin V2.n → ℝ) :
    pMass P (DConf.choose a V1 V2) (Fin.append (fun i => a * p i) (fun j => (1 - a) * q j))
      = a * pMass P V1 p + (1 - a) * pMass P V2 q := by
  show massOf P (Fin.append V1.val V2.val) _ = _
  rw [massOf_append, massOf_mul_left, massOf_mul_left]
  rfl

/-- `pMass` of a weighted sum `wsum W V` at the solution built from weights `ω`
and solutions `b k` of the components is the `ω`-weighted sum of the
components'. -/
theorem pMass_wsum (P : Val → Prop) {K : ℕ} (W : (Fin K → ℝ) → Prop)
    (V : Fin K → DConf) (ω : Fin K → ℝ) (b : (k : Fin K) → Fin (V k).n → ℝ) :
    pMass P (DConf.wsum W V)
        (fun c => ω (finSigmaFinEquiv.symm c).1 * b _ (finSigmaFinEquiv.symm c).2)
      = ∑ k, ω k * pMass P (V k) (b k) :=
  massOf_sigmaFin P (fun k => (V k).val) ω b

/-- Push-forward along a routing: a rule that routes outcomes along `g` and
coerces them without changing `P` produces the measure of its input, under the
push-forward of the weights along `g`. -/
theorem pMass_pushforward (P : Val → Prop) {V : DConf} {K : ℕ} (ω : Fin K → ℝ)
    (wv : Fin K → Val) (g : Fin K → Fin V.n) (hP : ∀ c, P (wv c) ↔ P (V.val (g c))) :
    massOf P wv ω = pMass P V (pushfwd g ω) :=
  (massOf_congr (val' := fun c => V.val (g c)) hP).trans (massOf_pushfwd P g V.val ω).symm

/-- If `erv i` is the erasure of the outcome `i` of `V`, the erased measure of `V`
is the push-forward of the solution along `erv`. -/
theorem erMass_eq_pushfwd {V : DConf} {erv : Fin V.n → SPLC.Val}
    (herv : ∀ i, ErVal (V.val i) (erv i)) (q : Fin V.n → ℝ) (w : SPLC.Val) :
    erMass V q w = pushfwd erv q w :=
  massOf_congr (P := fun tv => ErVal tv w) (val := V.val) (Q := (· = w)) (val' := erv)
    fun i => ⟨erVal_det (herv i), fun h => h ▸ herv i⟩

/-! ### The source measure

The measure of a scaled distribution value, of a concatenation and of a
weighted sum, for any predicate on values; `srcMass` is the case of the
predicate `· = w`. -/

/-- The weight of a predicate under a weighted sum given as a list is the
weighted sum of its weights under the components. -/
theorem massOf_wsumList (P : SPLC.Val → Prop) [DecidablePred P] :
    ∀ L : List (ℝ × DistVal),
    massOf P (DistVal.wsumList L).val (DistVal.wsumList L).mass
      = (L.map fun c => c.1 * massOf P c.2.val c.2.mass).sum
  | [] => by simp [massOf, DistVal.wsumList]
  | (a, V) :: rest => by
      show massOf P (Fin.append V.val _) (Fin.append (fun i => a * V.mass i) _) = _
      rw [massOf_append, massOf_mul_left, massOf_wsumList P rest]
      simp

/-- The weight of a predicate under a weighted sum is the weighted sum of its
weights under the components. -/
theorem massOf_wsum (P : SPLC.Val → Prop) [DecidablePred P] {K : ℕ}
    (cells : Fin K → ℝ × DistVal) :
    massOf P (DistVal.wsum cells).val (DistVal.wsum cells).mass
      = ∑ j, (cells j).1 * massOf P (cells j).2.val (cells j).2.mass := by
  refine (massOf_wsumList P (List.ofFn cells)).trans ?_
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-- Scaling a distribution value by `a` scales its measure by `a`. -/
theorem srcMass_scale (a : ℝ) (V : DistVal) (w : SPLC.Val) :
    srcMass (V.scale a) w = a * srcMass V w :=
  massOf_mul_left _ V.val a V.mass

/-- The measure of the concatenation of two distribution values is the sum of
their measures. -/
theorem srcMass_append (V1 V2 : DistVal) (w : SPLC.Val) :
    srcMass (V1.append V2) w = srcMass V1 w + srcMass V2 w :=
  massOf_append _ V1.val V2.val V1.mass V2.mass

/-- The measure of a weighted sum is the weighted sum of the measures. -/
theorem srcMass_wsum {K : ℕ} (cells : Fin K → ℝ × DistVal) (w : SPLC.Val) :
    srcMass (DistVal.wsum cells) w = ∑ j, (cells j).1 * srcMass (cells j).2 w :=
  massOf_wsum _ cells

/-! ### Regrouping by fibers

Two finite families that give each value the same probability average any
function of the value alike. This step turns the target mixture, indexed by
the entries of the routing evidence, into the source mixture, indexed by outcomes. -/

/-- Lemma 63 (regrouping by fibers): if `a` and `b` give the same total weight to
each fiber of `f` and `g`, then `∑ i, a i * F (f i) = ∑ j, b j * F (g j)` for
every `F`. The hypothesis says that the push-forwards of `a` along `f` and of
`b` along `g` agree (`sum_mul_eq_of_pushfwd_eq`). -/
theorem sum_fiber_transfer {N M : ℕ} {α : Type*} (f : Fin N → α) (g : Fin M → α)
    (a : Fin N → ℝ) (b : Fin M → ℝ) (F : α → ℝ)
    (h : ∀ v, (∑ i, if f i = v then a i else 0)
            = ∑ j, if g j = v then b j else 0) :
    (∑ i, a i * F (f i)) = ∑ j, b j * F (g j) :=
  sum_mul_eq_of_pushfwd_eq (funext h) F

/-! ## Reduction without the error-raising rules

`ErVal` has no clause for an error value and `ErTm` none for `.errD` nor for a
choice with `?`, so the error propagation rules, (Derr) and the rule of the
choice with `?` are unreachable from a term that erases. The only rules that
create an error are the error cases of (D::σ) (`dascErr`) and of (D::μ)
(`dascDErr`). `RedSt` is `Red` without all of these; Lemma 62
(`redSt_of_red`) shows that none of them fires on the terms of Theorem 7, and
the results below are proved over `RedSt`. -/

/-- `Red` restricted to the rules that a term that erases can use: without
the error cases `dascErr` and `dascDErr`, the error propagation rules
(`eAscV`, `eAddL`, `eAddR`, `eApp`, `eIte`), (Derr) (`derr`) and the choice
with `?` (`dchoiceU`). Every rule it keeps has the same premises as in
`Red`. -/
inductive RedSt : Tm → ℕ → DConf → Prop where
  | dv : ∀ {v}, RedSt (.val v) 1 (DConf.point v)
  | dchoice : ∀ {a m n k1 k2 V1 V2}, 0 ≤ a → a ≤ 1 →
      RedSt m k1 V1 → RedSt n k2 V2 →
      RedSt (.choice (.q a) m n) (k1+k2+1) (DConf.choose a V1 V2)
  | dadd : ∀ {ε1 : TagTy} {r1 : ℝ} {ε2 : TagTy} {r2 : ℝ} {ε3 : TagTy},
      emeetTy ε1 ε2 = some ε3 →
      RedSt (.add (.asc ε1 (.real r1) .real) (.asc ε2 (.real r2) .real)) 1
          (DConf.point (.asc ε3 (.real (r1+r2)) .real))
  | dmon : ∀ {m k V}, RedSt m k V → RedSt m (k+1) V
  | dit : ∀ {ε m n k V}, RedSt m k V →
      RedSt (.ite (.asc ε (.bool true) .bool) m n) (k+1) V
  | dif : ∀ {ε m n k V}, RedSt n k V →
      RedSt (.ite (.asc ε (.bool false) .bool) m n) (k+1) V
  | dascOk : ∀ {ε1 : TagTy} {u σ} {ε2 : TagTy} {σ' ε3},
      emeetTy ε1 ε2 = some ε3 → GoodTy ε3.toF →
      RedSt (.ascV ε2 (.asc ε1 u σ) σ') 1 (DConf.point (.asc ε3 u σ'))
  | dapp : ∀ {ε : TagTy} {σ' m σa Dres v} {s : TagTy} {d : TagD} {k1 k2 w V},
      tagDom ε = some s → tagCod ε = some d →
      RedSt (.ascV s v σ') k1 (DConf.point w) →
      RedSt ((Tm.ascT d m Dres).subErr w Dres) k2 V →
      RedSt (.app (.asc ε (.lam σ' m) (.arrow σa Dres)) v) (k1+k2+1) V
  | dlet : ∀ {m n} {ty : Fin n → FTy} {C : (Fin n → ℝ) → Prop} {ns : Fin n → Tm}
      {k1 k2} {V : DConf}
      {wv : Fin (tagReorderD V.confF ⟨n, ty, C⟩).n → Val}
      {Vk : Fin (tagReorderD V.confF ⟨n, ty, C⟩).n → DConf}
      {Fb : Fin (tagReorderD V.confF ⟨n, ty, C⟩).n → FDist},
      RedSt m k1 V → HasTyT [] m ⟨n, ty, C⟩ →
      (∀ c, RedSt (.ascV ((tagReorderD V.confF ⟨n, ty, C⟩).ty c)
        (V.val (reorderDL V.confF ⟨n, ty, C⟩ c)) (ty (reorderDR V.confF ⟨n, ty, C⟩ c))) 1
        (DConf.point (wv c))) →
      (∀ c, HasTyT [ty (reorderDR V.confF ⟨n, ty, C⟩ c)]
        (ns (reorderDR V.confF ⟨n, ty, C⟩ c)) (Fb c)) →
      (∀ c, RedSt ((ns (reorderDR V.confF ⟨n, ty, C⟩ c)).subErr (wv c) (Fb c)) k2 (Vk c)) →
      RedSt (.letin m n ns) (k1+k2+1) (DConf.wsum (tagReorderD V.confF ⟨n, ty, C⟩).toF.C Vk)
  | dascD : ∀ {εd : TagD} {m μ μb k1} {V : DConf}
      {wv : Fin (emeetD (tagReorderD V.confF μ) εd).n → Val}
      (hval : εd.HValidFor μ μb),
      RedSt m k1 V → HasTyT [] m μ →
      (∃ w, (emeetD (tagReorderD V.confF μ) εd).toF.C w) →
      (∀ c, RedSt (.ascV ((emeetD (tagReorderD V.confF μ) εd).ty c)
        (V.val (reorderDL V.confF μ (meetDL (tagReorderD V.confF μ).toF εd.toF c)))
        (μb.ty ⟨_, emeetD_r_lt_of_hvalid hval.2 c⟩)) 1 (DConf.point (wv c))) →
      RedSt (.ascT εd m μb) (k1+1)
        (DConf.wsumPoint (emeetD (tagReorderD V.confF μ) εd).toF.C wv)


/-- The argument coercion of rule (Dapp) is well typed. The domain of an arrow
evidence relates the two sides in flipped order, which `hvtag_flip` accounts
for on each side. -/
theorem dapp_coercion_typed {ε : TagTy} {σ' σa σX : FTy} {mb : Tm}
    {Dres D0 : FDist} {v : Val} {s : TagTy}
    (hv : HasTyV [] (.asc ε (.lam σ' mb) (.arrow σa Dres)) (.arrow σX D0))
    (hw : HasTyV [] v σX) (hdom : tagDom ε = some s) :
    HasTyT [] (.ascV s v σ') (pointF σ') := by
  cases hv with
  | ascRaw hlam hevε hgeε hgarr =>
    cases hlam with
    | lam hbody hgσ'2 =>
      cases ε with
      | real => simp [tagDom] at hdom
      | bool => simp [tagDom] at hdom
      | unk => simp [tagDom] at hdom
      | arrow s0 d0 =>
        simp only [tagDom, Option.some.injEq] at hdom
        subst hdom
        obtain ⟨hprec1, hprec2⟩ := hevε
        cases hprec1 with
        | arrow hs1 hD1 =>
          cases hprec2 with
          | arrow hs2 hD2 =>
            cases hgeε with
            | arrow hgs hgD =>
              have hgsf : GoodTy s0.flip.toF := by
                rw [TagTy.flip_toF]; exact hgs
              exact .ascV hw ⟨hvtag_flip hs2, hvtag_flip hs1⟩ hgsf hgσ'2

/-- Every `RedSt` derivation is a `Red` derivation. -/
theorem redSt_to_red : ∀ {m : Tm} {k : ℕ} {V : DConf}, RedSt m k V → Red m k V
  | _, _, _, .dv => .dv
  | _, _, _, .dchoice ha0 ha1 h1 h2 =>
      .dchoice ha0 ha1 (redSt_to_red h1) (redSt_to_red h2)
  | _, _, _, .dadd hm => .dadd hm
  | _, _, _, .dmon h0 => .dmon (redSt_to_red h0)
  | _, _, _, .dit h => .dit (redSt_to_red h)
  | _, _, _, .dif h => .dif (redSt_to_red h)
  | _, _, _, .dascOk hm hg => .dascOk hm hg
  | _, _, _, .dapp hd hc h1 h2 => .dapp hd hc (redSt_to_red h1) (redSt_to_red h2)
  | _, _, _, .dlet hr ht hcell hbty hbred =>
      .dlet (redSt_to_red hr) ht
        (fun c => redSt_to_red (hcell c)) hbty (fun c => redSt_to_red (hbred c))
  | _, _, _, .dascD hvR hr ht hsat hcell =>
      .dascD hvR (redSt_to_red hr) ht hsat (fun c => redSt_to_red (hcell c))


/-- A value that has an erasure is not an error. -/
theorem erVal_not_err : ∀ {tv : Val} {v : SPLC.Val}, ErVal tv v → ∀ σ, tv ≠ .err σ
  | _, _, .evar, _ => by simp
  | _, _, .ereal, _ => by simp
  | _, _, .ebool, _ => by simp
  | _, _, .elam _, _ => by simp

/-- Inversion of a value ascription under `RedSt`: the only rule is (D::σ) in
its success case, so the result is a Dirac on an ascribed value. -/
theorem redSt_ascV_asc : ∀ {ε : TagTy} {tv : Val} {σ' : FTy} {k} {V : DConf},
    RedSt (.ascV ε tv σ') k V →
    ∃ (ε3 : TagTy) (u : Raw) (σ2 : FTy), V = DConf.point (.asc ε3 u σ2)
  | _, _, _, _, _, .dascOk _ _ => ⟨_, _, _, rfl⟩
  | _, _, _, _, _, .dmon h0 => redSt_ascV_asc h0

/-- The same inversion, giving the annotation of the result: the target type
`σ'`. -/
theorem redSt_ascV_target : ∀ {ε : TagTy} {tv : Val} {σ' : FTy} {k} {V : DConf},
    RedSt (.ascV ε tv σ') k V → ∀ w, V = DConf.point w → w.tyEntry = σ'
  | _, _, _, _, _, .dascOk _ _, _, hw => by rw [← DConf.point_inj hw]
  | _, _, _, _, _, .dmon h0, w, hw => redSt_ascV_target h0 w hw

/-! ## Coercion under `RedSt` preserves the erasure -/

/-- Lemma 58 (coercion invariance), over `RedSt`: a value ascription of a value
that erases to `v` yields a value that erases to `v`. -/
theorem erVal_ascV_redSt {ε : TagTy} {tv : Val} {σ' : FTy} {k} {w : Val}
    (h : RedSt (.ascV ε tv σ') k (DConf.point w)) {v : SPLC.Val} (hEr : ErVal tv v) :
    ErVal w v := by
  obtain ⟨ε3, u, σ2, hpt⟩ := redSt_ascV_asc h
  obtain rfl : w = Val.asc ε3 u σ2 := DConf.point_inj hpt
  exact erVal_ascV (redSt_to_red h) (by simp) hEr

/-! ## Coverage (Lemma 67)

Every outcome of the result erases to some SPLC value. The statement does not
mention the source run; the `let` case of `erasure_meas` uses it to know which
source value each outcome of the bound term stands for. -/

/-- Lemma 67 (coverage), over `RedSt`: every outcome of the result of a term that
erases has an erasure. `erasure_cover_red` is the form over `Red`. -/
theorem erasure_cover : ∀ (k : ℕ) {tm : Tm} {V : DConf}, RedSt tm k V →
    ∀ {m : SPLC.Tm}, ErTm tm m → ∀ i, ∃ v, ErVal (V.val i) v := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro tm V hred m her i
    cases hred with
    | dv =>
      cases her with
      | eval hv => exact ⟨_, hv⟩
    | dchoice ha0 ha1 h1 h2 =>
      cases her with
      | echoice _ _ e1 e2 =>
        refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i
        · show ∃ v, ErVal (Fin.append _ _ (Fin.castAdd _ i1)) v
          rw [Fin.append_left]
          exact ih _ (by omega) h1 e1 i1
        · show ∃ v, ErVal (Fin.append _ _ (Fin.natAdd _ i2)) v
          rw [Fin.append_right]
          exact ih _ (by omega) h2 e2 i2
    | dadd _ => cases her with | eadd _ _ => exact ⟨_, .ereal⟩
    | dmon h0 => exact ih _ (by omega) h0 her i
    | dit h => cases her with | eite _ e1 _ => exact ih _ (by omega) h e1 i
    | dif h => cases her with | eite _ _ e2 => exact ih _ (by omega) h e2 i
    | dascOk hm hg =>
      cases her with
      | eascV hv => exact ⟨_, erVal_of_raw_eq hv rfl rfl⟩
    | dapp hd hc hcoe hbody =>
      cases her with
      | eapp hf ha =>
        cases hf with
        | elam hb =>
          obtain ⟨ε3, u, σ2, hpt⟩ := redSt_ascV_asc hcoe
          obtain rfl : _ = Val.asc ε3 u σ2 := DConf.point_inj hpt
          have hw := erVal_ascV_redSt hcoe ha
          have hbody' := hbody
          rw [Tm.subErr_asc] at hbody'
          simp only [Tm.subst0, Tm.subst] at hbody'
          exact ih _ (by omega) hbody' (.eascT (erTm_subst0 hb hw)) i
    | dlet hsc hty hcell hbty hbred =>
      cases her with
      | eletin hne h0 hbodies =>
        obtain ⟨v0, hv0⟩ := ih _ (by omega) hsc h0 (reorderDL _ _ (finSigmaFinEquiv.symm i).1)
        have hw := erVal_ascV_redSt (hcell (finSigmaFinEquiv.symm i).1) hv0
        obtain ⟨ε3, u, σ2, hpt⟩ := redSt_ascV_asc (hcell (finSigmaFinEquiv.symm i).1)
        have heqw := DConf.point_inj hpt
        rw [heqw] at hw
        have hbred' := hbred (finSigmaFinEquiv.symm i).1
        rw [heqw, Tm.subErr_asc] at hbred'
        exact ih _ (by omega) hbred' (erTm_subst0 (hbodies _) hw) _
    | @dascD εd _ μ _ _ V0 _ hvR hsc hty hsat hcell =>
      cases her with
      | eascT h0 =>
        obtain ⟨v0, hv0⟩ := ih _ (by omega) hsc h0
          (reorderDL V0.confF μ (meetDL (tagReorderD V0.confF μ).toF εd.toF i))
        exact ⟨v0, erVal_ascV_redSt (hcell i) hv0⟩


/-! ## The measure of a Dirac

A target Dirac and a source Dirac agree on every value, not only on the one they
produce: functionality of the erasure excludes the others. -/

/-- The erased measure of a Dirac configuration on a value that erases to `v`
is the measure of the Dirac distribution value on `v`. -/
theorem erMass_point_of_erVal {tv : Val} {v : SPLC.Val} (hv : ErVal tv v)
    (q : Fin (DConf.point tv).n → ℝ) (hq : (DConf.point tv).C q) :
    ∀ w, erMass (DConf.point tv) q w = srcMass (DistVal.point v) w := by
  intro w
  rw [erMass, pMass_point _ _ _ hq, srcMass_point]
  exact if_congr ⟨erVal_det hv, fun he => he ▸ hv⟩ rfl rfl


/-! ### Marginals over the tagged carrier

`reorderD_left_marginal` and `routing_left_marginal` are stated over the
untagged operators `reorderD D1 D2` and `meetD (reorderD D1 D2) ξ.toF`, while
rules (Dlet) and (D::μ) name their entries over the tagged evidences
(`tagReorderD D1 D2` and `emeetD (tagReorderD D1 D2) ξ`), whose formula types
`toF` agree with the untagged operators only propositionally
(`tagReorderD_toF`, `routing_toF`). The two lemmas below state the marginals
over the tagged carrier, through the entry projections the rules use. Both are
the transport of marginals along the left tags of a tagged witness construction
(`tagWitness_left_marginal`): for (Dlet) the tags are the entry indices of
`D1`; for (D::μ) they are the tags of `tagReorderD D1 D2`, whose push-forward
clause is the first conjunct of `reorderD_C_iff`, as in
`reorderD_left_marginal`. -/

/-- Lemma 66 (routing preserves marginals), tagged form of
`reorderD_left_marginal` over the carrier of rule (Dlet), with the
nonnegativity of the solution and of its marginal. -/
theorem reorderD_left_marginal_tag (D1 D2 : FDist)
    {ω : Fin (D1 ∥ᵗ D2).n → ℝ} (hω : (D1 ∥ᵗ D2).toF.C ω) :
    ∃ q, D1.C q ∧ (∀ c, 0 ≤ ω c) ∧ (∀ i, 0 ≤ q i) ∧ ∀ i : Fin D1.n,
      (∑ c, if reorderDL D1 D2 c = i then ω c else 0) = q i := by
  have hnn : ∀ c, 0 ≤ ω c := reorderD_C_nonneg hω
  exact ⟨_, tagWitness_left_marginal hω Fin.isLt
    (fun p hp => (congrArg D1.C (pushfwd_id p)).mpr hp),
    hnn, pushfwd_nonneg hnn, fun _ => rfl⟩

/-- Lemma 66 (routing preserves marginals), tagged form of
`routing_left_marginal` over the carrier of rule (D::μ). -/
theorem routing_left_marginal_tag (D1 D2 : FDist) (ξ : TagD)
    {ω : Fin ((D1 ∥ᵗ D2) ∘ ξ).n → ℝ}
    (hω : ((D1 ∥ᵗ D2) ∘ ξ).toF.C ω) :
    ∃ q, D1.C q ∧ (∀ c, 0 ≤ ω c) ∧ ∀ i : Fin D1.n,
      (∑ c, if reorderDL D1 D2 (meetDL (D1 ∥ᵗ D2).toF ξ.toF c) = i
            then ω c else 0) = q i :=
  ⟨_, tagWitness_left_marginal hω (fun c => (reorderDL D1 D2 c).isLt)
    (fun p hp => ((reorderD_C_iff D1 D2 p).1 hp).1), meetD_C_nonneg hω, fun _ => rfl⟩


/-! ### Source-side lemmas for the `let` case -/

/-- The measure of a (Dlet) mixture, regrouped by the outcomes `g c` of the
bound term, when the equation at each entry is available only at entries of positive
weight: entries of weight zero contribute nothing. -/
theorem pMass_dlet_pos (P : Val → Prop) {K NI : ℕ} (W : (Fin K → ℝ) → Prop)
    (Vk : Fin K → DConf) (ω : Fin K → ℝ) (b : (k : Fin K) → Fin (Vk k).n → ℝ)
    (hnn : ∀ c, 0 ≤ ω c) (g : Fin K → Fin NI) (S : Fin NI → ℝ)
    (hIH : ∀ c, 0 < ω c → pMass P (Vk c) (b c) = S (g c)) :
    pMass P (DConf.wsum W Vk)
        (fun c => ω (finSigmaFinEquiv.symm c).1 * b _ (finSigmaFinEquiv.symm c).2)
      = ∑ i, pushfwd g ω i * S i := by
  rw [pMass_wsum, sum_pushfwd_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rcases (hnn c).lt_or_eq with hpos | hzero
  · rw [hIH c hpos]
  · rw [← hzero, zero_mul, zero_mul]

/-- Nonnegativity of a source mixture, assuming nonnegative probabilities only in
the summands of positive weight. -/
theorem distVal_wsumList_nonneg : ∀ (L : List (ℝ × DistVal)),
    (∀ c ∈ L, 0 ≤ c.1) → (∀ c ∈ L, 0 < c.1 → ∀ i, 0 ≤ c.2.mass i) →
    ∀ i, 0 ≤ (DistVal.wsumList L).mass i
  | [], _, _, i => i.elim0
  | (a, V) :: rest, h1, h2, i => by
      show 0 ≤ Fin.append (DistVal.scale a V).mass (DistVal.wsumList rest).mass i
      refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i
      · beta_reduce
        rw [Fin.append_left]
        show 0 ≤ a * V.mass i1
        rcases (h1 _ (List.mem_cons.mpr (Or.inl rfl))).lt_or_eq with hpos | hzero
        · exact mul_nonneg hpos.le (h2 _ (List.mem_cons.mpr (Or.inl rfl)) hpos i1)
        · rw [show a = 0 from hzero.symm, zero_mul]
      · beta_reduce
        rw [Fin.append_right]
        exact distVal_wsumList_nonneg rest
          (fun c hc => h1 c (List.mem_cons.mpr (Or.inr hc)))
          (fun c hc => h2 c (List.mem_cons.mpr (Or.inr hc))) i2

/-- A weighted sum with nonnegative weights, whose components with positive
weight have nonnegative probabilities, has nonnegative probabilities. -/
theorem distVal_wsum_nonneg {K : ℕ} (cells : Fin K → ℝ × DistVal)
    (h1 : ∀ j, 0 ≤ (cells j).1)
    (h2 : ∀ j, 0 < (cells j).1 → ∀ i, 0 ≤ (cells j).2.mass i) :
    ∀ i, 0 ≤ (DistVal.wsum cells).mass i := by
  refine distVal_wsumList_nonneg _ ?_ ?_
  · intro c hc
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    exact h1 j
  · intro c hc
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    exact h2 j


/-! ## Source probabilities are nonnegative

The `let` case turns "this source outcome has nonzero probability" into "this value
has positive probability", which requires that probabilities do not cancel. It
suffices that every probability written in the program lies in `[0,1]`. -/

mutual
/-- Every probability in an SPLC value lies in `[0,1]`. -/
def ProbOkV : SPLC.Val → Prop
  | .var _ => True
  | .real _ => True
  | .bool _ => True
  | .lam _ m => ProbOkT m
/-- Every probability in an SPLC term lies in `[0,1]`. Probabilities are real
numbers in the mechanization; this predicate is the grammar's `[0,1]` side
condition, imposed as a hypothesis by the statements that need it. -/
def ProbOkT : SPLC.Tm → Prop
  | .val v => ProbOkV v
  | .app v w => ProbOkV v ∧ ProbOkV w
  | .letin m n => ProbOkT m ∧ ProbOkT n
  | .choice p m n => (0 ≤ p ∧ p ≤ 1) ∧ ProbOkT m ∧ ProbOkT n
  | .ascT m _ => ProbOkT m
  | .ascV v _ => ProbOkV v
  | .ite v m n => ProbOkV v ∧ ProbOkT m ∧ ProbOkT n
  | .add v w => ProbOkV v ∧ ProbOkV w
end

mutual
/-- Renaming preserves `ProbOkV`. -/
theorem probOkV_rename : ∀ (v : SPLC.Val) (c : ℕ), ProbOkV v → ProbOkV (v.rename c)
  | .var _, _, _ => trivial
  | .real _, _, _ => trivial
  | .bool _, _, _ => trivial
  | .lam _ m, c, h => probOkT_rename m (c + 1) h
/-- Renaming preserves `ProbOkT`. -/
theorem probOkT_rename : ∀ (m : SPLC.Tm) (c : ℕ), ProbOkT m → ProbOkT (m.rename c)
  | .val v, c, h => probOkV_rename v c h
  | .app v w, c, h => ⟨probOkV_rename v c h.1, probOkV_rename w c h.2⟩
  | .letin m n, c, h => ⟨probOkT_rename m c h.1, probOkT_rename n (c + 1) h.2⟩
  | .choice _ m n, c, h =>
      ⟨h.1, probOkT_rename m c h.2.1, probOkT_rename n c h.2.2⟩
  | .ascT m _, c, h => probOkT_rename m c h
  | .ascV v _, c, h => probOkV_rename v c h
  | .ite v m n, c, h =>
      ⟨probOkV_rename v c h.1, probOkT_rename m c h.2.1, probOkT_rename n c h.2.2⟩
  | .add v w, c, h => ⟨probOkV_rename v c h.1, probOkV_rename w c h.2⟩
end

mutual
/-- A static SPLC value satisfies `ProbOkV`: the `[0,1]` condition is part of
`IsStaticTm`. -/
theorem probOkV_of_isStaticVal : ∀ {v : SPLC.Val}, IsStaticVal v → ProbOkV v
  | _, .var => trivial
  | _, .real => trivial
  | _, .bool => trivial
  | _, .lam _ hm => probOkT_of_isStaticTm hm
/-- A static SPLC term satisfies `ProbOkT`. -/
theorem probOkT_of_isStaticTm : ∀ {m : SPLC.Tm}, IsStaticTm m → ProbOkT m
  | _, .val hv => probOkV_of_isStaticVal hv
  | _, .app hv hw => ⟨probOkV_of_isStaticVal hv, probOkV_of_isStaticVal hw⟩
  | _, .letin hm hn => ⟨probOkT_of_isStaticTm hm, probOkT_of_isStaticTm hn⟩
  | _, .choice h0 h1 hm hn =>
      ⟨⟨h0, h1⟩, probOkT_of_isStaticTm hm, probOkT_of_isStaticTm hn⟩
  | .ascT m _, .ascT hm _ => (probOkT_of_isStaticTm hm : ProbOkT m)
  | _, .ascV hv _ => probOkV_of_isStaticVal hv
  | _, .ite hv hm hn =>
      ⟨probOkV_of_isStaticVal hv, probOkT_of_isStaticTm hm, probOkT_of_isStaticTm hn⟩
  | _, .add hv hw => ⟨probOkV_of_isStaticVal hv, probOkV_of_isStaticVal hw⟩
end

mutual
/-- Substituting a value that satisfies `ProbOkV` preserves `ProbOkV`. -/
theorem probOkV_subst : ∀ (v : SPLC.Val) (k : ℕ) (w : SPLC.Val), ProbOkV v → ProbOkV w →
    ProbOkV (v.subst k w)
  | .var x, k, w, _, hw => by
      by_cases h1 : x = k
      · simp only [SPLC.Val.subst, if_pos h1]; exact hw
      · by_cases h2 : x > k
        · simp only [SPLC.Val.subst, if_neg h1, if_pos h2]; exact trivial
        · simp only [SPLC.Val.subst, if_neg h1, if_neg h2]; exact trivial
  | .real _, _, _, _, _ => trivial
  | .bool _, _, _, _, _ => trivial
  | .lam _ m, k, w, h, hw =>
      probOkT_subst m (k + 1) (w.rename 0) h (probOkV_rename w 0 hw)
/-- Substituting a value that satisfies `ProbOkV` preserves `ProbOkT`. -/
theorem probOkT_subst : ∀ (m : SPLC.Tm) (k : ℕ) (w : SPLC.Val), ProbOkT m → ProbOkV w →
    ProbOkT (m.subst k w)
  | .val v, k, w, h, hw => probOkV_subst v k w h hw
  | .app v u, k, w, h, hw =>
      ⟨probOkV_subst v k w h.1 hw, probOkV_subst u k w h.2 hw⟩
  | .letin m n, k, w, h, hw =>
      ⟨probOkT_subst m k w h.1 hw,
       probOkT_subst n (k + 1) (w.rename 0) h.2 (probOkV_rename w 0 hw)⟩
  | .choice _ m n, k, w, h, hw =>
      ⟨h.1, probOkT_subst m k w h.2.1 hw, probOkT_subst n k w h.2.2 hw⟩
  | .ascT m _, k, w, h, hw => probOkT_subst m k w h hw
  | .ascV v _, k, w, h, hw => probOkV_subst v k w h hw
  | .ite v m n, k, w, h, hw =>
      ⟨probOkV_subst v k w h.1 hw, probOkT_subst m k w h.2.1 hw,
       probOkT_subst n k w h.2.2 hw⟩
  | .add v u, k, w, h, hw =>
      ⟨probOkV_subst v k w h.1 hw, probOkV_subst u k w h.2 hw⟩
end

mutual
/-- The erasure of a TPLC value has every probability in `[0,1]`. -/
theorem probOkV_of_erVal : ∀ {tv : Val} {v : SPLC.Val}, ErVal tv v → ProbOkV v
  | _, _, .evar => trivial
  | _, _, .ereal => trivial
  | _, _, .ebool => trivial
  | _, _, .elam hb => probOkT_of_erTm hb
/-- The erasure of a TPLC term has every probability in `[0,1]`. -/
theorem probOkT_of_erTm : ∀ {tm : Tm} {m : SPLC.Tm}, ErTm tm m → ProbOkT m
  | _, _, .eval hv => probOkV_of_erVal hv
  | _, _, .eapp h1 h2 => ⟨probOkV_of_erVal h1, probOkV_of_erVal h2⟩
  | _, _, .eadd h1 h2 => ⟨probOkV_of_erVal h1, probOkV_of_erVal h2⟩
  | _, _, .eite h1 h2 h3 =>
      ⟨probOkV_of_erVal h1, probOkT_of_erTm h2, probOkT_of_erTm h3⟩
  | _, _, .echoice hp0 hp1 h1 h2 =>
      ⟨⟨hp0, hp1⟩, probOkT_of_erTm h1, probOkT_of_erTm h2⟩
  | _, _, .eletin hpos h1 h2 => ⟨probOkT_of_erTm h1, probOkT_of_erTm (h2 ⟨0, hpos⟩)⟩
  | _, _, .eascV hv => probOkV_of_erVal hv
  | _, _, .eascT hm => by
      simp only [ProbOkT]
      exact probOkT_of_erTm hm
end

/-! ### Combinators of `DistVal` -/

/-- Scaling by a nonnegative `a` preserves nonnegative probabilities. -/
theorem distVal_scale_nonneg {a : ℝ} {V : DistVal} (ha : 0 ≤ a)
    (h : ∀ i, 0 ≤ V.mass i) : ∀ i, 0 ≤ (V.scale a).mass i :=
  fun i => mul_nonneg ha (h i)

/-- Concatenation preserves nonnegative probabilities. -/
theorem distVal_append_nonneg {V1 V2 : DistVal} (h1 : ∀ i, 0 ≤ V1.mass i)
    (h2 : ∀ i, 0 ≤ V2.mass i) : ∀ i, 0 ≤ (V1.append V2).mass i := by
  intro i
  show 0 ≤ Fin.append V1.mass V2.mass i
  refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i
  · beta_reduce; rw [Fin.append_left]; exact h1 i1
  · beta_reduce; rw [Fin.append_right]; exact h2 i2

/-- A property of every value of two distribution values holds of every value
of their concatenation. -/
theorem distVal_append_val {V1 V2 : DistVal} {P : SPLC.Val → Prop}
    (h1 : ∀ i, P (V1.val i)) (h2 : ∀ i, P (V2.val i)) :
    ∀ i, P ((V1.append V2).val i) := by
  intro i
  show P (Fin.append V1.val V2.val i)
  refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i
  · beta_reduce; rw [Fin.append_left]; exact h1 i1
  · beta_reduce; rw [Fin.append_right]; exact h2 i2

/-- A property of every value of the components of a weighted sum given as a
list holds of every value of the sum. -/
theorem distVal_wsumList_val {P : SPLC.Val → Prop} : ∀ (L : List (ℝ × DistVal)),
    (∀ c ∈ L, ∀ i, P (c.2.val i)) → ∀ i, P ((DistVal.wsumList L).val i)
  | [], _, i => i.elim0
  | (a, V) :: rest, h, i => by
      refine distVal_append_val (P := P) (fun i1 => ?_) ?_ i
      · exact h _ (List.mem_cons.mpr (Or.inl rfl)) i1
      · exact distVal_wsumList_val rest
          (fun c hc => h c (List.mem_cons.mpr (Or.inr hc)))

/-- A property of every value of the components of a weighted sum holds of
every value of the sum. -/
theorem distVal_wsum_val {P : SPLC.Val → Prop} {K : ℕ} (cells : Fin K → ℝ × DistVal)
    (h : ∀ j i, P ((cells j).2.val i)) :
    ∀ i, P ((DistVal.wsum cells).val i) := by
  refine distVal_wsumList_val _ ?_
  intro c hc
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
  exact h j

/-- The probabilities of a run of an SPLC term satisfying `ProbOkT` are nonnegative,
and its values satisfy `ProbOkV`. -/
theorem red_probOk : ∀ (k : ℕ) {m : SPLC.Tm} {V : DistVal}, SPLC.Red m k V → ProbOkT m →
    (∀ i, 0 ≤ V.mass i) ∧ (∀ i, ProbOkV (V.val i)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m V hs hok
    cases hs with
    | sv => exact ⟨fun _ => zero_le_one, fun _ => hok⟩
    | sapp h =>
      exact ih _ (by omega) h (probOkT_subst _ 0 _ hok.1 hok.2)
    | schoice h1 h2 =>
      obtain ⟨hp, hok1, hok2⟩ := hok
      obtain ⟨hn1, hv1⟩ := ih _ (by omega) h1 hok1
      obtain ⟨hn2, hv2⟩ := ih _ (by omega) h2 hok2
      exact ⟨distVal_append_nonneg (distVal_scale_nonneg hp.1 hn1)
          (distVal_scale_nonneg (by linarith [hp.2]) hn2),
        distVal_append_val (P := ProbOkV) hv1 hv2⟩
    | @slet _ _ _ _ _ _ cells _ hsc hinj hcompl hbody =>
      obtain ⟨hok1, hok2⟩ := hok
      obtain ⟨hn0, hv0⟩ := ih _ (by omega) hsc hok1
      have hcell := fun j =>
        ih _ (by omega) (hbody j) (probOkT_subst _ 0 _ hok2 (hv0 (cells j)))
      exact ⟨distVal_wsum_nonneg _ (fun j => hn0 _) (fun j _ => (hcell j).1),
        distVal_wsum_val _ (fun j => (hcell j).2)⟩
    | sascV => exact ⟨fun _ => zero_le_one, fun _ => hok⟩
    | sascT h => exact ih _ (by omega) h hok
    | sadd => exact ⟨fun _ => zero_le_one, fun _ => trivial⟩
    | sit h => exact ih _ (by omega) h hok.2.1
    | sif h => exact ih _ (by omega) h hok.2.2


/-! ## Erasure preserves measure (Theorem 8)

By induction on the target reduction, with the source run given. The source run
is quantified inside the conclusion, so in the `let` case the induction
hypothesis on the bound term also supplies the determinism of the source that
the regrouping needs. -/

/-- Theorem 8 (erasure preserves measure), over `RedSt`: if `tm` erases to
`ms`, `tm` reduces to `V` and `ms` to `Vs`, then for every solution `q` of the
formula of `V` and every SPLC value `w`, `erMass V q w = srcMass Vs w`.
`erasure_meas_red` is the form over `Red`. -/
theorem erasure_meas : ∀ (k : ℕ) {tm : Tm} {V : DConf}, RedSt tm k V →
    ∀ {ms : SPLC.Tm} {ks : ℕ} {Vs : DistVal}, ErTm tm ms → ms ⇓ₛ[ks] Vs →
    ∀ q, V.C q → ∀ w, erMass V q w = srcMass Vs w := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro tm V hred ms ks Vs her hs q hq w
    cases hred with
    | dv =>
      cases her with
      | eval hv =>
        cases hs with
        | sv => exact erMass_point_of_erVal hv q hq w
    | dchoice ha0 ha1 h1 h2 =>
      cases her with
      | echoice hp0 hp1 e1 e2 =>
        cases hs with
        | schoice hs1 hs2 =>
          obtain ⟨p1, q2, hp1', hq2', rfl⟩ := hq
          rw [erMass, pMass_choose, srcMass_append, srcMass_scale, srcMass_scale,
            ← erMass, ← erMass,
            ih _ (by omega) h1 e1 hs1 p1 hp1' w,
            ih _ (by omega) h2 e2 hs2 q2 hq2' w]
    | dadd hm =>
      cases her with
      | eadd h1 h2 =>
        cases h1
        cases h2
        cases hs with
        | sadd => exact erMass_point_of_erVal .ereal q hq w
    | dmon h0 => exact ih _ (by omega) h0 her hs q hq w
    | dit h =>
      cases her with
      | eite hv e1 e2 =>
        cases hv
        cases hs with
        | sit hs1 => exact ih _ (by omega) h e1 hs1 q hq w
    | dif h =>
      cases her with
      | eite hv e1 e2 =>
        cases hv
        cases hs with
        | sif hs2 => exact ih _ (by omega) h e2 hs2 q hq w
    | dascOk hm hg =>
      cases her with
      | eascV hv =>
        cases hs with
        | sascV => exact erMass_point_of_erVal (erVal_of_raw_eq hv rfl rfl) q hq w
    | @dapp ε σ' m0 σa Dres v s d k1 k2 wc V' hd hc hcoe hbody =>
      cases her with
      | eapp hf ha =>
        cases hf with
        | elam hb =>
          cases hs with
          | sapp hs0 =>
            have hw := erVal_ascV_redSt hcoe ha
            obtain ⟨ε3, u3, σ3, hpt⟩ := redSt_ascV_asc hcoe
            obtain rfl : wc = Val.asc ε3 u3 σ3 := DConf.point_inj hpt
            have hbody' := hbody
            rw [Tm.subErr_asc] at hbody'
            simp only [Tm.subst0, Tm.subst] at hbody'
            exact ih _ (by omega) hbody' (.eascT (erTm_subst0 hb hw))
              (SPLC.Red.sascT hs0) q hq w
    | @dascD εd m0 μ μb k1 V0 wv hvR hsc hty hsat hcell =>
      cases her with
      | eascT h0 =>
        cases hs with
        | sascT hs0 =>
          set idx := fun c => reorderDL V0.confF μ (meetDL (tagReorderD V0.confF μ).toF εd.toF c)
            with hidx
          have hP : ∀ c, (ErVal (wv c) w ↔ ErVal (V0.val (idx c)) w) := by
            intro c
            obtain ⟨vc, hvc⟩ := erasure_cover _ hsc h0 (idx c)
            have hwc := erVal_ascV_redSt (hcell c) hvc
            constructor
            · intro hh; exact (erVal_det hwc hh) ▸ hvc
            · intro hh; exact (erVal_det hvc hh) ▸ hwc
          obtain ⟨q0, hq0, -, hmarg⟩ :=
            routing_left_marginal_tag V0.confF μ εd hq
          obtain rfl : pushfwd idx q = q0 := funext hmarg
          exact (pMass_pushforward (fun tv => ErVal tv w) q wv _ hP).trans
            (ih _ (by omega) hsc h0 hs0 _ hq0 w)
    | @dlet m0 n ty C ns k1 k2 V0 wv Vk Fb hsc hty hcell hbty hbred =>
      cases her with
      | eletin hne h0 hbodies =>
        cases hs with
        | @slet _ _ j1 j2 Vs0 K cells Ws hs0 hinj hcompl hsbody =>
          set idx := reorderDL V0.confF ⟨n, ty, C⟩ with hidx
          obtain ⟨ω, hωC, b, hbC, hx⟩ := hq
          obtain rfl := funext hx
          obtain ⟨q0, hq0, hωnn, hq0nn, hmarg⟩ :=
            reorderD_left_marginal_tag V0.confF ⟨n, ty, C⟩ hωC
          obtain rfl : pushfwd idx ω = q0 := funext hmarg
          have hsceq := ih _ (by omega) hsc h0 hs0 _ hq0
          have hcovf := erasure_cover _ hsc h0
          choose erv herv using hcovf
          have hsnn : ∀ i, 0 ≤ Vs0.mass i :=
            (red_probOk _ hs0 (probOkT_of_erTm h0)).1
          -- the fiber identity given by the induction hypothesis on the bound term:
          -- the outcomes that erase to `v` weigh what `v` weighs in the source
          have hfib : ∀ v, pushfwd erv (pushfwd idx ω) v
              = srcMass Vs0 v := fun v =>
            (erMass_eq_pushfwd herv _ v).symm.trans (hsceq v)
          -- an entry of positive weight routes to an outcome of positive source measure
          have hsrcpos : ∀ c, 0 < ω c → 0 < srcMass Vs0 (erv (idx c)) := fun c hc =>
            ((hc.trans_le (le_pushfwd hωnn c)).trans_le (le_pushfwd hq0nn _)).trans_eq (hfib _)
          -- the induction hypothesis for each entry
          have hcellIH : ∀ (c : Fin (tagReorderD V0.confF ⟨n, ty, C⟩).n) (j : Fin K),
              Vs0.val (cells j) = erv (idx c) → 0 < ω c →
              pMass (fun tv => ErVal tv w) (Vk c) (b c) = srcMass (Ws j) w := by
            intro c j hval hpos
            have hwc : ErVal (wv c) (erv (idx c)) :=
              erVal_ascV_redSt (hcell c) (herv _)
            obtain ⟨ε3, u3, σ3, hpt⟩ := redSt_ascV_asc (hcell c)
            have heqw := DConf.point_inj hpt
            rw [heqw] at hwc
            have hbred' := hbred c
            rw [heqw, Tm.subErr_asc] at hbred'
            have hErb := erTm_subst0 (hbodies (reorderDR V0.confF ⟨n, ty, C⟩ c)) hwc
            rw [← hval] at hErb
            exact ih _ (by omega) hbred' hErb (hsbody j) (b c) (hbC c hpos) w
          -- the measure of the body at each source outcome of positive measure: such
          -- an outcome is the erasure of an entry of positive weight (`pushfwd_pos`)
          have hF : ∀ v : SPLC.Val, ∃ r : ℝ, ∀ j : Fin K, Vs0.val (cells j) = v →
              0 < srcMass Vs0 v → srcMass (Ws j) w = r := by
            intro v
            by_cases hpos : 0 < srcMass Vs0 v
            · obtain ⟨i, rfl, hi⟩ := pushfwd_pos (hpos.trans_eq (hfib v).symm)
              obtain ⟨c, rfl, hc⟩ := pushfwd_pos hi
              exact ⟨_, fun j hj _ => (hcellIH c j hj hc).symm⟩
            · exact ⟨0, fun _ _ h => absurd h hpos⟩
          choose F hFspec using hF
          -- (1) the target mixture, regrouped by outcome
          have hleft : pMass (fun tv => ErVal tv w)
              (DConf.wsum (tagReorderD V0.confF ⟨n, ty, C⟩).toF.C Vk)
              (fun c => ω (finSigmaFinEquiv.symm c).1 * b _ (finSigmaFinEquiv.symm c).2)
              = ∑ i, pushfwd idx ω i * F (erv i) := by
            refine pMass_dlet_pos _ _ Vk ω b hωnn _ (fun i => F (erv i)) fun c hpos => ?_
            obtain ⟨j', hj', -⟩ := massOf_pos (hsrcpos c hpos)
            obtain ⟨j, rfl⟩ := hcompl j'
            rw [hcellIH c j hj' hpos]
            exact hFspec _ j hj' (hsrcpos c hpos)
          -- (2) the source mixture, regrouped by outcome
          have hright : srcMass (DistVal.wsum (fun j => (Vs0.mass (cells j), Ws j))) w
              = ∑ j, Vs0.mass (cells j) * F (Vs0.val (cells j)) := by
            rw [srcMass_wsum]
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hm : Vs0.mass (cells j) = 0
            · rw [hm, zero_mul, zero_mul]
            · rw [hFspec _ j rfl
                (((hsnn _).lt_of_ne (Ne.symm hm)).trans_le (le_massOf hsnn rfl))]
          -- (3) transfer along the fibers
          rw [hright]
          refine hleft.trans (sum_fiber_transfer erv (fun j => Vs0.val (cells j)) _
            (fun j => Vs0.mass (cells j)) F fun v => (hfib v).trans ?_)
          exact (massOf_comp_of_injective _ Vs0.val Vs0.mass hinj fun i _ => hcompl i).symm


/-! ## Normalization of the source

The elaboration puts the operands of application, addition and the conditional
in monadic normal form, binding them with `let`s that the source
does not have. `anfV`/`anfT`, the normalization of Section C.7, perform this
rewriting on the source side and replace every annotation by the placeholder.
`elab_erVal`/`elab_erTm` (Lemma 60) show that every elaboration of an embedded
term erases to its normalization, and `red_anf` (Lemma 65) that the normalized
source runs to the same measure. -/

mutual
/-- The normalization of SPLC values (Section C.7): the annotation of a `λ`
becomes the placeholder `.unk` and its body is normalized. -/
def anfV : SPLC.Val → SPLC.Val
  | .var x => .var x
  | .real r => .real r
  | .bool b => .bool b
  | .lam _ m => .lam .unk (anfT m)
/-- The normalization of SPLC terms (Section C.7): application, addition and
the conditional become nested `let`s that bind the operands,
ascribed to the placeholder; ascriptions take the placeholder (see `ErVal`). -/
def anfT : SPLC.Tm → SPLC.Tm
  | .val v => .val (anfV v)
  | .app v w => .letin (.ascV (anfV w) .unk)
      (.letin (.ascV ((anfV v).rename 0) .unk) (.app (.var 0) (.var 1)))
  | .letin m n => .letin (anfT m) (anfT n)
  | .choice p m n => .choice p (anfT m) (anfT n)
  | .ascT m _ => .ascT (anfT m) (.dist [])
  | .ascV v _ => .ascV (anfV v) .unk
  | .ite v m n => .letin (.ascV (anfV v) .unk)
      (.ite (.var 0) ((anfT m).rename 0) ((anfT n).rename 0))
  | .add v w => .letin (.ascV (anfV v) .unk)
      (.letin (.ascV ((anfV w).rename 0) .unk) (.add (.var 1) (.var 0)))
end

mutual
/-- Normalization preserves the bound on free variables (values). -/
theorem anfV_fvBelow : ∀ (v : SPLC.Val) (n : ℕ), v.FvBelow n → (anfV v).FvBelow n
  | .var _, _, h => h
  | .real _, _, _ => trivial
  | .bool _, _, _ => trivial
  | .lam _ m, n, h => anfT_fvBelow m (n + 1) h
/-- Normalization preserves the bound on free variables (terms). -/
theorem anfT_fvBelow : ∀ (m : SPLC.Tm) (n : ℕ), m.FvBelow n → (anfT m).FvBelow n
  | .val v, n, h => anfV_fvBelow v n h
  | .app v w, n, h =>
      ⟨anfV_fvBelow w n h.2,
       SPLC.Val.rename_fvBelow (anfV v) n 0 (anfV_fvBelow v n h.1),
       by show (0:ℕ) < n + 1 + 1; omega, by show (1:ℕ) < n + 1 + 1; omega⟩
  | .letin m b, n, h => ⟨anfT_fvBelow m n h.1, anfT_fvBelow b (n + 1) h.2⟩
  | .choice _ m1 m2, n, h => ⟨anfT_fvBelow m1 n h.1, anfT_fvBelow m2 n h.2⟩
  | .ascT m _, n, h => anfT_fvBelow m n h
  | .ascV v _, n, h => anfV_fvBelow v n h
  | .ite v m1 m2, n, h =>
      ⟨anfV_fvBelow v n h.1, by show (0:ℕ) < n + 1; omega,
       SPLC.Tm.rename_fvBelow (anfT m1) n 0 (anfT_fvBelow m1 n h.2.1),
       SPLC.Tm.rename_fvBelow (anfT m2) n 0 (anfT_fvBelow m2 n h.2.2)⟩
  | .add v w, n, h =>
      ⟨anfV_fvBelow v n h.1,
       SPLC.Val.rename_fvBelow (anfV w) n 0 (anfV_fvBelow w n h.2),
       by show (1:ℕ) < n + 1 + 1; omega, by show (0:ℕ) < n + 1 + 1; omega⟩
end

mutual
/-- Normalization commutes with the substitution of a closed value (values). -/
theorem anfV_subst : ∀ (v : SPLC.Val) (k : ℕ) (w : SPLC.Val), w.FvBelow 0 →
    anfV (v.subst k w) = (anfV v).subst k (anfV w)
  | .var x, k, w, _ => by
      by_cases h1 : x = k
      · simp only [SPLC.Val.subst, if_pos h1, anfV]
      · by_cases h2 : x > k
        · simp only [SPLC.Val.subst, if_neg h1, if_pos h2, anfV]
        · simp only [SPLC.Val.subst, if_neg h1, if_neg h2, anfV]
  | .real _, _, _, _ => rfl
  | .bool _, _, _, _ => rfl
  | .lam τ m, k, w, hw => by
      have hwa : (anfV w).FvBelow 0 := anfV_fvBelow w 0 hw
      simp only [SPLC.Val.subst, anfV]
      rw [SPLC.Val.rename_below hw (Nat.zero_le 0),
        anfT_subst m (k + 1) w hw, SPLC.Val.rename_below hwa (Nat.zero_le 0)]
/-- Normalization commutes with the substitution of a closed value (terms). -/
theorem anfT_subst : ∀ (m : SPLC.Tm) (k : ℕ) (w : SPLC.Val), w.FvBelow 0 →
    anfT (m.subst k w) = (anfT m).subst k (anfV w)
  | .val v, k, w, hw => by
      simp only [SPLC.Tm.subst, anfT]; rw [anfV_subst v k w hw]
  | .app v u, k, w, hw => by
      have hwa : (anfV w).FvBelow 0 := anfV_fvBelow w 0 hw
      simp only [SPLC.Tm.subst, anfT, SPLC.Val.subst]
      rw [SPLC.Val.rename_below hwa (Nat.zero_le 0),
        SPLC.Val.rename_below hwa (Nat.zero_le 0),
        anfV_subst u k w hw, SPLC.Val.rename_subst (anfV v) 0 k (Nat.zero_le k)
          (anfV w) hwa, anfV_subst v k w hw]
      simp only [SPLC.Val.subst, if_neg (by omega : ¬ (0:ℕ) = k + 1 + 1),
        if_neg (by omega : ¬ (0:ℕ) > k + 1 + 1),
        if_neg (by omega : ¬ (1:ℕ) = k + 1 + 1),
        if_neg (by omega : ¬ (1:ℕ) > k + 1 + 1)]
  | .letin m b, k, w, hw => by
      have hwa : (anfV w).FvBelow 0 := anfV_fvBelow w 0 hw
      simp only [SPLC.Tm.subst, anfT]
      rw [SPLC.Val.rename_below hw (Nat.zero_le 0), anfT_subst m k w hw,
        anfT_subst b (k + 1) w hw, SPLC.Val.rename_below hwa (Nat.zero_le 0)]
  | .choice p m1 m2, k, w, hw => by
      simp only [SPLC.Tm.subst, anfT]
      rw [anfT_subst m1 k w hw, anfT_subst m2 k w hw]
  | .ascT m T, k, w, hw => by
      simp only [SPLC.Tm.subst, anfT]; rw [anfT_subst m k w hw]
  | .ascV v τ, k, w, hw => by
      simp only [SPLC.Tm.subst, anfT]; rw [anfV_subst v k w hw]
  | .ite v m1 m2, k, w, hw => by
      have hwa : (anfV w).FvBelow 0 := anfV_fvBelow w 0 hw
      simp only [SPLC.Tm.subst, anfT, SPLC.Tm.subst]
      rw [SPLC.Val.rename_below hwa (Nat.zero_le 0), anfV_subst v k w hw,
        SPLC.Tm.rename_subst (anfT m1) 0 k (Nat.zero_le k) (anfV w) hwa,
        SPLC.Tm.rename_subst (anfT m2) 0 k (Nat.zero_le k) (anfV w) hwa,
        anfT_subst m1 k w hw, anfT_subst m2 k w hw]
      simp only [SPLC.Val.subst, if_neg (by omega : ¬ (0:ℕ) = k + 1),
        if_neg (by omega : ¬ (0:ℕ) > k + 1)]
  | .add v u, k, w, hw => by
      have hwa : (anfV w).FvBelow 0 := anfV_fvBelow w 0 hw
      simp only [SPLC.Tm.subst, anfT, SPLC.Val.subst]
      rw [SPLC.Val.rename_below hwa (Nat.zero_le 0),
        SPLC.Val.rename_below hwa (Nat.zero_le 0),
        anfV_subst v k w hw, SPLC.Val.rename_subst (anfV u) 0 k (Nat.zero_le k)
          (anfV w) hwa, anfV_subst u k w hw]
      simp only [SPLC.Val.subst, if_neg (by omega : ¬ (0:ℕ) = k + 1 + 1),
        if_neg (by omega : ¬ (0:ℕ) > k + 1 + 1),
        if_neg (by omega : ¬ (1:ℕ) = k + 1 + 1),
        if_neg (by omega : ¬ (1:ℕ) > k + 1 + 1)]
end

/-- The values of a run of a closed SPLC term are closed. -/
theorem red_closed : ∀ (k : ℕ) {m : SPLC.Tm} {V : DistVal}, SPLC.Red m k V →
    m.FvBelow 0 → ∀ i, (V.val i).FvBelow 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m V hs hcl
    cases hs with
    | sv => exact fun _ => hcl
    | sapp h =>
      exact ih _ (by omega) h (SPLC.Tm.subst_pres_below hcl.1 hcl.2 (le_refl 0))
    | schoice h1 h2 =>
      have c1 := ih _ (by omega) h1 hcl.1
      have c2 := ih _ (by omega) h2 hcl.2
      exact distVal_append_val (P := fun v => SPLC.Val.FvBelow v 0) c1 c2
    | @slet _ _ _ _ _ _ cells _ hsc hinj hcompl hbody =>
      have hv0 := ih _ (by omega) hsc hcl.1
      have hcb := fun j => ih _ (by omega) (hbody j)
        (SPLC.Tm.subst_pres_below hcl.2 (hv0 (cells j)) (le_refl 0))
      exact distVal_wsum_val (P := fun v => SPLC.Val.FvBelow v 0) _ hcb
    | sascV => exact fun _ => hcl
    | sascT h => exact ih _ (by omega) h hcl
    | sadd => exact fun _ => trivial
    | sit h => exact ih _ (by omega) h hcl.2.1
    | sif h => exact ih _ (by omega) h hcl.2.2


/-! ### Elaboration erases to the normalized source (Lemma 60) -/

mutual
/-- Lemma 60 (elaboration erases to the normalized source), values. -/
theorem elab_erVal : ∀ {Γ σ tv} (v : SPLC.Val), Γ ⊢ embedV v : σ ⇝ tv →
    CtxGood Γ → ErVal tv (anfV v)
  | _, _, _, .var _, h, _ => by simp only [embedV] at h; cases h; exact .evar
  | _, _, _, .real _, h, _ => by simp only [embedV] at h; cases h; exact .ereal
  | _, _, _, .bool _, h, _ => by simp only [embedV] at h; cases h; exact .ebool
  | Γ, _, _, .lam τ mb, h, hΓ => by
      simp only [embedV] at h
      cases h with
      | elam hm hτ =>
        exact .elam (elab_erTm mb hm (ctxGood_cons (goodTy_liftF hτ) hΓ))
/-- Lemma 60 (elaboration erases to the normalized source): every elaboration
of the embedding of an SPLC term `m` erases to `anfT m`. -/
theorem elab_erTm : ∀ {Γ D tm} (m : SPLC.Tm), Γ ⊢ embedT m : D ⇝ tm →
    CtxGood Γ → ErTm tm (anfT m)
  | _, _, _, .val v, h, hΓ => by
      simp only [embedT] at h
      cases h with
      | eval hv => exact .eval (elab_erVal v hv hΓ)
  | _, _, _, .choice p m1 m2, h, hΓ => by
      simp only [embedT] at h
      cases h with
      | echoice ha0 ha1 hm hn =>
        exact .echoice ha0 ha1 (elab_erTm m1 hm hΓ) (elab_erTm m2 hn hΓ)
  | _, _, _, .ascV v τ, h, hΓ => by
      simp only [embedT] at h
      cases h with
      | eascV hv _ _ _ => exact .eascV (elab_erVal v hv hΓ)
  | _, _, _, .ascT m T, h, hΓ => by
      simp only [embedT] at h
      cases h with
      | eascT hm _ _ => exact .eascT (elab_erTm m hm hΓ)
  | Γ, _, _, .letin m b, h, hΓ => by
      simp only [embedT] at h
      cases h with
      | @eletin _ _ _ k ty C _ tns _ hm hbody =>
        have hgD : GoodD ⟨k, ty, C⟩ := wf_tm (elab_preserves_tm hm hΓ) hΓ
        exact .eletin hgD.good.pos (elab_erTm m hm hΓ)
          (fun i => elab_erTm b (hbody i) (ctxGood_cons (hgD.tys i) hΓ))
  | Γ, _, _, .app v w, h, hΓ => by
      simp only [embedT] at h
      cases h with
      | eapp hv hw _ _ _ _ =>
        exact .eletin Nat.one_pos (.eascV (elab_erVal w hw hΓ)) fun _ =>
          .eletin Nat.one_pos (.eascV (erVal_rename (elab_erVal v hv hΓ) 0)) fun _ =>
            .eapp .evar .evar
  | Γ, _, _, .add v w, h, hΓ => by
      simp only [embedT] at h
      cases h with
      | eadd hv hw _ _ _ _ =>
        exact .eletin Nat.one_pos (.eascV (elab_erVal v hv hΓ)) fun _ =>
          .eletin Nat.one_pos (.eascV (erVal_rename (elab_erVal w hw hΓ) 0)) fun _ =>
            .eadd .evar .evar
  | Γ, _, _, .ite v m1 m2, h, hΓ => by
      simp only [embedT] at h
      cases h with
      | eite hv hm hn _ _ _ =>
        exact .eletin Nat.one_pos (.eascV (elab_erVal v hv hΓ)) fun _ =>
          .eite .evar (erTm_rename (elab_erTm m1 hm hΓ) 0)
            (erTm_rename (elab_erTm m2 hn hΓ) 0)
end


/-! ### Source determinism modulo measure (Lemma 64)

`SPLC.Red` is not deterministic as a relation, since its `let` rule chooses how
it enumerates the outcomes (`cells`), but the measure it produces is. The proof
regroups both mixtures by the fibers of the value, as in the `let` case of
`erasure_meas`. -/

/-- Lemma 64 (source determinism modulo measure): two runs of the same closed
SPLC term satisfying `ProbOkT` give every value the same probability. -/
theorem red_srcMass_det : ∀ (k1 : ℕ) {m : SPLC.Tm} {V1 : DistVal}, m ⇓ₛ[k1] V1 →
    m.FvBelow 0 → ProbOkT m →
    ∀ {k2 : ℕ} {V2 : DistVal}, m ⇓ₛ[k2] V2 → ∀ w, srcMass V1 w = srcMass V2 w := by
  intro k1
  induction k1 using Nat.strong_induction_on with
  | _ k ih =>
    intro m V1 hs1 hcl hok k2 V2 hs2 w
    cases hs1 with
    | sv => cases hs2 with | sv => rfl
    | sapp h1 =>
      cases hs2 with
      | sapp h2 =>
        exact ih _ (by omega) h1 (SPLC.Tm.subst_pres_below hcl.1 hcl.2 (le_refl 0))
          (probOkT_subst _ 0 _ hok.1 hok.2) h2 w
    | schoice h1 h1' =>
      cases hs2 with
      | schoice h2 h2' =>
        rw [srcMass_append, srcMass_append, srcMass_scale, srcMass_scale,
          srcMass_scale, srcMass_scale,
          ih _ (by omega) h1 hcl.1 hok.2.1 h2 w,
          ih _ (by omega) h1' hcl.2 hok.2.2 h2' w]
    | sascV => cases hs2 with | sascV => rfl
    | sascT h1 =>
      cases hs2 with
      | sascT h2 => exact ih _ (by omega) h1 hcl hok h2 w
    | sadd => cases hs2 with | sadd => rfl
    | sit h1 =>
      cases hs2 with
      | sit h2 => exact ih _ (by omega) h1 hcl.2.1 hok.2.1 h2 w
    | sif h1 =>
      cases hs2 with
      | sif h2 => exact ih _ (by omega) h1 hcl.2.2 hok.2.2 h2 w
    | @slet m0 b ka k2a Va Ka cellsa Wa hsa hinja hcompla hbodya =>
      cases hs2 with
      | @slet _ _ kb k2b Vb Kb cellsb Wb hsb hinjb hcomplb hbodyb =>
        have hsc := ih ka (by omega) hsa hcl.1 hok.1 hsb
        have hnnb := (red_probOk _ hsb hok.1).1
        have hva := (red_probOk _ hsa hok.1).2
        have hcla := red_closed _ hsa hcl.1
        have hbcl : ∀ (i : Fin Va.n), (b.subst0 (Va.val i)).FvBelow 0 :=
          fun i => SPLC.Tm.subst_pres_below hcl.2 (hcla i) (le_refl 0)
        have hbok : ∀ (i : Fin Va.n), ProbOkT (b.subst0 (Va.val i)) :=
          fun i => probOkT_subst _ 0 _ hok.2 (hva i)
        have hF : ∀ v : SPLC.Val, ∃ r : ℝ,
            ∀ j : Fin Ka, Va.val (cellsa j) = v → r = srcMass (Wa j) w := by
          intro v
          by_cases hex : ∃ j : Fin Ka, Va.val (cellsa j) = v
          · obtain ⟨j0, rfl⟩ := hex
            refine ⟨srcMass (Wa j0) w, fun j hj => ?_⟩
            have h2 := hbodya j
            rw [hj] at h2
            exact ih k2a (by omega) (hbodya j0) (hbcl _) (hbok _) h2 w
          · exact ⟨0, fun j hj => absurd ⟨j, hj⟩ hex⟩
        choose F hFspec using hF
        -- an outcome of positive weight of the second run is an outcome of the first
        have hFb : ∀ jb : Fin Kb, Vb.mass (cellsb jb) ≠ 0 →
            F (Vb.val (cellsb jb)) = srcMass (Wb jb) w := by
          intro jb hjb
          have hposb : 0 < srcMass Vb (Vb.val (cellsb jb)) :=
            ((hnnb _).lt_of_ne (Ne.symm hjb)).trans_le (le_massOf hnnb rfl)
          obtain ⟨i, hival, -⟩ := massOf_pos (hposb.trans_eq (hsc _).symm)
          obtain ⟨ja, rfl⟩ := hcompla i
          have h2 := hbodyb jb
          rw [← hival] at h2
          rw [hFspec _ ja hival]
          exact ih k2a (by omega) (hbodya ja) (hbcl _) (hbok _) h2 w
        rw [srcMass_wsum, srcMass_wsum]
        have hleft : (∑ ja, Va.mass (cellsa ja) * srcMass (Wa ja) w)
            = ∑ ja, Va.mass (cellsa ja) * F (Va.val (cellsa ja)) := by
          refine Finset.sum_congr rfl fun ja _ => ?_
          rw [← hFspec _ ja rfl]
        have hright : (∑ jb, Vb.mass (cellsb jb) * srcMass (Wb jb) w)
            = ∑ jb, Vb.mass (cellsb jb) * F (Vb.val (cellsb jb)) := by
          refine Finset.sum_congr rfl fun jb _ => ?_
          by_cases hm : Vb.mass (cellsb jb) = 0
          · rw [hm, zero_mul, zero_mul]
          · rw [hFb jb hm]
        rw [hleft, hright]
        refine sum_fiber_transfer (fun ja => Va.val (cellsa ja))
          (fun jb => Vb.val (cellsb jb)) (fun ja => Va.mass (cellsa ja))
          (fun jb => Vb.mass (cellsb jb)) F fun v => ?_
        exact ((massOf_comp_of_injective _ Va.val Va.mass hinja fun i _ => hcompla i).trans
          (hsc v)).trans
          (massOf_comp_of_injective _ Vb.val Vb.mass hinjb fun i _ => hcomplb i).symm


/-! ### The source measure pushed forward along a map

Lemma 65 compares the run of the normalized source with the run of the original
pushed forward along `anfV`. -/

/-- The probability `V` gives to the values whose image under `f` is `w`: the
weight (`massOf`) of the predicate `f · = w`. With `f = anfV` it is the
right-hand side of item 1 of Theorem 7. -/
noncomputable def sMassF (f : SPLC.Val → SPLC.Val) (V : DistVal) (w : SPLC.Val) : ℝ :=
  massOf (fun v => f v = w) V.val V.mass

/-- `sMassF f` of a Dirac distribution value `point v` at `w`: `1` if
`f v = w`, `0` otherwise. -/
theorem sMassF_point (f : SPLC.Val → SPLC.Val) (v w : SPLC.Val) :
    sMassF f (DistVal.point v) w = if f v = w then 1 else 0 :=
  massOf_fin_one _ _ _

/-- Scaling a distribution value by `a` scales `sMassF f` by `a`. -/
theorem sMassF_scale (f : SPLC.Val → SPLC.Val) (a : ℝ) (V : DistVal) (w : SPLC.Val) :
    sMassF f (V.scale a) w = a * sMassF f V w :=
  massOf_mul_left _ V.val a V.mass

/-- `sMassF f` of a concatenation is the sum of the two. -/
theorem sMassF_append (f : SPLC.Val → SPLC.Val) (V1 V2 : DistVal) (w : SPLC.Val) :
    sMassF f (V1.append V2) w = sMassF f V1 w + sMassF f V2 w :=
  massOf_append _ V1.val V2.val V1.mass V2.mass

/-- `sMassF f` of a weighted sum is the weighted sum. -/
theorem sMassF_wsum (f : SPLC.Val → SPLC.Val) {K : ℕ} (cells : Fin K → ℝ × DistVal)
    (w : SPLC.Val) :
    sMassF f (DistVal.wsum cells) w = ∑ j, (cells j).1 * sMassF f (cells j).2 w :=
  massOf_wsum _ cells

/-! ### Normalization preserves `ProbOkT` -/

mutual
/-- Normalization preserves `ProbOkV`. -/
theorem anfV_probOk : ∀ (v : SPLC.Val), ProbOkV v → ProbOkV (anfV v)
  | .var _, _ => trivial
  | .real _, _ => trivial
  | .bool _, _ => trivial
  | .lam _ m, h => anfT_probOk m h
/-- Normalization preserves `ProbOkT`. -/
theorem anfT_probOk : ∀ (m : SPLC.Tm), ProbOkT m → ProbOkT (anfT m)
  | .val v, h => anfV_probOk v h
  | .app v u, h =>
      ⟨anfV_probOk u h.2, probOkV_rename (anfV v) 0 (anfV_probOk v h.1),
       trivial, trivial⟩
  | .letin m b, h => ⟨anfT_probOk m h.1, anfT_probOk b h.2⟩
  | .choice _ m1 m2, h => ⟨h.1, anfT_probOk m1 h.2.1, anfT_probOk m2 h.2.2⟩
  | .ascT m _, h => anfT_probOk m h
  | .ascV v _, h => anfV_probOk v h
  | .ite v m1 m2, h =>
      ⟨anfV_probOk v h.1, trivial,
       probOkT_rename (anfT m1) 0 (anfT_probOk m1 h.2.1),
       probOkT_rename (anfT m2) 0 (anfT_probOk m2 h.2.2)⟩
  | .add v u, h =>
      ⟨anfV_probOk v h.1, probOkV_rename (anfV u) 0 (anfV_probOk u h.2),
       trivial, trivial⟩
end

/-- A `let` of the elaboration, with a Dirac bound term: binding a value and
continuing changes neither the measure nor the values of the result. -/
theorem red_let_point {v : SPLC.Val} {n : SPLC.Tm} {k : ℕ} {W : DistVal}
    (h : SPLC.Red (n.subst0 v) k W) :
    ∃ k' W', SPLC.Red (.letin (.ascV v .unk) n) k' W' ∧
      (∀ w, srcMass W' w = srcMass W w) ∧ (∀ i, ∃ j, W'.val i = W.val j) := by
  refine ⟨1 + k + 1, _, SPLC.Red.slet (V := DistVal.point v) (K := 1)
    (cells := fun _ => (0 : Fin 1)) (W := fun _ => W)
    (SPLC.Red.sascV (k := 0))
    (fun a b _ => by
      have ha : (a : ℕ) < 1 := a.isLt
      have hb : (b : ℕ) < 1 := b.isLt
      exact Fin.ext (by omega))
    (fun i => ⟨0, by
      have hi : (i : ℕ) < 1 := i.isLt
      exact Fin.ext (by omega)⟩)
    (fun _ => h), ?_, ?_⟩
  · intro w
    rw [srcMass_wsum]
    show (∑ _j : Fin 1, (1:ℝ) * srcMass W w) = _
    rw [Fin.sum_univ_one, one_mul]
  · intro i
    obtain ⟨_, x, hx⟩ := wsum_val_decomp
      (fun _ : Fin 1 => (DistVal.point v).mass (0 : Fin 1)) (fun _ => W) i
    exact ⟨x, hx⟩


/-- Lemma 65 (normalization preserves the measure), strong form: the normalized
source runs to the same measure, and every outcome of its run is the
normalization of an outcome of the original run, whatever its probability. The
second part gives the exhaustive `let` rule of SPLC a body reduction at every
outcome of the normalized bound term, including those of probability zero. -/
theorem red_anf' : ∀ (k : ℕ) {m : SPLC.Tm} {V : DistVal}, SPLC.Red m k V →
    m.FvBelow 0 → ProbOkT m →
    ∃ k' V', SPLC.Red (anfT m) k' V' ∧ (∀ w, srcMass V' w = sMassF anfV V w) ∧
      (∀ i, ∃ j, V'.val i = anfV (V.val j)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m V hs hcl hok
    cases hs with
    | sv => exact ⟨1, _, SPLC.Red.sv, fun w => by rw [srcMass_point, sMassF_point],
        fun i => ⟨i, rfl⟩⟩
    | sascV => exact ⟨1, _, SPLC.Red.sascV,
        fun w => by rw [srcMass_point, sMassF_point], fun i => ⟨i, rfl⟩⟩
    | sascT h =>
      obtain ⟨k', V', hr, hm, hc⟩ := ih _ (by omega) h hcl hok
      exact ⟨k' + 1, V', SPLC.Red.sascT hr, hm, hc⟩
    | @schoice p m1 m2 k1 k2 V1 V2 h1 h2 =>
      obtain ⟨k1', V1', hr1, hm1, hc1⟩ := ih _ (by omega) h1 hcl.1 hok.2.1
      obtain ⟨k2', V2', hr2, hm2, hc2⟩ := ih _ (by omega) h2 hcl.2 hok.2.2
      refine ⟨k1' + k2' + 1, _, SPLC.Red.schoice hr1 hr2, fun w => ?_, ?_⟩
      · rw [srcMass_append, srcMass_scale, srcMass_scale,
          sMassF_append, sMassF_scale, sMassF_scale, hm1, hm2]
      · refine distVal_append_val
          (P := fun x => ∃ j, x = anfV (((V1.scale p).append (V2.scale (1 - p))).val j))
          ?_ ?_
        · intro i
          obtain ⟨j, hj⟩ := hc1 i
          refine ⟨Fin.castAdd V2.n j, ?_⟩
          show V1'.val i = anfV (Fin.append (V1.scale p).val (V2.scale (1 - p)).val
            (Fin.castAdd _ j))
          rw [Fin.append_left]
          exact hj
        · intro i
          obtain ⟨j, hj⟩ := hc2 i
          refine ⟨Fin.natAdd V1.n j, ?_⟩
          show V2'.val i = anfV (Fin.append (V1.scale p).val (V2.scale (1 - p)).val
            (Fin.natAdd _ j))
          rw [Fin.append_right]
          exact hj
    | @sit m1 m2 k0 V0 h =>
      obtain ⟨k', V', hr, hm, hc⟩ := ih _ (by omega) h hcl.2.1 hok.2.1
      have hbody : SPLC.Red ((SPLC.Tm.ite (.var 0) ((anfT m1).rename 0)
          ((anfT m2).rename 0)).subst0 (.bool true)) (k' + 1) V' := by
        show SPLC.Red (SPLC.Tm.ite ((SPLC.Val.var 0).subst 0 (.bool true))
          (((anfT m1).rename 0).subst 0 (.bool true))
          (((anfT m2).rename 0).subst 0 (.bool true))) (k' + 1) V'
        rw [SPLC.Tm.subst_rename_cancel (anfT m1) 0 (.bool true),
          SPLC.Tm.subst_rename_cancel (anfT m2) 0 (.bool true)]
        exact SPLC.Red.sit hr
      obtain ⟨kk, WW, hrr, hmm, hcc⟩ := red_let_point hbody
      exact ⟨kk, WW, hrr, fun w => by rw [hmm w, hm w], fun i => by
        obtain ⟨j, hj⟩ := hcc i
        obtain ⟨j', hj'⟩ := hc j
        exact ⟨j', hj.trans hj'⟩⟩
    | @sif m1 m2 k0 V0 h =>
      obtain ⟨k', V', hr, hm, hc⟩ := ih _ (by omega) h hcl.2.2 hok.2.2
      have hbody : SPLC.Red ((SPLC.Tm.ite (.var 0) ((anfT m1).rename 0)
          ((anfT m2).rename 0)).subst0 (.bool false)) (k' + 1) V' := by
        show SPLC.Red (SPLC.Tm.ite ((SPLC.Val.var 0).subst 0 (.bool false))
          (((anfT m1).rename 0).subst 0 (.bool false))
          (((anfT m2).rename 0).subst 0 (.bool false))) (k' + 1) V'
        rw [SPLC.Tm.subst_rename_cancel (anfT m1) 0 (.bool false),
          SPLC.Tm.subst_rename_cancel (anfT m2) 0 (.bool false)]
        exact SPLC.Red.sif hr
      obtain ⟨kk, WW, hrr, hmm, hcc⟩ := red_let_point hbody
      exact ⟨kk, WW, hrr, fun w => by rw [hmm w, hm w], fun i => by
        obtain ⟨j, hj⟩ := hcc i
        obtain ⟨j', hj'⟩ := hc j
        exact ⟨j', hj.trans hj'⟩⟩
    | @sadd r1 r2 k0 =>
      have hin : SPLC.Red ((SPLC.Tm.add (.real r1) (.var 0)).subst0 (.real r2)) (k0 + 1)
          (DistVal.point (.real (r1 + r2))) := by
        simp only [SPLC.Tm.subst0, SPLC.Tm.subst, SPLC.Val.subst]
        exact SPLC.Red.sadd
      obtain ⟨k2, W2, hr2, hm2, hc2⟩ := red_let_point hin
      obtain ⟨k3, W3, hr3, hm3, hc3⟩ := red_let_point (v := .real r1)
        (n := .letin (.ascV ((anfV (.real r2)).rename 0) .unk)
          (.add (.var 1) (.var 0))) hr2
      refine ⟨k3, W3, hr3, fun w => by
        rw [hm3 w, hm2 w, srcMass_point, sMassF_point]
        rfl, fun i => ⟨(0 : Fin 1), ?_⟩⟩
      obtain ⟨j, hj⟩ := hc3 i
      obtain ⟨j', hj'⟩ := hc2 j
      rw [hj, hj']
      rfl
    | @sapp τ mb u k0 V0 h =>
      obtain ⟨k', V', hr, hm, hc⟩ := ih _ (by omega) h
        (SPLC.Tm.subst_pres_below hcl.1 hcl.2 (le_refl 0))
        (probOkT_subst _ 0 _ hok.1 hok.2)
      have hucl : (anfV u).FvBelow 0 := anfV_fvBelow u 0 hcl.2
      rw [anfT_subst mb 0 u hcl.2] at hr
      have hin : SPLC.Red ((SPLC.Tm.app (.var 0) (anfV u)).subst0 (anfV (.lam τ mb)))
          (k' + 1) V' := by
        show SPLC.Red (SPLC.Tm.app (.lam .unk (anfT mb))
          ((anfV u).subst 0 (anfV (.lam τ mb)))) (k' + 1) V'
        rw [SPLC.Val.subst_below hucl (Nat.zero_le 0)]
        exact SPLC.Red.sapp hr
      obtain ⟨k2, W2, hr2, hm2, hc2⟩ := red_let_point hin
      have hout : SPLC.Red ((SPLC.Tm.letin (.ascV ((anfV (.lam τ mb)).rename 0) .unk)
          (.app (.var 0) (.var 1))).subst0 (anfV u)) k2 W2 := by
        show SPLC.Red (SPLC.Tm.letin
          (.ascV (((anfV (.lam τ mb)).rename 0).subst 0 (anfV u)) .unk)
          (.app ((SPLC.Val.var 0).subst 1 ((anfV u).rename 0))
            ((SPLC.Val.var 1).subst 1 ((anfV u).rename 0)))) k2 W2
        rw [SPLC.Val.subst_rename_cancel, SPLC.Val.rename_below hucl (Nat.zero_le 0)]
        exact hr2
      obtain ⟨k3, W3, hr3, hm3, hc3⟩ := red_let_point hout
      exact ⟨k3, W3, hr3, fun w => by rw [hm3 w, hm2 w, hm w], fun i => by
        obtain ⟨j, hj⟩ := hc3 i
        obtain ⟨j', hj'⟩ := hc2 j
        obtain ⟨j'', hj''⟩ := hc j'
        exact ⟨j'', (hj.trans hj').trans hj''⟩⟩
    | @slet m0 bb ka k2a V0 K cells Ws hs0 hinj hcompl hsbody =>
      obtain ⟨ka', V0', hr0', hm0', hc0'⟩ := ih ka (by omega) hs0 hcl.1 hok.1
      have hcl0' : ∀ i, (V0'.val i).FvBelow 0 :=
        red_closed _ hr0' (anfT_fvBelow m0 0 hcl.1)
      have hok0' := red_probOk _ hr0' (anfT_probOk m0 hok.1)
      have hclb : ∀ v : SPLC.Val, v.FvBelow 0 → ((anfT bb).subst0 v).FvBelow 0 :=
        fun v hv => SPLC.Tm.subst_pres_below (anfT_fvBelow bb 1 hcl.2) hv (le_refl 0)
      have hokb : ∀ v : SPLC.Val, ProbOkV v → ProbOkT ((anfT bb).subst0 v) :=
        fun v hv => probOkT_subst _ 0 _ (anfT_probOk bb hok.2) hv
      have hcla := red_closed _ hs0 hcl.1
      have hva := (red_probOk _ hs0 hok.1).2
      have hsbcl : ∀ jj : Fin K, (bb.subst0 (V0.val (cells jj))).FvBelow 0 :=
        fun jj => SPLC.Tm.subst_pres_below hcl.2 (hcla _) (le_refl 0)
      have hsbok : ∀ jj : Fin K, ProbOkT (bb.subst0 (V0.val (cells jj))) :=
        fun jj => probOkT_subst _ 0 _ hok.2 (hva _)
      -- the source partner of every outcome of the normalized bound term: the
      -- value coverage of the induction hypothesis, plus the surjectivity of the
      -- source enumeration `cells`
      have hpartner : ∀ i : Fin V0'.n, ∃ jj : Fin K,
          anfV (V0.val (cells jj)) = V0'.val i := by
        intro i
        obtain ⟨j0, hj0⟩ := hc0' i
        obtain ⟨jj, hjj⟩ := hcompl j0
        exact ⟨jj, by rw [hjj, hj0]⟩
      choose jsrc hjsrcval using hpartner
      have hb : ∀ i : Fin V0'.n, ∃ (kk : ℕ) (Wv : DistVal),
          SPLC.Red ((anfT bb).subst0 (V0'.val i)) kk Wv ∧
          ∀ x, ∃ y, Wv.val x = anfV ((Ws (jsrc i)).val y) := by
        intro i
        obtain ⟨kk, Wv, hd, _, hcv⟩ := ih k2a (by omega) (hsbody (jsrc i))
          (hsbcl _) (hsbok _)
        rw [anfT_subst bb 0 _ (hcla _), hjsrcval i] at hd
        exact ⟨kk, Wv, hd, hcv⟩
      choose kb Wb hbd hbcov using hb
      have hFex : ∀ (w : SPLC.Val) (v : SPLC.Val), ∃ r : ℝ, ∀ (kk : ℕ) (Wv : DistVal),
          v.FvBelow 0 → ProbOkV v → SPLC.Red ((anfT bb).subst0 v) kk Wv →
          srcMass Wv w = r := by
        intro w v
        by_cases hex : ∃ (kk : ℕ) (Wv : DistVal), SPLC.Red ((anfT bb).subst0 v) kk Wv
        · obtain ⟨kk0, Wv0, hd0⟩ := hex
          exact ⟨srcMass Wv0 w, fun kk Wv hv hv2 hd =>
            red_srcMass_det kk hd (hclb v hv) (hokb v hv2) hd0 w⟩
        · exact ⟨0, fun kk Wv _ _ hd => absurd ⟨kk, Wv, hd⟩ hex⟩
      choose F hFspec using hFex
      refine ⟨ka' + (Finset.univ.sup kb) + 1, _,
        SPLC.Red.slet (V := V0') (K := V0'.n) (cells := fun i => i) (W := Wb)
          hr0' (fun _ _ h => h) (fun i => ⟨i, rfl⟩)
          (fun j => SPLC.red_index_mono (hbd j) (Finset.le_sup (Finset.mem_univ j))),
        fun w => ?_, ?_⟩
      · rw [srcMass_wsum, sMassF_wsum]
        have hL : ∀ j : Fin V0'.n,
            V0'.mass j * srcMass (Wb j) w = V0'.mass j * F w (V0'.val j) := by
          intro j
          rw [hFspec w _ (kb j) (Wb j) (hcl0' _) (hok0'.2 _) (hbd j)]
        have hR : ∀ jj : Fin K,
            V0.mass (cells jj) * sMassF anfV (Ws jj) w
            = V0.mass (cells jj) * F w (anfV (V0.val (cells jj))) := by
          intro jj
          obtain ⟨kk, Wv, hd, hmm, -⟩ := ih k2a (by omega) (hsbody jj)
            (hsbcl _) (hsbok _)
          rw [anfT_subst bb 0 _ (hcla _)] at hd
          rw [← hmm w, hFspec w _ kk Wv (anfV_fvBelow _ 0 (hcla _))
            (anfV_probOk _ (hva _)) hd]
        rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hL j),
          Finset.sum_congr rfl (fun jj (_ : jj ∈ Finset.univ) => hR jj)]
        refine sum_fiber_transfer (fun j : Fin V0'.n => V0'.val j)
          (fun jj : Fin K => anfV (V0.val (cells jj)))
          (fun j : Fin V0'.n => V0'.mass j)
          (fun jj : Fin K => V0.mass (cells jj)) (F w) ?_
        intro v
        exact (hm0' v).trans
          (massOf_comp_of_injective _ V0.val V0.mass hinj fun i _ => hcompl i).symm
      · intro x
        obtain ⟨j, y, hxy⟩ := wsum_val_decomp (fun j => V0'.mass j) Wb x
        obtain ⟨y', hy'⟩ := hbcov j y
        obtain ⟨z, hz⟩ := wsum_val_mem (fun jj => V0.mass (cells jj)) Ws (jsrc j) y'
        exact ⟨z, by rw [hxy, hy', hz]⟩

/-- Lemma 65 (normalization preserves the measure): if a closed SPLC term `m`
satisfying `ProbOkT` runs to `V`, then `anfT m` runs to some `V'` that gives
each value `w` the probability `V` gives to the outcomes whose normalization is
`w`. -/
theorem red_anf (k : ℕ) {m : SPLC.Tm} {V : DistVal} (hs : m ⇓ₛ[k] V)
    (hcl : m.FvBelow 0) (hok : ProbOkT m) :
    ∃ k' V', anfT m ⇓ₛ[k'] V' ∧ ∀ w, srcMass V' w = sMassF anfV V w := by
  obtain ⟨k', V', hr, hm, -⟩ := red_anf' k hs hcl hok
  exact ⟨k', V', hr, hm⟩


/-! ## Theorem 7 over `RedSt`

The statement assumes that both runs exist. `ProbOkT m` is the grammar's
`[0,1]` condition on the probabilities of the program, and `m.FvBelow 0` says
that the program is closed. -/

/-- Item 1 of Theorem 7 for a target run in `RedSt`: the erased measure of the
target result is the source measure pushed forward along `anfV`. -/
theorem erasure_simulation {m : SPLC.Tm} {ks : ℕ} {Vs : DistVal} {tm : Tm} {D : FDist}
    {k : ℕ} {V : DConf}
    (hcl : m.FvBelow 0) (hok : ProbOkT m)
    (helab : ElabT [] (embedT m) tm D)
    (hsrc : SPLC.Red m ks Vs) (htgt : RedSt tm k V) :
    ∀ q, V.C q → ∀ w, erMass V q w = sMassF anfV Vs w := by
  have hΓ : CtxGood ([] : List FTy) := ctxGood_nil
  have her : ErTm tm (anfT m) := elab_erTm m helab hΓ
  obtain ⟨k', Vs', hr', hm'⟩ := red_anf ks hsrc hcl hok
  intro q hq w
  rw [erasure_meas k htgt her hr' q hq w, hm' w]

/-- Normalization leaves real numbers alone. -/
theorem anfV_eq_real : ∀ (v : SPLC.Val) (r : ℝ), anfV v = .real r ↔ v = .real r
  | .var _, _ => by simp [anfV]
  | .real _, _ => by simp [anfV]
  | .bool _, _ => by simp [anfV]
  | .lam _ _, _ => by simp [anfV]

/-- Normalization leaves booleans alone. -/
theorem anfV_eq_bool : ∀ (v : SPLC.Val) (b : Bool), anfV v = .bool b ↔ v = .bool b
  | .var _, _ => by simp [anfV]
  | .real _, _ => by simp [anfV]
  | .bool _, _ => by simp [anfV]
  | .lam _ _, _ => by simp [anfV]

/-- Item 2 of Theorem 7 for a target run in `RedSt`: on reals and booleans the
erased measure equals the source measure. -/
theorem erasure_simulation_obs {m : SPLC.Tm} {ks : ℕ} {Vs : DistVal} {tm : Tm} {D : FDist}
    {k : ℕ} {V : DConf}
    (hcl : m.FvBelow 0) (hok : ProbOkT m)
    (helab : ElabT [] (embedT m) tm D)
    (hsrc : SPLC.Red m ks Vs) (htgt : RedSt tm k V) :
    ∀ q, V.C q → (∀ r : ℝ, erMass V q (.real r) = srcMass Vs (.real r)) ∧
      (∀ b : Bool, erMass V q (.bool b) = srcMass Vs (.bool b)) := by
  intro q hq
  constructor
  · intro r
    rw [erasure_simulation hcl hok helab hsrc htgt q hq (.real r)]
    exact massOf_congr fun i => anfV_eq_real _ r
  · intro b
    rw [erasure_simulation hcl hok helab hsrc htgt q hq (.bool b)]
    exact massOf_congr fun i => anfV_eq_bool _ b


/-! ## No failure (Lemma 62): the composition lemmas

Two evidences below the same annotation, when that annotation weakly realizes a
static type, always compose. This is `red_ascV_static_ok` with the equality of
static types collapsed to reflexivity, and it is the form the obligation takes
at every composition site: the evidence of the value and the evidence of the
coercion both lie below the value's annotation. -/

/-- Lemma 62 (no failure), simple level: two good evidences more precise than
the same annotation `σ`, which weakly realizes a static type, compose, and the
value ascription fires its success case. -/
theorem red_ascV_below_ok {ε1 ε2 : TagTy} {u : Raw} {σ σ' : FTy} {τ : Ty}
    (hg1 : GoodTy ε1.toF) (hg2 : GoodTy ε2.toF)
    (hp1 : ε1.toF ⊑̇ σ) (hp2 : ε2.toF ⊑̇ σ)
    (hst : σ ⇝ʷ τ) (hτ : IsStaticTy τ) :
    ∃ ε3, ε1 ∘ ε2 = some ε3 ∧
      .ascV ε2 (.asc ε1 u σ) σ' ⇓[1] DConf.point (.asc ε3 u σ') ∧
      ε3.toF ⇝ʷ τ ∧ GoodTy ε3.toF :=
  red_ascV_static_ok hg1 hg2 (weakRealizesTy_of_prec hg1 hp1 hst)
    (weakRealizesTy_of_prec hg2 hp2 hst) (EqTy.refl hτ)

/-- Lemma 62 (no failure), simple level, negative form: the premise of
`dascErr` does not hold. -/
theorem not_dascErr_below {ε1 ε2 : TagTy} {σ : FTy} {τ : Ty}
    (hg1 : GoodTy ε1.toF) (hg2 : GoodTy ε2.toF)
    (hp1 : ε1.toF ⊑̇ σ) (hp2 : ε2.toF ⊑̇ σ)
    (hst : σ ⇝ʷ τ) (hτ : IsStaticTy τ) :
    ∃ ε3, ε1 ∘ ε2 = some ε3 ∧ GoodTy ε3.toF := by
  obtain ⟨ε3, hm, _, _, hg⟩ :=
    red_ascV_below_ok (u := .real 0) (σ' := σ) hg1 hg2 hp1 hp2 hst hτ
  exact ⟨ε3, hm, hg⟩

/-- Lemma 62 (no failure), distribution level: two good formula types more
precise than the same type `μ`, which weakly realizes a static type, are
consistent. -/
theorem econsD_below {D1 D2 μ : FDist} {T : DTy}
    (hg1 : GoodD D1) (hg2 : GoodD D2) (hp1 : D1 ⊑̇ μ) (hp2 : D2 ⊑̇ μ)
    (hst : μ ⇝ʷ T) (hT : IsStaticDTy T) : D1 ∼̇ D2 :=
  econs_of_weakRealizes_d (weakRealizesD_of_prec hg1 hp1 hst) (EqD.refl hT)
    (weakRealizesD_of_prec hg2 hp2 hst)

/-- Lemma 62 (no failure), rule (D::μ): the routing formula is satisfiable
when the initial reordering and the ascription evidence are both more precise
than the ascribed term's type, which weakly realizes a static type. This rules out
`dascDErr`. -/
theorem routing_sat_below {V : DConf} {μ : FDist} {εd : TagD} {T : DTy}
    (hgr : GoodD (V.confF ∥ μ)) (hgd : GoodD εd.toF)
    (hp1 : V.confF ∥ μ ⊑̇ μ) (hp2 : εd.toF ⊑̇ μ)
    (hst : μ ⇝ʷ T) (hT : IsStaticDTy T) :
    ∃ w, ((V.confF ∥ᵗ μ) ∘ εd).toF.C w := by
  have h := meetD_sat_iff_econsD.mpr (econsD_below hgr hgd hp1 hp2 hst hT)
  rw [routing_toF]
  exact h

/-! ### The entries of (Dlet) coerce between syntactically equal types

The entries of the initial reordering pair entries with syntactically equal
types, so an entry of (Dlet) coerces a value to the type it already has and its
annotation does not change. Of the two routed rules, only (D::μ) changes
annotations, and its target type is written in the term. -/

/-- `reorderD_cell_eq` over the tagged carrier of rule (Dlet): the type of the
value and the target type of its coercion coincide. -/
theorem dlet_cell_ty_eq (D1 D2 : FDist) (c : Fin (tagReorderD D1 D2).n) :
    D1.ty (reorderDL D1 D2 c) = D2.ty (reorderDR D1 D2 c) :=
  reorderD_cell_eq D1 D2 c

/-! ### Annotations that realize static types

`SAnnTy σ` is the premise "`σ` realizes some static type" of Definition 16. -/

/-- A formula simple type realizes some static type (Definition 7). Full
realization, with coverage, is used, so that every entry of a realizing
distribution type realizes (`sAnnD_entries`). -/
def SAnnTy (σ : FTy) : Prop := ∃ τ : Ty, RealizesTy σ τ ∧ IsStaticTy τ

/-- A formula distribution type realizes some static distribution type. -/
def SAnnD (D : FDist) : Prop := ∃ T : DTy, RealizesD D T ∧ IsStaticDTy T

/-- `Real` realizes a static type. -/
@[simp] theorem sAnnTy_real : SAnnTy .real := ⟨.real, .real, .real⟩
/-- `Bool` realizes a static type. -/
@[simp] theorem sAnnTy_bool : SAnnTy .bool := ⟨.bool, .bool, .bool⟩

/-- A realizing type weakly realizes the same static type. -/
theorem sAnnTy_weakRealizes {σ : FTy} : SAnnTy σ → ∃ τ, WeakRealizesTy σ τ ∧ IsStaticTy τ
  | ⟨τ, h, hs⟩ => ⟨τ, weakRealizesTy_of_realizes h, hs⟩

/-- The lifting of a static simple type realizes it. -/
theorem sAnnTy_lift {τ : Ty} (hs : IsStaticTy τ) (hw : GPLC.WfTy τ) :
    SAnnTy (liftFTy τ) :=
  ⟨τ, realizesTy_lift hs hw, hs⟩

/-- Every entry of a realizing distribution type realizes: the left coverage
clause of `RealizesD` gives each entry its partner. -/
theorem sAnnD_entries : ∀ {D : FDist}, SAnnD D → ∀ i, SAnnTy (D.ty i)
  | _, ⟨.dist _, .dist R hR hcovL _ _ _, .dist hst _⟩, i => by
      obtain ⟨j, hj⟩ := hcovL i
      exact ⟨_, hR i j hj, hst _ (List.get_mem _ _)⟩

/-- The codomain of a realizing arrow realizes. -/
theorem sAnnTy_cod : ∀ {σ : FTy} {D : FDist}, SAnnTy (.arrow σ D) → SAnnD D
  | _, _, ⟨.arrow _ T, .arrow _ hd, .arrow _ hT⟩ => ⟨T, hd, hT⟩

/-- The lifting of a static distribution type realizes it. -/
theorem sAnnD_lift {T : DTy} (hs : IsStaticDTy T) (hw : GPLC.WfDTy T) :
    SAnnD (liftFDist T) :=
  ⟨T, realizesD_lift hs hw, hs⟩


/-! ## Realizing types (Definition 16)

The premise of `dascDErr` reads the type of the ascribed term, which is not written
in the term, so the annotations alone do not suffice. The type the TPLC typing
infers does not realize in general: the conditional infers the convex hull
`chooseSemU D1 D2` of its branch types, which realizes a static type only when
the branches are `=ₛ`, and the TPLC typing does not require it. `SRT` mirrors
the typing judgment and asks for realization as a premise exactly where the
type is not determined by those of the subterms. -/

mutual
/-- Definition 16 (realizing types), values: `Γ ⊢⇝ tv : σ`. -/
inductive SRV : List FTy → Val → FTy → Prop where
  | var    : ∀ {Γ x σ}, Γ[x]? = some σ → SAnnTy σ → SRV Γ (.var x) σ
  | ascRaw : ∀ {Γ} {ε : TagTy} {u σu σ}, SRRaw Γ u σu → SAnnTy σ →
               SRV Γ (.asc ε u σ) σ
  | err    : ∀ {Γ σ}, SAnnTy σ → SRV Γ (.err σ) σ
/-- Definition 16 (realizing types), raw values. -/
inductive SRRaw : List FTy → Raw → FTy → Prop where
  | real : ∀ {Γ r}, SRRaw Γ (.real r) .real
  | bool : ∀ {Γ b}, SRRaw Γ (.bool b) .bool
  | lam  : ∀ {Γ σ m D}, SRT (σ :: Γ) m D → SAnnTy σ →
             SRRaw Γ (.lam σ m) (.arrow σ D)
/-- Definition 16 (realizing types), terms: `Γ ⊢⇝ tm : D`. The rules for
`let`, both choices and the conditional ask for the realization of the result
type. -/
inductive SRT : List FTy → Tm → FDist → Prop where
  | val    : ∀ {Γ v σ}, SRV Γ v σ → SRT Γ (.val v) (pointF σ)
  | app    : ∀ {Γ v w σ D}, SRV Γ v (.arrow σ D) → SRV Γ w σ →
               SRT Γ (.app v w) D
  | letin  : ∀ {Γ m n} {ty : Fin n → FTy} {C : (Fin n → ℝ) → Prop}
               {ns : Fin n → Tm} {F : Fin n → FDist},
               SRT Γ m ⟨n, ty, C⟩ → (∀ i, SRT (ty i :: Γ) (ns i) (F i)) →
               SAnnD (letSem ⟨n, ty, C⟩ F) →
               SRT Γ (.letin m n ns) (letSem ⟨n, ty, C⟩ F)
  | choice : ∀ {Γ m n D1 D2} {a : ℝ}, SRT Γ m D1 → SRT Γ n D2 →
               SAnnD (chooseSem a D1 D2) →
               SRT Γ (.choice (.q a) m n) (chooseSem a D1 D2)
  | choiceU : ∀ {Γ m n D1 D2}, SRT Γ m D1 → SRT Γ n D2 →
               SAnnD (chooseSemU D1 D2) →
               SRT Γ (.choice .unk m n) (chooseSemU D1 D2)
  | ascT   : ∀ {Γ} {ε : TagD} {m D Db}, SRT Γ m D → SAnnD Db →
               SRT Γ (.ascT ε m Db) Db
  | ascV   : ∀ {Γ} {ε : TagTy} {v σ σ'}, SRV Γ v σ → SAnnTy σ' →
               SRT Γ (.ascV ε v σ') (pointF σ')
  | ite    : ∀ {Γ v m n D1 D2}, SRV Γ v .bool → SRT Γ m D1 → SRT Γ n D2 →
               SAnnD (chooseSemU D1 D2) →
               SRT Γ (.ite v m n) (chooseSemU D1 D2)
  | add    : ∀ {Γ v w}, SRV Γ v .real → SRV Γ w .real →
               SRT Γ (.add v w) (pointF .real)
  | errD   : ∀ {Γ D}, SAnnD D → SRT Γ (.errD D) D
end

/-- `Γ ⊢⇝ u : σ`, the raw value `u` has the type `σ`, which realizes a static
type (Definition 16), the article's `Γ ⊢_⇝ u : σ`. -/
scoped notation:50 (name := sRRawStx) Γ:51 " ⊢⇝ " u:51 " : " σ:51 => SRRaw Γ u σ
/-- `Γ ⊢⇝ v : σ`, the value `v` has the type `σ`, which realizes a static type
(Definition 16). -/
scoped notation:50 (name := sRVStx) Γ:51 " ⊢⇝ " v:51 " : " σ:51 => SRV Γ v σ
/-- `Γ ⊢⇝ m : D`, the term `m` has the type `D`, which realizes a static type
(Definition 16). -/
scoped notation:50 (name := sRTStx) Γ:51 " ⊢⇝ " m:51 " : " D:51 => SRT Γ m D
/-- `⊢⇝ v : σ`, the closed form of `Γ ⊢⇝ v : σ`. -/
scoped notation:50 (name := sRVClosedStx) "⊢⇝ " v:51 " : " σ:51 => SRV [] v σ
/-- `⊢⇝ m : D`, the closed form of `Γ ⊢⇝ m : D`. -/
scoped notation:50 (name := sRTClosedStx) "⊢⇝ " m:51 " : " D:51 => SRT [] m D

/-- A Dirac on a realizing type realizes. -/
theorem sAnnD_point {σ : FTy} : SAnnTy σ → SAnnD (pointF σ)
  | ⟨τ, h, hs⟩ => ⟨.dist [(τ, .q 1)], realizes_point h hs,
      IsStaticDTy.point hs⟩

/-- An arrow whose domain and codomain realize, realizes. -/
theorem sAnnTy_arrow {σ : FTy} {D : FDist} : SAnnTy σ → SAnnD D →
    SAnnTy (.arrow σ D)
  | ⟨τ, h, hs⟩, ⟨T, hd, hT⟩ => ⟨.arrow τ T, .arrow h hd, .arrow hs hT⟩

mutual
/-- The type of a value in the realizing-types judgment realizes a static type. -/
theorem srV_sAnnTy : ∀ {Γ : List FTy} {v : Val} {σ : FTy}, SRV Γ v σ → SAnnTy σ
  | _, _, _, .var _ h => h
  | _, _, _, .ascRaw _ h => h
  | _, _, _, .err h => h
/-- The type of a term in `SRT` realizes a static type. -/
theorem srT_sAnnD : ∀ {Γ : List FTy} {m : Tm} {D : FDist}, SRT Γ m D → SAnnD D
  | _, _, _, .val hv => sAnnD_point (srV_sAnnTy hv)
  | _, _, _, .app hv _ => sAnnTy_cod (srV_sAnnTy hv)
  | _, _, _, .letin _ _ h => h
  | _, _, _, .choice _ _ h => h
  | _, _, _, .choiceU _ _ h => h
  | _, _, _, .ascT _ h => h
  | _, _, _, .ascV _ h => sAnnD_point h
  | _, _, _, .ite _ _ _ h => h
  | _, _, _, .add _ _ => sAnnD_point sAnnTy_real
  | _, _, _, .errD h => h
end

/-! ### `SRT` is stable under weakening and substitution

The context is read only at variables, so both proofs are structural; the
realization premises concern types, which substitution does not change. -/

mutual
/-- Weakening by append for the realizing-types judgment (values). -/
theorem srV_wkapp : ∀ {Γ : List FTy} {v : Val} {σ : FTy}, SRV Γ v σ →
    ∀ Γ', SRV (Γ ++ Γ') v σ
  | Γ0, _, _, @SRV.var _ x _ hx hσ, Γ' => by
      refine .var ?_ hσ
      have hlt : x < Γ0.length := by
        by_contra hge
        rw [List.getElem?_eq_none (by omega)] at hx
        exact absurd hx (by simp)
      rw [List.getElem?_append, if_pos hlt]
      exact hx
  | _, _, _, .ascRaw hu hσ, Γ' => .ascRaw (srRaw_wkapp hu Γ') hσ
  | _, _, _, .err hσ, _ => .err hσ
/-- Weakening by append for the realizing-types judgment (raw values). -/
theorem srRaw_wkapp : ∀ {Γ : List FTy} {u : Raw} {σ : FTy}, SRRaw Γ u σ →
    ∀ Γ', SRRaw (Γ ++ Γ') u σ
  | _, _, _, .real, _ => .real
  | _, _, _, .bool, _ => .bool
  | _, _, _, .lam hm hσ, Γ' => .lam (srT_wkapp hm Γ') hσ
/-- Weakening by append for the realizing-types judgment (terms). -/
theorem srT_wkapp : ∀ {Γ : List FTy} {m : Tm} {D : FDist}, SRT Γ m D →
    ∀ Γ', SRT (Γ ++ Γ') m D
  | _, _, _, .val hv, Γ' => .val (srV_wkapp hv Γ')
  | _, _, _, .app hv hw, Γ' => .app (srV_wkapp hv Γ') (srV_wkapp hw Γ')
  | _, _, _, .letin hm hbody hg, Γ' =>
      .letin (srT_wkapp hm Γ') (fun i => srT_wkapp (hbody i) Γ') hg
  | _, _, _, .choice h1 h2 hg, Γ' =>
      .choice (srT_wkapp h1 Γ') (srT_wkapp h2 Γ') hg
  | _, _, _, .choiceU h1 h2 hg, Γ' =>
      .choiceU (srT_wkapp h1 Γ') (srT_wkapp h2 Γ') hg
  | _, _, _, .ascT hm hg, Γ' => .ascT (srT_wkapp hm Γ') hg
  | _, _, _, .ascV hv hg, Γ' => .ascV (srV_wkapp hv Γ') hg
  | _, _, _, .ite hv h1 h2 hg, Γ' =>
      .ite (srV_wkapp hv Γ') (srT_wkapp h1 Γ') (srT_wkapp h2 Γ') hg
  | _, _, _, .add hv hw, Γ' => .add (srV_wkapp hv Γ') (srV_wkapp hw Γ')
  | _, _, _, .errD hg, _ => .errD hg
end

mutual
/-- A value with `Γ ⊢⇝ v : σ` has its free variables below the length of `Γ`. -/
theorem srV_fvBelow : ∀ {Γ : List FTy} {v : Val} {σ : FTy}, SRV Γ v σ →
    v.FvBelow Γ.length
  | Γ0, _, _, @SRV.var _ x _ hx _ => by
      show x < Γ0.length
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hx
      exact absurd hx (by simp)
  | _, _, _, .ascRaw hu _ => by
      simp only [Val.FvBelow]; exact srRaw_fvBelow hu
  | _, _, _, .err _ => trivial
/-- A raw value with a realizing typing in `Γ` has its free variables below the
length of `Γ`. -/
theorem srRaw_fvBelow : ∀ {Γ : List FTy} {u : Raw} {σ : FTy}, SRRaw Γ u σ →
    u.FvBelow Γ.length
  | _, _, _, .real => trivial
  | _, _, _, .bool => trivial
  | _, _, _, .lam hm _ => by
      simp only [Raw.FvBelow]; exact srT_fvBelow hm
/-- A term with `Γ ⊢⇝ m : D` has its free variables below the length of `Γ`. -/
theorem srT_fvBelow : ∀ {Γ : List FTy} {m : Tm} {D : FDist}, SRT Γ m D →
    m.FvBelow Γ.length
  | _, _, _, .val hv => by simp only [Tm.FvBelow]; exact srV_fvBelow hv
  | _, _, _, .app hv hw => ⟨srV_fvBelow hv, srV_fvBelow hw⟩
  | _, _, _, .letin hm hbody _ =>
      ⟨srT_fvBelow hm, fun i => by simpa using srT_fvBelow (hbody i)⟩
  | _, _, _, .choice h1 h2 _ => ⟨srT_fvBelow h1, srT_fvBelow h2⟩
  | _, _, _, .choiceU h1 h2 _ => ⟨srT_fvBelow h1, srT_fvBelow h2⟩
  | _, _, _, .ascT hm _ => by simp only [Tm.FvBelow]; exact srT_fvBelow hm
  | _, _, _, .ascV hv _ => by simp only [Tm.FvBelow]; exact srV_fvBelow hv
  | _, _, _, .ite hv h1 h2 _ =>
      ⟨srV_fvBelow hv, srT_fvBelow h1, srT_fvBelow h2⟩
  | _, _, _, .add hv hw => ⟨srV_fvBelow hv, srV_fvBelow hw⟩
  | _, _, _, .errD _ => trivial
end

/-- A value with a realizing typing in the empty context is closed. -/
theorem srV_closed {v : Val} {σ : FTy} (h : SRV [] v σ) : v.FvBelow 0 :=
  srV_fvBelow h

mutual
/-- Substitution of a closed value with `⊢⇝ w : τ` for the variable of type `τ`
preserves the realizing typing (raw values). -/
theorem srRaw_subst : ∀ {Δ Γ : List FTy} {τ : FTy} (u : Raw) {σ : FTy},
    SRRaw (Δ ++ τ :: Γ) u σ → ∀ {w : Val}, SRV [] w τ →
    SRRaw (Δ ++ Γ) (u.subst Δ.length w) σ
  | _, _, _, .real _, _, h, _, _ => by
      cases h; simp only [Raw.subst]; exact .real
  | _, _, _, .bool _, _, h, _, _ => by
      cases h; simp only [Raw.subst]; exact .bool
  | Δ0, _, _, .lam σ0 body, _, h, w, hw => by
      cases h with
      | lam hm hσ =>
        simp only [Raw.subst]
        rw [Val.rename_below (srV_closed hw) (Nat.zero_le 0)]
        exact .lam (srT_subst (Δ := σ0 :: Δ0) body hm hw) hσ
/-- Substitution of a closed value with `⊢⇝ w : τ` for the variable of type `τ`
preserves the realizing typing (values). -/
theorem srV_subst : ∀ {Δ Γ : List FTy} {τ : FTy} (v : Val) {σ : FTy},
    SRV (Δ ++ τ :: Γ) v σ → ∀ {w : Val}, SRV [] w τ →
    SRV (Δ ++ Γ) (v.subst Δ.length w) σ
  | Δ0, Γ0, τ0, .var x, σ, h, w, hw => by
      cases h with
      | var hx hσ =>
        by_cases h1 : x = Δ0.length
        · subst h1
          have hστ : σ = τ0 := by
            rw [List.getElem?_append, if_neg (by omega)] at hx
            have : τ0 = σ := by simpa using hx
            exact this.symm
          subst hστ
          simp only [Val.subst, if_pos rfl]
          have hwk := srV_wkapp hw (Δ0 ++ Γ0)
          simpa using hwk
        · by_cases h2 : x > Δ0.length
          · simp only [Val.subst, if_neg h1, if_pos h2]
            refine .var ?_ hσ
            rw [List.getElem?_append, if_neg (by omega)] at hx
            rw [List.getElem?_append, if_neg (by omega)]
            rw [show x - Δ0.length = (x - 1 - Δ0.length) + 1 by omega] at hx
            simpa using hx
          · simp only [Val.subst, if_neg h1, if_neg h2]
            refine .var ?_ hσ
            rw [List.getElem?_append, if_pos (by omega)] at hx
            rw [List.getElem?_append, if_pos (by omega)]
            exact hx
  | _, _, _, .asc ε u σ0, _, h, w, hw => by
      cases h with
      | ascRaw hu hσ =>
        simp only [Val.subst]
        exact .ascRaw (srRaw_subst u hu hw) hσ
  | _, _, _, .err σ0, _, h, _, _ => by
      cases h with
      | err hσ => simp only [Val.subst]; exact .err hσ
/-- Substitution of a closed value with `⊢⇝ w : τ` for the variable of type `τ`
preserves the realizing typing (terms). -/
theorem srT_subst : ∀ {Δ Γ : List FTy} {τ : FTy} (m : Tm) {D : FDist},
    SRT (Δ ++ τ :: Γ) m D → ∀ {w : Val}, SRV [] w τ →
    SRT (Δ ++ Γ) (m.subst Δ.length w) D
  | _, _, _, .val v, _, h, w, hw => by
      cases h with
      | val hv => simp only [Tm.subst]; exact .val (srV_subst v hv hw)
  | _, _, _, .app v u, _, h, w, hw => by
      cases h with
      | app hv hu =>
        simp only [Tm.subst]
        exact .app (srV_subst v hv hw) (srV_subst u hu hw)
  | Δ0, _, _, .letin m0 _ ns, _, h, w, hw => by
      cases h with
      | @letin _ _ _ ty _ _ F hm hbody hg =>
        rw [Tm.subst_letin, Val.rename_below (srV_closed hw) (Nat.zero_le 0)]
        exact .letin (srT_subst m0 hm hw)
          (fun i => srT_subst (Δ := ty i :: Δ0) (ns i) (hbody i) hw) hg
  | _, _, _, .choice p m1 m2, _, h, w, hw => by
      cases h with
      | choice h1 h2 hg =>
        simp only [Tm.subst]
        exact .choice (srT_subst m1 h1 hw) (srT_subst m2 h2 hw) hg
      | choiceU h1 h2 hg =>
        simp only [Tm.subst]
        exact .choiceU (srT_subst m1 h1 hw) (srT_subst m2 h2 hw) hg
  | _, _, _, .ascT ε m0 Db, _, h, w, hw => by
      cases h with
      | ascT hm hg => simp only [Tm.subst]; exact .ascT (srT_subst m0 hm hw) hg
  | _, _, _, .ascV ε v σ', _, h, w, hw => by
      cases h with
      | ascV hv hg => simp only [Tm.subst]; exact .ascV (srV_subst v hv hw) hg
  | _, _, _, .ite v m1 m2, _, h, w, hw => by
      cases h with
      | ite hv h1 h2 hg =>
        simp only [Tm.subst]
        exact .ite (srV_subst v hv hw) (srT_subst m1 h1 hw)
          (srT_subst m2 h2 hw) hg
  | _, _, _, .add v u, _, h, w, hw => by
      cases h with
      | add hv hu =>
        simp only [Tm.subst]
        exact .add (srV_subst v hv hw) (srV_subst u hu hw)
  | _, _, _, .errD D, _, h, _, _ => by
      cases h with
      | errD hg => simp only [Tm.subst]; exact .errD hg
end

/-- Closed substitution at the outermost binder. -/
theorem srT_subst0 {τ : FTy} {m : Tm} {D : FDist} (h : SRT [τ] m D)
    {w : Val} (hw : SRV [] w τ) : SRT [] (m.subst0 w) D :=
  srT_subst (Δ := []) _ h hw

/-- In the empty context, the type `SRV` assigns to a value is its
annotation. -/
theorem srV_tyEntry : ∀ {v : Val} {σ : FTy}, SRV [] v σ → v.tyEntry = σ
  | _, _, .var hx _ => by simp at hx
  | _, _, .ascRaw _ _ => rfl
  | _, _, .err _ => rfl

/- `SRT` mirrors the typing judgment, so it assigns the same types. -/
mutual
/-- A value has the same type in the realizing-types judgment and in the TPLC
typing. -/
theorem srV_hasTy_det : ∀ {Γ : List FTy} {v : Val} {σ σ' : FTy}, SRV Γ v σ →
    HasTyV Γ v σ' → σ = σ'
  | _, _, _, _, .var hx _, .var hx' => by
      rw [hx] at hx'; exact Option.some.inj hx'
  | _, _, _, _, .ascRaw _ _, .ascRaw _ _ _ _ => rfl
  | _, _, _, _, .err _, .err _ => rfl
/-- A term has the same type in the realizing-types judgment and in the TPLC
typing. -/
theorem srT_hasTy_det : ∀ {Γ : List FTy} {m : Tm} {D D' : FDist}, SRT Γ m D →
    HasTyT Γ m D' → D = D'
  | _, _, _, _, .val hv, .val hv' => by rw [srV_hasTy_det hv hv']
  | _, _, _, _, .app hv _, .app hv' _ => by
      have h := srV_hasTy_det hv hv'
      exact (FTy.arrow.inj h).2
  | _, _, _, _, .letin hm hbody _, .letin hm' hbody' => by
      injection srT_hasTy_det hm hm' with _ hty hC
      subst hty hC
      congr 1
      funext i
      exact srT_hasTy_det (hbody i) (hbody' i)
  | _, _, _, _, .choice h1 h2 _, .choice _ _ h1' h2' => by
      rw [srT_hasTy_det h1 h1', srT_hasTy_det h2 h2']
  | _, _, _, _, .choiceU h1 h2 _, .choiceU h1' h2' => by
      rw [srT_hasTy_det h1 h1', srT_hasTy_det h2 h2']
  | _, _, _, _, .ascT _ _, .ascT _ _ _ _ => rfl
  | _, _, _, _, .ascV _ _, .ascV _ _ _ _ => rfl
  | _, _, _, _, .ite _ h1 h2 _, .ite _ h1' h2' => by
      rw [srT_hasTy_det h1 h1', srT_hasTy_det h2 h2']
  | _, _, _, _, .add _ _, .add _ _ => rfl
  | _, _, _, _, .errD _, .errD _ => rfl
end

/-! ### Inversions of `SRT`

Several clauses have a compound index, so a case analysis on `SRT` after one on
the typing needs a dependent elimination that does not go through. The
inversions return the components and the equation, and the type is identified
by `srT_hasTy_det`. -/


/-- Inversion of `SRT` at an application. -/
theorem srT_app_inv {Γ : List FTy} {v w : Val} {D : FDist} :
    SRT Γ (.app v w) D → ∃ σ, SRV Γ v (.arrow σ D) ∧ SRV Γ w σ := by
  intro h; cases h with | app hv hw => exact ⟨_, hv, hw⟩

/-- Inversion of `SRT` at a choice with a known probability. -/
theorem srT_choice_inv {Γ : List FTy} {a : ℝ} {m n : Tm} {D : FDist} :
    SRT Γ (.choice (.q a) m n) D →
    ∃ D1 D2, SRT Γ m D1 ∧ SRT Γ n D2 ∧ D = chooseSem a D1 D2 := by
  intro h; cases h with | choice h1 h2 _ => exact ⟨_, _, h1, h2, rfl⟩

/-- Inversion of `SRT` at a conditional. -/
theorem srT_ite_inv {Γ : List FTy} {v : Val} {m n : Tm} {D : FDist} :
    SRT Γ (.ite v m n) D →
    ∃ D1 D2, SRT Γ m D1 ∧ SRT Γ n D2 ∧ D = chooseSemU D1 D2 := by
  intro h; cases h with | ite _ h1 h2 _ => exact ⟨_, _, h1, h2, rfl⟩


/-- Inversion of `SRT` at a `let`. The typing of the bound term is a
hypothesis, so that its type `μ` is a parameter (as in `red_letin_inv`). -/
theorem srT_letin_inv {Γ : List FTy} {m : Tm} {μ : FDist} {ns : Fin μ.n → Tm}
    {D : FDist} (h : SRT Γ (.letin m μ.n ns) D) (hμ : HasTyT Γ m μ) :
    ∃ F : Fin μ.n → FDist, SRT Γ m μ ∧ (∀ i, SRT (μ.ty i :: Γ) (ns i) (F i)) := by
  obtain ⟨n, ty, C⟩ := μ
  cases h with
  | @letin _ _ _ ty2 C2 _ F hm hbody _ =>
    injection srT_hasTy_det hm hμ with _ hty hC
    subst ty2 C2
    exact ⟨_, hm, hbody⟩

/-! ## No failure (Lemma 62): the error cases never fire

With the TPLC typing and `SRT`, a value ascription always composes and the
routing formula of (D::μ) is always satisfiable. The typing gives the two
precisions the composition lemmas need (`vtag_evTy` on the validity premises),
with the value's annotation as common bound. The induction also yields that
every value of the result is in `SRV`, which the routed rules consume: in
(Dlet) an entry coerces to a type syntactically equal to the value's
(`dlet_cell_ty_eq`), and in (D::μ) the target type is written in the term. -/


/-- Lemma 62 (no failure): a reduction of a closed TPLC term that erases, is
typed and satisfies `SRT` takes neither the error case of (D::σ) nor that of
(D::μ) (nor, since the term erases, an error propagation rule, (Derr) or the
choice with `?`), so it is a `RedSt` derivation; and every value of the result
is in `SRV` at its annotation. -/
theorem redSt_of_red : ∀ (k : ℕ) {tm : Tm} {V : DConf}, tm ⇓[k] V →
    ∀ {ms : SPLC.Tm}, ErTm tm ms → ∀ {D : FDist}, ⊢ tm : D → ⊢⇝ tm : D →
    RedSt tm k V ∧ ∀ i, ⊢⇝ V.val i : (V.val i).tyEntry := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro tm V hred ms her D hty hsrt
    cases hred with
    | dv =>
      cases her with
      | eval hv =>
        cases hsrt with
        | val hsv =>
          refine ⟨.dv, fun _ => ?_⟩
          show SRV [] _ (Val.tyEntry _)
          rw [srV_tyEntry hsv]
          exact hsv
    | dchoice ha0 ha1 h1 h2 =>
      cases her with
      | echoice _ _ e1 e2 =>
        cases hty with
        | choice _ _ ht1 ht2 =>
          obtain ⟨D1s, D2s, hs1, hs2, -⟩ := srT_choice_inv hsrt
          obtain rfl := srT_hasTy_det hs1 ht1
          obtain rfl := srT_hasTy_det hs2 ht2
          obtain ⟨s1, v1⟩ := ih _ (by omega) h1 e1 ht1 hs1
          obtain ⟨s2, v2⟩ := ih _ (by omega) h2 e2 ht2 hs2
          refine ⟨.dchoice ha0 ha1 s1 s2, fun i => ?_⟩
          refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i
          · show SRV [] (Fin.append _ _ (Fin.castAdd _ i1))
                (Val.tyEntry (Fin.append _ _ (Fin.castAdd _ i1)))
            rw [Fin.append_left]; exact v1 i1
          · show SRV [] (Fin.append _ _ (Fin.natAdd _ i2))
                (Val.tyEntry (Fin.append _ _ (Fin.natAdd _ i2)))
            rw [Fin.append_right]; exact v2 i2
    | dchoiceU h1 h2 => cases her
    | dadd hm =>
      refine ⟨.dadd hm, fun _ => ?_⟩
      exact .ascRaw .real sAnnTy_real
    | dmon h0 =>
      obtain ⟨s0, v0⟩ := ih _ (by omega) h0 her hty hsrt
      exact ⟨.dmon s0, v0⟩
    | dit h =>
      cases her with
      | eite hv e1 e2 =>
        cases hty with
        | ite _ ht1 ht2 =>
          obtain ⟨D1s, D2s, hs1, hs2, -⟩ := srT_ite_inv hsrt
          obtain rfl := srT_hasTy_det hs1 ht1
          obtain ⟨s1, v1⟩ := ih _ (by omega) h e1 ht1 hs1
          exact ⟨.dit s1, v1⟩
    | dif h =>
      cases her with
      | eite hv e1 e2 =>
        cases hty with
        | ite _ ht1 ht2 =>
          obtain ⟨D1s, D2s, hs1, hs2, -⟩ := srT_ite_inv hsrt
          obtain rfl := srT_hasTy_det hs2 ht2
          obtain ⟨s2, v2⟩ := ih _ (by omega) h e2 ht2 hs2
          exact ⟨.dif s2, v2⟩
    | derr => cases her
    | dascOk hm hg =>
      cases her with
      | eascV hv =>
        cases hsrt with
        | ascV hsv hgσ' =>
          cases hsv with
          | ascRaw hu hσ =>
            exact ⟨.dascOk hm hg, fun _ => .ascRaw hu hgσ'⟩
    | dascErr hne =>
      cases her with
      | eascV hv =>
        cases hty with
        | ascV htv hev hge hgσ' =>
          cases htv with
          | ascRaw hu hev1 hge1 hgσ =>
            cases hsrt with
            | ascV hsv _ =>
              cases hsv with
              | ascRaw _ hσ =>
                obtain ⟨τ, hst, hτ⟩ := sAnnTy_weakRealizes hσ
                exact absurd (not_dascErr_below hge1 hge
                  (vtag_evTy (hvtag_toVTy hev1) hge1).2
                  (vtag_evTy (hvtag_toVTy hev) hge).1 hst hτ) hne
    | @dapp ε σ' mb σa Dres v s d k1 k2 wc V' hd hc hcoe hbody =>
      cases her with
      | eapp hf ha =>
        cases hty with
        | app hv hw =>
          obtain ⟨σA, hsv, hsw⟩ := srT_app_inv hsrt
          have hdet := FTy.arrow.inj (srV_hasTy_det hsv hv)
          obtain rfl := hdet.1
          rw [hdet.2] at hsv
          cases hsv with
            | ascRaw hraw hσarr =>
              cases hraw with
              | lam hbodySRT hσ' =>
                have htcoe := dapp_coercion_typed hv hw hd
                obtain ⟨scoe, vcoe⟩ := ih _ (by omega) hcoe (.eascV ha) htcoe
                  (.ascV hsw hσ')
                cases hf with
                | elam hb =>
                  have hwEr := erVal_ascV_redSt scoe ha
                  obtain ⟨ε3, u3, σ3, hpt⟩ :=
                    redSt_ascV_asc scoe
                  obtain rfl : wc = Val.asc ε3 u3 σ3 := DConf.point_inj hpt
                  have hteq := redSt_ascV_target scoe _ rfl
                  have hwSRV : SRV [] (Val.asc ε3 u3 σ3) σ' := by
                    have := vcoe 0
                    rw [hteq] at this
                    exact this
                  have hbody' := hbody
                  rw [Tm.subErr_asc] at hbody'
                  simp only [Tm.subst0, Tm.subst] at hbody'
                  have htbody := dapp_contractum_typed hv hw hd hc hcoe
                  rw [Tm.subErr_asc] at htbody
                  simp only [Tm.subst0, Tm.subst] at htbody
                  have hsrtbody :=
                    SRT.ascT (ε := d) (srT_subst0 hbodySRT hwSRV)
                      (sAnnTy_cod hσarr)
                  obtain ⟨sb, vb⟩ := ih _ (by omega) hbody'
                    (.eascT (erTm_subst0 hb hwEr)) htbody hsrtbody
                  refine ⟨.dapp hd hc scoe ?_, vb⟩
                  rw [Tm.subErr_asc]
                  simp only [Tm.subst0, Tm.subst]
                  exact sb
    | eAscV => cases her with | eascV hv => exact absurd rfl (erVal_not_err hv _)
    | eAddL => cases her with | eadd h1 _ => exact absurd rfl (erVal_not_err h1 _)
    | eAddR => cases her with | eadd _ h2 => exact absurd rfl (erVal_not_err h2 _)
    | eApp => cases her with | eapp h1 _ => exact absurd rfl (erVal_not_err h1 _)
    | eIte _ _ =>
      cases her with | eite h1 _ _ => exact absurd rfl (erVal_not_err h1 _)
    | @dlet m0 n ty C ns k1 k2 V0 wv Vk Fb hsc hty0 hcell hbty hbred =>
      cases her with
      | eletin hne h0 hbodies =>
        cases hty with
        | @letin _ _ _ ty2 C2 _ F hm hbodyty =>
          injection det_tm hty0 hm with _ h1 h2
          subst h1 h2
          obtain ⟨Fs, hsm, hsbody⟩ := srT_letin_inv hsrt hm
          have hgμ := wf_tm hm ctxGood_nil
          obtain ⟨hstep0, hsrv0⟩ := ih _ (by omega) hsc h0 hm hsm
          have hVvals := type_safety_vals (redSt_to_red hstep0) hm
          have hVg : ∀ i, GoodTy (V0.confF.ty i) :=
            fun i => wf_val (hVvals i) ctxGood_nil
          have hpos : 1 ≤ k1 := red_index_pos hsc
          choose vsrc hvsrc using erasure_cover _ hstep0 h0
          have hcells := fun c => ih 1 (by omega) (hcell c) (.eascV (hvsrc _))
            (HasTyT.ascV (hVvals _)
              (tagReorderD_cell hVg hgμ.tys c).1
              (tagReorderD_cell hVg hgμ.tys c).2 (hgμ.tys _))
            (.ascV (hsrv0 _) (by
              show SAnnTy ((⟨n, ty, C⟩ : FDist).ty (reorderDR V0.confF ⟨n, ty, C⟩ c))
              rw [← dlet_cell_ty_eq V0.confF _ c]
              exact srV_sAnnTy (hsrv0 _)))
          have hbodies' : ∀ c, RedSt ((ns (reorderDR V0.confF ⟨n, ty, C⟩ c)).subErr (wv c) (Fb c))
                k2 (Vk c)
              ∧ ∀ i, SRV [] ((Vk c).val i) (((Vk c).val i).tyEntry) := by
            intro c
            have hwEr := erVal_ascV_redSt (hcells c).1 (hvsrc _)
            obtain ⟨ε3, u3, σ3, hpt⟩ :=
              redSt_ascV_asc (hcells c).1
            have heqw := DConf.point_inj hpt
            have hteq := redSt_ascV_target (hcells c).1 _ rfl
            have hsrv_wv := (hcells c).2 0
            rw [hteq] at hsrv_wv
            rw [heqw] at hwEr hsrv_wv
            have hbred' := hbred c
            rw [heqw, Tm.subErr_asc] at hbred'
            have hwv := dlet_cell_typed hVvals hgμ (redSt_to_red (hcells c).1)
            have hgFb := wf_tm (hbty c) (ctxGood_cons (hgμ.tys _) ctxGood_nil)
            have htb := subErr_typed hwv (hbty c) hgFb
            rw [heqw, Tm.subErr_asc] at htb
            have hFeq : Fs (reorderDR V0.confF ⟨n, ty, C⟩ c) = Fb c :=
              srT_hasTy_det (hsbody _) (hbty c)
            have hsb0 := hsbody (reorderDR V0.confF ⟨n, ty, C⟩ c)
            rw [hFeq] at hsb0
            have hsrtb := srT_subst0 hsb0 hsrv_wv
            obtain ⟨sb, vb⟩ := ih _ (by omega) hbred'
              (erTm_subst0 (hbodies _) hwEr) htb hsrtb
            refine ⟨?_, vb⟩
            rw [heqw, Tm.subErr_asc]
            exact sb
          exact ⟨.dlet hstep0 hty0 (fun c => (hcells c).1) hbty
            (fun c => (hbodies' c).1), fun i => (hbodies' _).2 _⟩
    | @dascD εd m0 μ μb k1 V0 wv hvR hsc hty0 hsat hcell =>
      cases her with
      | eascT h0 =>
        cases hty with
        | ascT htm hval hgεd hgμb =>
          cases hsrt with
          | ascT hsm hgb =>
            rw [srT_hasTy_det hsm htm] at hsm
            have hμD : μ = _ := det_tm hty0 htm
            subst hμD
            obtain ⟨hstep0, hsrv0⟩ := ih _ (by omega) hsc h0 hty0 hsm
            have hVvals := type_safety_vals (redSt_to_red hstep0) hty0
            have hgμ : GoodD μ := wf_tm hty0 ctxGood_nil
            have hVg : ∀ i, GoodTy (V0.confF.ty i) :=
              fun i => wf_val (hVvals i) ctxGood_nil
            obtain ⟨hrR, -, hhR⟩ := hval.2
            have hpos : 1 ≤ k1 := red_index_pos hsc
            choose vsrc hvsrc using erasure_cover _ hstep0 h0
            have hcells := fun c => ih 1 (by omega) (hcell c) (.eascV (hvsrc _))
              (HasTyT.ascV (hVvals _)
                (hemeetD_entry (tagReorderD_cellL hVg hgμ.tys) (fun j _ => hhR j)
                  (goodTy_tagReorderD_entry hVg hgμ.tys) (TagD.goodTy_entry hgεd) _
                  (reorderDL _ _ _).isLt (emeetD_r_lt_of_hvalid hvR.2 c))
                (goodTy_emeetD_entry (goodTy_tagReorderD_entry hVg hgμ.tys)
                  (TagD.goodTy_entry hgεd) _)
                (hgμb.tys _))
              (.ascV (hsrv0 _) (sAnnD_entries hgb _))
            refine ⟨.dascD hvR hstep0 hty0 hsat (fun c => (hcells c).1),
              fun c => ?_⟩
            have hw := (hcells c).2 0
            exact hw
    | @dascDErr εd m0 μ μb k1 V0 _ hsc hty0 hnsat =>
      cases her with
      | eascT h0 =>
        cases hty with
        | ascT htm hval hgεd hgμb =>
          cases hsrt with
          | ascT hsm hgb =>
            rw [srT_hasTy_det hsm htm] at hsm
            have hμD : μ = _ := det_tm hty0 htm
            subst hμD
            obtain ⟨hstep0, hsrv0⟩ := ih _ (by omega) hsc h0 hty0 hsm
            have hsafe := type_safety (redSt_to_red hstep0) hty0
            have hgμ : GoodD μ := wf_tm hty0 ctxGood_nil
            have hrd : EReordD V0.confF μ :=
              ereordD_of_refDist hsafe.good.good.sat hsafe.reord
            have hgr : GoodD (reorderD V0.confF μ) :=
              goodD_reorderD hsafe.good hgμ hrd
            obtain ⟨T, hst, hstT⟩ := srT_sAnnD hsm
            obtain ⟨hpL, -⟩ := validFor_evD hval.toV hgεd
            exact absurd (routing_sat_below hgr hgεd
              (eprec_reorderD .r hsafe.good hgμ) hpL
              (weakRealizesD_of_realizes hst) hstT) hnsat

/-- Item 1 of Theorem 7 over `Red`, for an elaboration that satisfies `SRT`:
`redSt_of_red` reduces it to `erasure_simulation`. -/
theorem erasure_simulation_red {m : SPLC.Tm} {ks : ℕ} {Vs : DistVal} {tm : Tm} {D : FDist}
    {k : ℕ} {V : DConf}
    (hcl : m.FvBelow 0) (hok : ProbOkT m)
    (helab : ElabT [] (embedT m) tm D) (hann : SRT [] tm D)
    (hsrc : SPLC.Red m ks Vs) (htgt : Red tm k V) :
    ∀ q, V.C q → ∀ w, erMass V q w = sMassF anfV Vs w := by
  have hΓ : CtxGood ([] : List FTy) := ctxGood_nil
  have her : ErTm tm (anfT m) := elab_erTm m helab hΓ
  have hty : HasTyT [] tm D := elab_preserves_tm helab hΓ
  exact erasure_simulation hcl hok helab hsrc
    (redSt_of_red k htgt her hty hann).1

/-! ## Static realization (Lemma 61)

The elaboration of an embedded static term satisfies `SRT`. The realization
premises of the rules for `let`, choice and the conditional come from the
forward direction of Theorem 3 (`GPLC.conservative_forward_tm`) applied to the
source node, with `elab_sound_tm` and `GPLC.det_tm` identifying the elaborated
type with the inferred one. -/

/-- `?` realizes no static type: `RealizesTy` has no clause for it. -/
theorem not_sAnnTy_unk : ¬ SAnnTy .unk
  | ⟨_, h, _⟩ => by cases h

/-- The domain and codomain of a realizing type realize. The `?` case of
`DomCod` is unreachable. -/
theorem sAnnTy_domcod {σ s : FTy} {D : FDist} (hdc : DomCod σ s D)
    (h : SAnnTy σ) : SAnnTy s ∧ SAnnD D := by
  cases hdc with
  | arrow =>
      obtain ⟨τ, hst, hs⟩ := h
      cases hst with
      | arrow h1 h2 =>
        cases hs with
        | arrow hs1 hs2 => exact ⟨⟨_, h1, hs1⟩, ⟨_, h2, hs2⟩⟩
  | unk => exact absurd h not_sAnnTy_unk

/-! ### Weakening by insertion

The elaboration of application, addition and the conditional weakens the
operands under the binders it introduces. -/

mutual
/-- Weakening by insertion at position `Δ.length` for the realizing-types
judgment (raw values). -/
theorem srRaw_wk : ∀ (u : Raw) {Δ Γ : List FTy} {σ τ : FTy},
    SRRaw (Δ ++ Γ) u σ → SRRaw (Δ ++ τ :: Γ) (u.rename Δ.length) σ
  | .real _, _, _, _, _, h => by cases h; rw [Raw.rename]; exact .real
  | .bool _, _, _, _, _, h => by cases h; rw [Raw.rename]; exact .bool
  | .lam σ0 body, Δ, _, _, τ, h => by
      cases h with
      | lam hbody hg =>
        rw [Raw.rename]
        have ih := srT_wk body (Δ := σ0 :: Δ) (τ := τ) hbody
        simp only [List.cons_append, List.length_cons] at ih
        exact .lam ih hg
/-- Weakening by insertion at position `Δ.length` for the realizing-types
judgment (values). -/
theorem srV_wk : ∀ (v : Val) {Δ Γ : List FTy} {σ τ : FTy},
    SRV (Δ ++ Γ) v σ → SRV (Δ ++ τ :: Γ) (v.rename Δ.length) σ
  | .var _, _, _, _, _, h => by
      cases h with
      | var hx hg => rw [Val.rename]; exact .var (by rw [getElem?_insert]; exact hx) hg
  | .asc _ u _, _, _, _, _, h => by
      cases h with
      | ascRaw hu hg => rw [Val.rename]; exact .ascRaw (srRaw_wk u hu) hg
  | .err _, _, _, _, _, h => by
      cases h with | err hg => rw [Val.rename]; exact .err hg
/-- Weakening by insertion at position `Δ.length` for the realizing-types
judgment (terms). -/
theorem srT_wk : ∀ (m : Tm) {Δ Γ : List FTy} {D : FDist} {τ : FTy},
    SRT (Δ ++ Γ) m D → SRT (Δ ++ τ :: Γ) (m.rename Δ.length) D
  | .val v, _, _, _, _, h => by
      cases h with | val hv => rw [Tm.rename]; exact .val (srV_wk v hv)
  | .app v w, _, _, _, _, h => by
      cases h with
      | app hv hw => rw [Tm.rename]; exact .app (srV_wk v hv) (srV_wk w hw)
  | .letin mm _ ns, Δ, _, _, τ, h => by
      cases h with
      | @letin _ _ _ ty _ _ F hm hbody hg =>
        rw [Tm.rename_letin]
        refine .letin (srT_wk mm hm) (fun i => ?_) hg
        have ih := srT_wk (ns i) (Δ := ty i :: Δ) (τ := τ) (hbody i)
        simp only [List.cons_append, List.length_cons] at ih
        exact ih
  | .choice _ m n, _, _, _, _, h => by
      cases h with
      | choice hm hn hg =>
        rw [Tm.rename]; exact .choice (srT_wk m hm) (srT_wk n hn) hg
      | choiceU hm hn hg =>
        rw [Tm.rename]; exact .choiceU (srT_wk m hm) (srT_wk n hn) hg
  | .ascT _ m _, _, _, _, _, h => by
      cases h with
      | ascT hm hg => rw [Tm.rename]; exact .ascT (srT_wk m hm) hg
  | .ascV _ v _, _, _, _, _, h => by
      cases h with
      | ascV hv hg => rw [Tm.rename]; exact .ascV (srV_wk v hv) hg
  | .ite v m n, _, _, _, _, h => by
      cases h with
      | ite hv hm hn hg =>
        rw [Tm.rename]
        exact .ite (srV_wk v hv) (srT_wk m hm) (srT_wk n hn) hg
  | .add v w, _, _, _, _, h => by
      cases h with
      | add hv hw => rw [Tm.rename]; exact .add (srV_wk v hv) (srV_wk w hw)
  | .errD _, _, _, _, _, h => by
      cases h with | errD hg => rw [Tm.rename]; exact .errD hg
end

/-- Weakening at the front, the form the monadic elaboration uses. -/
theorem srV_wk0 {Γ : List FTy} {v : Val} {σ τ : FTy} (h : SRV Γ v σ) :
    SRV (τ :: Γ) (v.rename 0) σ :=
  srV_wk v (Δ := []) h

/-- Weakening at the head of the context for the realizing-types judgment
(terms). -/
theorem srT_wk0 {Γ : List FTy} {m : Tm} {D : FDist} {τ : FTy}
    (h : SRT Γ m D) : SRT (τ :: Γ) (m.rename 0) D :=
  srT_wk m (Δ := []) h

/-- A `let` with a Dirac bound term has the type of its body (`letSem_point`);
every `let` that the elaboration introduces has this shape. -/
theorem srT_letin1 {Γ : List FTy} {m : Tm} {σ : FTy} {body : Tm} {D : FDist}
    (hs : SRT Γ m (pointF σ)) (hb : SRT (σ :: Γ) body D) :
    SRT Γ (.letin m 1 (fun _ => body)) D := by
  have hg : SAnnD (letSem (pointF σ) (fun _ => D)) := by
    rw [letSem_point]; exact srT_sAnnD hb
  have h : SRT Γ (.letin m 1 (fun _ => body)) (letSem (pointF σ) (fun _ => D)) :=
    SRT.letin hs (fun _ => hb) hg
  rwa [letSem_point] at h

/-- The type the elaboration infers for an embedded static term realizes its
SPLC type: the forward direction of Theorem 3, with `elab_sound_tm` and
`GPLC.det_tm` identifying the two types. -/
theorem sAnnD_of_elab {Γ : Ctx} {Φ : List FTy} {ms : SPLC.Tm} {T : DTy} {tsm : Tm}
    {D : FDist} (hty : SPLC.HasTyT Γ ms T) (hctx : RealizesCtx Φ Γ) (hΓs : CtxStatic Γ)
    (hΓw : CtxWf Γ) (hs : IsStaticTm ms)
    (he : ElabT Φ (embedT ms) tsm D) : SAnnD D := by
  obtain ⟨D', hD', hst⟩ := conservative_forward_tm hty hctx hΓs hΓw hs
  have hDD : D = D' := GPLC.det_tm (elab_sound_tm he) hD'
  subst hDD
  exact ⟨T, hst, isStatic_tm hty hΓs hs⟩

/-- The same, as a realization of the SPLC type itself; the `let` case uses it
to pair each entry of the bound term with a source branch. -/
theorem realizesD_of_elab {Γ : Ctx} {Φ : List FTy} {ms : SPLC.Tm} {T : DTy} {tsm : Tm}
    {D : FDist} (hty : SPLC.HasTyT Γ ms T) (hctx : RealizesCtx Φ Γ) (hΓs : CtxStatic Γ)
    (hΓw : CtxWf Γ) (hs : IsStaticTm ms)
    (he : ElabT Φ (embedT ms) tsm D) : RealizesD D T := by
  obtain ⟨D', hD', hst⟩ := conservative_forward_tm hty hctx hΓs hΓw hs
  have hDD : D = D' := GPLC.det_tm (elab_sound_tm he) hD'
  subst hDD
  exact hst


/- Lemma 61 (static realization), open-term form, by induction on the SPLC
typing with the elaboration alongside. The `let` case pairs each entry of the
elaborated bound term with the source branch that its realization covers (left
coverage), not by position. -/
mutual
/-- Lemma 61 (static realization), values. -/
theorem srV_of_elab : ∀ {Γ : Ctx} {Φ : List FTy} {v : SPLC.Val} {τ : Ty}
    {tv : Val} {σ : FTy},
    SPLC.HasTyV Γ v τ → RealizesCtx Φ Γ → CtxStatic Γ → CtxWf Γ → CtxGood Φ → IsStaticVal v →
    ElabV Φ (embedV v) tv σ → SRV Φ tv σ
  | _, _, _, _, _, _, .var _, hctx, hΓs, _, _, _, he => by
      simp only [embedV] at he
      cases he with
      | evar hy =>
        obtain ⟨τ0, h1, h2⟩ := realizesCtx_getElemF hctx hy
        exact .var hy ⟨τ0, h2, ctxStatic_get hΓs h1⟩
  | _, _, _, _, _, _, .real, _, _, _, _, _, he => by
      simp only [embedV] at he
      cases he with
      | ereal => exact .ascRaw .real sAnnTy_real
  | _, _, _, _, _, _, .bool, _, _, _, _, _, he => by
      simp only [embedV] at he
      cases he with
      | ebool => exact .ascRaw .bool sAnnTy_bool
  | _, _, _, _, _, _, .lam hm hτ, hctx, hΓs, hΓw, hΦg, hsv, he => by
      simp only [embedV] at he
      cases hsv with
      | lam hsτ hsm =>
        cases he with
        | elam hbody hwτ =>
          have hlift := realizesTy_lift hsτ hwτ
          have hσ : SAnnTy (liftFTy _) := ⟨_, hlift, hsτ⟩
          have ih := srT_of_elab hm (.cons hlift hctx) (ctxStatic_cons hsτ hΓs)
            (ctxWf_cons hτ hΓw) (ctxGood_cons (goodTy_liftF hwτ) hΦg) hsm hbody
          exact .ascRaw (.lam ih hσ) (sAnnTy_arrow hσ (srT_sAnnD ih))
/-- Lemma 61 (static realization), open-term form: every elaboration of a
well-typed embedded static term, in a context that realizes the SPLC context,
satisfies `SRT`. -/
theorem srT_of_elab : ∀ {Γ : Ctx} {Φ : List FTy} {ms : SPLC.Tm} {T : DTy}
    {tm : Tm} {D : FDist},
    Γ ⊢ₛ ms : T → RealizesCtx Φ Γ → CtxStatic Γ → CtxWf Γ → CtxGood Φ → IsStaticTm ms →
    Φ ⊢ embedT ms : D ⇝ tm → Φ ⊢⇝ tm : D
  | _, _, _, _, _, _, .val hv, hctx, hΓs, hΓw, hΦg, hsm, he => by
      cases hsm with
      | val hsv =>
        simp only [embedT] at he
        cases he with
        | eval hev => exact .val (srV_of_elab hv hctx hΓs hΓw hΦg hsv hev)
  | _, _, _, _, _, _, .app hv hw _, hctx, hΓs, hΓw, hΦg, hsm, he => by
      cases hsm with
      | app hsv hsw =>
        simp only [embedT] at he
        cases he with
        | eapp hev hew hdc _ _ _ =>
          have ihv := srV_of_elab hv hctx hΓs hΓw hΦg hsv hev
          have ihw := srV_of_elab hw hctx hΓs hΓw hΦg hsw hew
          obtain ⟨hsdom, hscod⟩ := sAnnTy_domcod hdc (srV_sAnnTy ihv)
          refine srT_letin1 (.ascV ihw hsdom) (srT_letin1
            (.ascV (srV_wk0 ihv) (sAnnTy_arrow hsdom hscod)) ?_)
          exact .app (.var (by simp) (sAnnTy_arrow hsdom hscod)) (.var (by simp) hsdom)
  | _, _, _, _, _, _, @SPLC.HasTyT.letin _ _ _ es Tf hm hF,
      hctx, hΓs, hΓw, hΦg, hsm, he => by
      have hgD' : SAnnD _ :=
        sAnnD_of_elab (SPLC.HasTyT.letin hm hF) hctx hΓs hΓw hsm he
      cases hsm with
      | letin hsm' hsn =>
        have hstat : IsStaticDTy (.dist es) := isStatic_tm hm hΓs hsm'
        have hwf : SPLC.WfDTy (.dist es) := SPLC.wf_tm hm hΓw
        obtain ⟨hEs, _⟩ := wfDTy_dist_inv hwf
        have hse : IsStaticEntries es := by exact hstat.entries
        simp only [embedT] at he
        cases he with
        | @eletin _ _ tm0 k0 ty0 C0 _ tns F helabm helabb =>
          have hstD : RealizesD ⟨k0, ty0, C0⟩ (.dist es) :=
            realizesD_of_elab hm hctx hΓs hΓw hsm' helabm
          have hgD : GoodD ⟨k0, ty0, C0⟩ := good_tm (elab_sound_tm helabm) hΦg
          refine SRT.letin (srT_of_elab hm hctx hΓs hΓw hΦg hsm' helabm)
            (fun i => ?_) hgD'
          cases hstD with
          | dist R hR hcovL _ _ _ =>
            obtain ⟨j, hij⟩ := hcovL i
            have htyj : RealizesTy (ty0 i) ((es.get j).1) := hR i j hij
            have hstj : IsStaticTy ((es.get j).1) :=
              entry_static_ty_mem hse _ (List.get_mem es j)
            have hwfj : SPLC.WfTy ((es.get j).1) :=
              hEs _ (List.get_mem es j)
            exact srT_of_elab (hF j) (.cons htyj hctx) (ctxStatic_cons hstj hΓs)
              (ctxWf_cons hwfj hΓw) (ctxGood_cons (hgD.tys i) hΦg) hsn (helabb i)
  | _, _, _, _, _, _, .choice hm hn, hctx, hΓs, hΓw, hΦg, hsm, he => by
      have hgD' : SAnnD _ :=
        sAnnD_of_elab (SPLC.HasTyT.choice hm hn) hctx hΓs hΓw hsm he
      cases hsm with
      | choice _ _ hsm' hsn =>
        simp only [embedT] at he
        cases he with
        | echoice _ _ hem hen =>
          exact .choice (srT_of_elab hm hctx hΓs hΓw hΦg hsm' hem)
            (srT_of_elab hn hctx hΓs hΓw hΦg hsn hen) hgD'
  | _, _, _, _, _, _, .ascT hm _ _, hctx, hΓs, hΓw, hΦg, hsm, he => by
      cases hsm with
      | ascT hsm' hstT =>
        simp only [embedT] at he
        cases he with
        | eascT hem _ hwfT =>
          exact .ascT (srT_of_elab hm hctx hΓs hΓw hΦg hsm' hem)
            (sAnnD_lift hstT hwfT)
  | _, _, _, _, _, _, .ascV hv _ _, hctx, hΓs, hΓw, hΦg, hsm, he => by
      cases hsm with
      | ascV hsv hsτ =>
        simp only [embedT] at he
        cases he with
        | eascV hev _ hwτ _ =>
          exact .ascV (srV_of_elab hv hctx hΓs hΓw hΦg hsv hev)
            (sAnnTy_lift hsτ hwτ)
  | _, _, _, _, _, _, .add hv _ hw _, hctx, hΓs, hΓw, hΦg, hsm, he => by
      cases hsm with
      | add hsv hsw =>
        simp only [embedT] at he
        cases he with
        | eadd hev hew _ _ _ _ =>
          have ihv := srV_of_elab hv hctx hΓs hΓw hΦg hsv hev
          have ihw := srV_of_elab hw hctx hΓs hΓw hΦg hsw hew
          refine srT_letin1 (.ascV ihv sAnnTy_real) (srT_letin1
            (.ascV (srV_wk0 ihw) sAnnTy_real) ?_)
          exact .add (.var (by simp) sAnnTy_real) (.var (by simp) sAnnTy_real)
  | _, _, _, _, _, _, .ite hv hc hm hn hcd, hctx, hΓs, hΓw, hΦg, hsm, he => by
      have hgD' : SAnnD _ :=
        sAnnD_of_elab (SPLC.HasTyT.ite hv hc hm hn hcd) hctx hΓs hΓw hsm he
      cases hsm with
      | ite hsv hsm' hsn =>
        simp only [embedT] at he
        cases he with
        | eite hev hem hen _ _ _ =>
          have ihv := srV_of_elab hv hctx hΓs hΓw hΦg hsv hev
          refine srT_letin1 (.ascV ihv sAnnTy_bool) ?_
          exact .ite (.var (by simp) sAnnTy_bool)
            (srT_wk0 (srT_of_elab hm hctx hΓs hΓw hΦg hsm' hem))
            (srT_wk0 (srT_of_elab hn hctx hΓs hΓw hΦg hsn hen)) hgD'
end


/-- Lemma 61 (static realization): the elaboration of a closed well-typed static
term satisfies `SRT` in the empty context. -/
theorem srT_closed {m : SPLC.Tm} {T : DTy} {tm : Tm} {D : FDist}
    (hty : ⊢ₛ m : T) (hs : IsStaticTm m) (he : ⊢ embedT m : D ⇝ tm) :
    ⊢⇝ tm : D :=
  srT_of_elab hty .nil (by intro τ h; simp at h) (by intro τ h; simp at h)
    ctxGood_nil hs he

/-- Theorem 7 (dynamic conservative extension of TPLC with respect to SPLC),
item 1. Let `m` be a closed SPLC term with `⊢ₛ m : T`, and `tm` the elaboration
of its embedding. If `m` runs to `Vs` and `tm` runs to `V`, then for every
solution `q` of the formula of `V` and every SPLC value `w`, the erased measure
`erMass V q w` is the total probability `Vs` gives to the outcomes `v` with
`anfV v = w`. `IsStaticTm m` says that `m` is an SPLC term (its choice
probabilities lie in `[0,1]`, so `ProbOkT m` holds by `probOkT_of_isStaticTm`);
closedness follows from the typing in the empty context. -/
theorem dynamic_conservative_extension {m : SPLC.Tm} {T : DTy} {ks : ℕ} {Vs : DistVal} {tm : Tm}
    {D : FDist} {k : ℕ} {V : DConf}
    (hty : ⊢ₛ m : T) (hs : IsStaticTm m)
    (helab : ⊢ embedT m : D ⇝ tm)
    (hsrc : m ⇓ₛ[ks] Vs) (htgt : tm ⇓[k] V) :
    ∀ q, V.C q → ∀ w, erMass V q w = sMassF anfV Vs w :=
  erasure_simulation_red (SPLC.hasTy_fvBelow_tm hty SPLC.ctxWf_nil)
    (probOkT_of_isStaticTm hs) helab (srT_closed hty hs helab) hsrc htgt

/-- Theorem 7 (dynamic conservative extension of TPLC with respect to SPLC),
item 2: on reals and booleans the erased measure equals the source measure. -/
theorem dynamic_conservative_extension_obs {m : SPLC.Tm} {T : DTy} {ks : ℕ} {Vs : DistVal}
    {tm : Tm} {D : FDist} {k : ℕ} {V : DConf}
    (hty : ⊢ₛ m : T) (hs : IsStaticTm m)
    (helab : ⊢ embedT m : D ⇝ tm)
    (hsrc : m ⇓ₛ[ks] Vs) (htgt : tm ⇓[k] V) :
    ∀ q, V.C q → (∀ r : ℝ, erMass V q (.real r) = srcMass Vs (.real r)) ∧
      (∀ b : Bool, erMass V q (.bool b) = srcMass Vs (.bool b)) := by
  have hΓ : CtxGood ([] : List FTy) := ctxGood_nil
  have her : ErTm tm (anfT m) := elab_erTm m helab hΓ
  have htyT : HasTyT [] tm D := elab_preserves_tm helab hΓ
  exact erasure_simulation_obs (SPLC.hasTy_fvBelow_tm hty SPLC.ctxWf_nil)
    (probOkT_of_isStaticTm hs) helab hsrc
    (redSt_of_red k htgt her htyT (srT_closed hty hs helab)).1

/-! ### Lemma 67 and Theorem 8 over `Red`

The article states both over `Red`, for a term that is typed and satisfies `SRT`
(Definition 16). `redSt_of_red` (Lemma 62) reduces them to the forms over
`RedSt`. -/

/-- Lemma 67 (coverage): every outcome of the result of a reduction of a closed
TPLC term that erases, is typed and satisfies `SRT` erases to some SPLC
value. -/
theorem erasure_cover_red {k : ℕ} {tm : Tm} {V : DConf} (hred : tm ⇓[k] V)
    {m : SPLC.Tm} (her : ErTm tm m) {D : FDist} (hty : ⊢ tm : D)
    (hsrt : ⊢⇝ tm : D) : ∀ i, ∃ v, ErVal (V.val i) v :=
  erasure_cover k (redSt_of_red k hred her hty hsrt).1 her

/-- Theorem 8 (erasure preserves measure): for a closed TPLC term `tm` that
erases to `ms`, is typed and satisfies `SRT`, if `tm` reduces to `V` and `ms` to
`Vs`, then for every solution `q` of the formula of `V` and every SPLC value
`w`, `erMass V q w = srcMass Vs w`. -/
theorem erasure_meas_red {k : ℕ} {tm : Tm} {V : DConf} (hred : tm ⇓[k] V)
    {ms : SPLC.Tm} {ks : ℕ} {Vs : DistVal} (her : ErTm tm ms) (hs : ms ⇓ₛ[ks] Vs)
    {D : FDist} (hty : ⊢ tm : D) (hsrt : ⊢⇝ tm : D) :
    ∀ q, V.C q → ∀ w, erMass V q w = srcMass Vs w :=
  erasure_meas k (redSt_of_red k hred her hty hsrt).1 her hs

end GradualProb.TPLC
