import GradualProb.TPLC.TypeSafety

/-!
# Precision under renaming and substitution

This module proves Lemma 43 (substitution preserves precision) and Lemma 44
(weakening preserves precision) for TPLC: term precision is stable under
renaming and under substitution of related values, which the `let` and
application cases of the dynamic gradual guarantee (Theorem 5) need. Because
the precision rule for `let` and the ascription rules quantify over the
typings of subterms, transporting them through renaming and substitution
requires inverse typing lemmas, proved first.

## Main results

* `subep_noerr`: Lemma 43 (substitution preserves precision), with the
  function `sub` of the article (`Tm.subErr`) and values that are not errors.
* `prec_subst0`: the same statement for ordinary substitution at index 0.
* `prec_rename_val`, `prec_rename_tm`: Lemma 44 (weakening preserves
  precision), as renaming at an arbitrary position.
* `prec_subst_tm`: precision is stable under substitution of related values
  at an arbitrary position.

## Reading guide

* `hasTy_pad_*`: appending types on the right of the context preserves
  typing (a typed term never looks past its context).
* `hasTy_unrename_*`, `hasTy_unsubst_*`: a typing of the renamed
  (substituted) term yields a typing of the original term, in the context
  without (with) the slot.
* `hasTy_closed_det_*`: the type of a closed term does not depend on the
  context.
* `prec_rename_*` (Lemma 44), `prec_subst_*`, then `prec_subst0` and
  `subep_noerr` (Lemma 43).
* `red_index_mono`: monotonicity of the big-step reduction in its derivation
  index (auxiliary, used in `TPLC/Normalization`).
-/

namespace GradualProb.TPLC

open GradualProb.GPLC

/-! ## Right padding: appending context types preserves typing -/

mutual
/-- Appending types on the right of the context preserves the typing of a
raw value. -/
theorem hasTy_pad_raw : ∀ (u : Raw) {Γ : List FTy} {σ : FTy} (Ξ : List FTy),
    HasTyRaw Γ u σ → HasTyRaw (Γ ++ Ξ) u σ
  | .real _, _, _, _, h => by cases h; exact .real
  | .bool _, _, _, _, h => by cases h; exact .bool
  | .lam σ0 body, _, _, Ξ, h => by
      cases h with
      | lam hbody hg => exact .lam (hasTy_pad_tm body Ξ hbody) hg
/-- Appending types on the right of the context preserves value typing. -/
theorem hasTy_pad_val : ∀ (v : Val) {Γ : List FTy} {σ : FTy} (Ξ : List FTy),
    HasTyV Γ v σ → HasTyV (Γ ++ Ξ) v σ
  | .var x, Γ, σ, Ξ, h => by
      cases h with
      | var hx =>
        refine .var ?_
        have hlt : x < Γ.length := by
          by_contra hge
          rw [List.getElem?_eq_none (by omega)] at hx
          cases hx
        rw [List.getElem?_append_left hlt]
        exact hx
  | .asc _ u _, _, _, Ξ, h => by
      cases h with
      | ascRaw hu hev hge hg => exact .ascRaw (hasTy_pad_raw u Ξ hu) hev hge hg
  | .err _, _, _, Ξ, h => by
      cases h with | err hg => exact .err hg
/-- Appending types on the right of the context preserves term typing. -/
theorem hasTy_pad_tm : ∀ (m : Tm) {Γ : List FTy} {D : FDist} (Ξ : List FTy),
    HasTyT Γ m D → HasTyT (Γ ++ Ξ) m D
  | .val v, _, _, Ξ, h => by
      cases h with | val hv => exact .val (hasTy_pad_val v Ξ hv)
  | .app v w, _, _, Ξ, h => by
      cases h with
      | app hv hw => exact .app (hasTy_pad_val v Ξ hv) (hasTy_pad_val w Ξ hw)
  | .letin mm _ ns, _, _, Ξ, h => by
      cases h with
      | letin hm hbody =>
        exact .letin (hasTy_pad_tm mm Ξ hm) (fun i => hasTy_pad_tm (ns i) Ξ (hbody i))
  | .choice _ m n, _, _, Ξ, h => by
      cases h with
      | choice ha0 ha1 hm hn =>
        exact .choice ha0 ha1 (hasTy_pad_tm m Ξ hm) (hasTy_pad_tm n Ξ hn)
      | choiceU hm hn =>
        exact .choiceU (hasTy_pad_tm m Ξ hm) (hasTy_pad_tm n Ξ hn)
  | .ascT _ m _, _, _, Ξ, h => by
      cases h with
      | ascT hm hev hge hg => exact .ascT (hasTy_pad_tm m Ξ hm) hev hge hg
  | .ascV _ v _, _, _, Ξ, h => by
      cases h with
      | ascV hv hev hge hg => exact .ascV (hasTy_pad_val v Ξ hv) hev hge hg
  | .ite v m n, _, _, Ξ, h => by
      cases h with
      | ite hv hm hn =>
        exact .ite (hasTy_pad_val v Ξ hv) (hasTy_pad_tm m Ξ hm)
          (hasTy_pad_tm n Ξ hn)
  | .add v w, _, _, Ξ, h => by
      cases h with
      | add hv hw => exact .add (hasTy_pad_val v Ξ hv) (hasTy_pad_val w Ξ hw)
  | .errD _, _, _, Ξ, h => by
      cases h with | errD hg => exact .errD hg
end

/-! ## Unrenaming of typings: a typing of the renamed term drops the inserted
slot -/

mutual
/-- If the raw value renamed at position `|Δ|` has type `σ` under
`Δ ++ τ :: Γ`, then the raw value has type `σ` under `Δ ++ Γ`. -/
theorem hasTy_unrename_raw : ∀ (u : Raw) {Δ Γ : List FTy} {σ τ : FTy},
    HasTyRaw (Δ ++ τ :: Γ) (u.rename Δ.length) σ → HasTyRaw (Δ ++ Γ) u σ
  | .real _, _, _, _, _, h => by rw [Raw.rename] at h; cases h; exact .real
  | .bool _, _, _, _, _, h => by rw [Raw.rename] at h; cases h; exact .bool
  | .lam σ0 body, Δ, _, _, τ, h => by
      rw [Raw.rename] at h
      cases h with
      | lam hbody hg =>
        have ih := hasTy_unrename_tm body (Δ := σ0 :: Δ) (τ := τ)
          (by simpa using hbody)
        exact .lam ih hg
/-- If the value renamed at position `|Δ|` has type `σ` under `Δ ++ τ :: Γ`,
then the value has type `σ` under `Δ ++ Γ`. -/
theorem hasTy_unrename_val : ∀ (v : Val) {Δ Γ : List FTy} {σ τ : FTy},
    HasTyV (Δ ++ τ :: Γ) (v.rename Δ.length) σ → HasTyV (Δ ++ Γ) v σ
  | .var x, Δ, Γ, σ, τ, h => by
      rw [Val.rename] at h
      cases h with
      | var hx =>
        refine .var ?_
        by_cases hlt : x < Δ.length
        · rw [if_pos hlt] at hx
          rw [List.getElem?_append_left hlt] at hx
          rw [List.getElem?_append_left hlt]
          exact hx
        · rw [if_neg hlt] at hx
          rw [List.getElem?_append_right (by omega : Δ.length ≤ x + 1),
            show x + 1 - Δ.length = (x - Δ.length) + 1 from by omega,
            List.getElem?_cons_succ] at hx
          rw [List.getElem?_append_right (by omega : Δ.length ≤ x)]
          exact hx
  | .asc _ u _, _, _, _, _, h => by
      rw [Val.rename] at h
      cases h with
      | ascRaw hu hev hge hg => exact .ascRaw (hasTy_unrename_raw u hu) hev hge hg
  | .err _, _, _, _, _, h => by
      rw [Val.rename] at h
      cases h with | err hg => exact .err hg
/-- If the term renamed at position `|Δ|` has type `D` under `Δ ++ τ :: Γ`,
then the term has type `D` under `Δ ++ Γ`. -/
theorem hasTy_unrename_tm : ∀ (m : Tm) {Δ Γ : List FTy} {D : FDist} {τ : FTy},
    HasTyT (Δ ++ τ :: Γ) (m.rename Δ.length) D → HasTyT (Δ ++ Γ) m D
  | .val v, _, _, _, _, h => by
      rw [Tm.rename] at h
      cases h with | val hv => exact .val (hasTy_unrename_val v hv)
  | .app v w, _, _, _, _, h => by
      rw [Tm.rename] at h
      cases h with
      | app hv hw => exact .app (hasTy_unrename_val v hv) (hasTy_unrename_val w hw)
  | .letin mm _ ns, Δ, _, _, τ, h => by
      rw [Tm.rename_letin] at h
      cases h with
      | @letin _ _ _ ty _ _ F hm hbody =>
        refine .letin (hasTy_unrename_tm mm hm) (fun i => ?_)
        exact hasTy_unrename_tm (ns i) (Δ := ty i :: Δ) (τ := τ) (by simpa using hbody i)
  | .choice _ m n, _, _, _, _, h => by
      rw [Tm.rename] at h
      cases h with
      | choice ha0 ha1 hm hn =>
        exact .choice ha0 ha1 (hasTy_unrename_tm m hm) (hasTy_unrename_tm n hn)
      | choiceU hm hn =>
        exact .choiceU (hasTy_unrename_tm m hm) (hasTy_unrename_tm n hn)
  | .ascT _ m _, _, _, _, _, h => by
      rw [Tm.rename] at h
      cases h with
      | ascT hm hev hge hg => exact .ascT (hasTy_unrename_tm m hm) hev hge hg
  | .ascV _ v _, _, _, _, _, h => by
      rw [Tm.rename] at h
      cases h with
      | ascV hv hev hge hg => exact .ascV (hasTy_unrename_val v hv) hev hge hg
  | .ite v m n, _, _, _, _, h => by
      rw [Tm.rename] at h
      cases h with
      | ite hv hm hn =>
        exact .ite (hasTy_unrename_val v hv) (hasTy_unrename_tm m hm)
          (hasTy_unrename_tm n hn)
  | .add v w, _, _, _, _, h => by
      rw [Tm.rename] at h
      cases h with
      | add hv hw => exact .add (hasTy_unrename_val v hv) (hasTy_unrename_val w hw)
  | .errD _, _, _, _, _, h => by
      rw [Tm.rename] at h
      cases h with | errD hg => exact .errD hg
end

/-! ## Unsubstitution of typings: with the substituted value typed in the
result context, a typing of the substituted term re-inserts the slot -/

mutual
/-- If `Δ ++ Γ ⊢ w : τ` and the raw value with `w` substituted at position
`|Δ|` has type `σ` under `Δ ++ Γ`, then the raw value has type `σ` under
`Δ ++ τ :: Γ`. -/
theorem hasTy_unsubst_raw : ∀ (u : Raw) {Δ Γ : List FTy} {σ τ : FTy} {w : Val},
    HasTyV (Δ ++ Γ) w τ → HasTyRaw (Δ ++ Γ) (u.subst Δ.length w) σ →
    HasTyRaw (Δ ++ τ :: Γ) u σ
  | .real _, _, _, _, _, _, _, h => by rw [Raw.subst] at h; cases h; exact .real
  | .bool _, _, _, _, _, _, _, h => by rw [Raw.subst] at h; cases h; exact .bool
  | .lam σ0 body, Δ, _, _, τ, w, hw, h => by
      rw [Raw.subst] at h
      cases h with
      | lam hbody hg =>
        have ih := hasTy_unsubst_tm body (Δ := σ0 :: Δ) (τ := τ)
          (hasTy_wk0_val hw) (by simpa using hbody)
        exact .lam ih hg
/-- If `Δ ++ Γ ⊢ w : τ` and the value with `w` substituted at position `|Δ|`
has type `σ` under `Δ ++ Γ`, then the value has type `σ` under
`Δ ++ τ :: Γ`. -/
theorem hasTy_unsubst_val : ∀ (v : Val) {Δ Γ : List FTy} {σ τ : FTy} {w : Val},
    HasTyV (Δ ++ Γ) w τ → HasTyV (Δ ++ Γ) (v.subst Δ.length w) σ →
    HasTyV (Δ ++ τ :: Γ) v σ
  | .var x, Δ, Γ, σ, τ, w, hw, h => by
      rw [Val.subst] at h
      by_cases h1 : x = Δ.length
      · rw [if_pos h1] at h
        obtain rfl : σ = τ := det_val h hw
        subst h1
        refine .var ?_
        rw [List.getElem?_append_right (le_refl _), Nat.sub_self,
          List.getElem?_cons_zero]
      · rw [if_neg h1] at h
        by_cases h2 : x > Δ.length
        · rw [if_pos h2] at h
          cases h with
          | var hx =>
            refine .var ?_
            rw [List.getElem?_append_right (by omega : Δ.length ≤ x - 1)] at hx
            rw [List.getElem?_append_right (by omega : Δ.length ≤ x),
              show x - Δ.length = (x - 1 - Δ.length) + 1 from by omega,
              List.getElem?_cons_succ]
            exact hx
        · rw [if_neg h2] at h
          cases h with
          | var hx =>
            have hlt : x < Δ.length := by omega
            refine .var ?_
            rw [List.getElem?_append_left hlt] at hx
            rw [List.getElem?_append_left hlt]
            exact hx
  | .asc _ u _, _, _, _, _, _, hw, h => by
      rw [Val.subst] at h
      cases h with
      | ascRaw hu hev hge hg => exact .ascRaw (hasTy_unsubst_raw u hw hu) hev hge hg
  | .err _, _, _, _, _, _, _, h => by
      rw [Val.subst] at h
      cases h with | err hg => exact .err hg
/-- If `Δ ++ Γ ⊢ w : τ` and the term with `w` substituted at position `|Δ|`
has type `D` under `Δ ++ Γ`, then the term has type `D` under
`Δ ++ τ :: Γ`. -/
theorem hasTy_unsubst_tm : ∀ (m : Tm) {Δ Γ : List FTy} {D : FDist} {τ : FTy} {w : Val},
    HasTyV (Δ ++ Γ) w τ → HasTyT (Δ ++ Γ) (m.subst Δ.length w) D →
    HasTyT (Δ ++ τ :: Γ) m D
  | .val v, _, _, _, _, _, hw, h => by
      rw [Tm.subst] at h
      cases h with | val hv => exact .val (hasTy_unsubst_val v hw hv)
  | .app v u, _, _, _, _, _, hw, h => by
      rw [Tm.subst] at h
      cases h with
      | app hv hu =>
        exact .app (hasTy_unsubst_val v hw hv) (hasTy_unsubst_val u hw hu)
  | .letin mm _ ns, Δ, _, _, τ, w, hw, h => by
      rw [Tm.subst_letin] at h
      cases h with
      | @letin _ _ _ ty _ _ F hm hbody =>
        refine .letin (hasTy_unsubst_tm mm hw hm) (fun i => ?_)
        exact hasTy_unsubst_tm (ns i) (Δ := ty i :: Δ) (τ := τ) (hasTy_wk0_val hw)
          (by simpa using hbody i)
  | .choice _ m n, _, _, _, _, _, hw, h => by
      rw [Tm.subst] at h
      cases h with
      | choice ha0 ha1 hm hn =>
        exact .choice ha0 ha1 (hasTy_unsubst_tm m hw hm) (hasTy_unsubst_tm n hw hn)
      | choiceU hm hn =>
        exact .choiceU (hasTy_unsubst_tm m hw hm) (hasTy_unsubst_tm n hw hn)
  | .ascT _ m _, _, _, _, _, _, hw, h => by
      rw [Tm.subst] at h
      cases h with
      | ascT hm hev hge hg => exact .ascT (hasTy_unsubst_tm m hw hm) hev hge hg
  | .ascV _ v _, _, _, _, _, _, hw, h => by
      rw [Tm.subst] at h
      cases h with
      | ascV hv hev hge hg => exact .ascV (hasTy_unsubst_val v hw hv) hev hge hg
  | .ite v m n, _, _, _, _, _, hw, h => by
      rw [Tm.subst] at h
      cases h with
      | ite hv hm hn =>
        exact .ite (hasTy_unsubst_val v hw hv) (hasTy_unsubst_tm m hw hm)
          (hasTy_unsubst_tm n hw hn)
  | .add v u, _, _, _, _, _, hw, h => by
      rw [Tm.subst] at h
      cases h with
      | add hv hu =>
        exact .add (hasTy_unsubst_val v hw hv) (hasTy_unsubst_val u hw hu)
  | .errD _, _, _, _, _, _, _, h => by
      rw [Tm.subst] at h
      cases h with | errD hg => exact .errD hg
end

/-! ## Typings of closed terms in arbitrary contexts -/


/-- The type of a closed raw value does not depend on the context (pad the
empty context and use determinism of typing). -/
theorem hasTy_closed_det_raw {u : Raw} {Γ : List FTy} {σ σ' : FTy}
    (h : HasTyRaw [] u σ) (h' : HasTyRaw Γ u σ') : σ = σ' :=
  det_raw (hasTy_pad_raw u Γ h) h'

/-- The type of a closed term does not depend on the context. -/
theorem hasTy_closed_det_tm {m : Tm} {Γ : List FTy} {D D' : FDist}
    (h : HasTyT [] m D) (h' : HasTyT Γ m D') : D = D' :=
  det_tm (hasTy_pad_tm m Γ h) h'


/-! ## Lemma 44: weakening (renaming) preserves precision

Renaming at position `|Δ|` is weakening: it inserts a type into both contexts
at that position. The premises of the rules that quantify over typings of a
subterm are transported by inverting the typing of the renamed subterm
(`hasTy_unrename_*`).

The contexts are variables whose shape is given by hypotheses
(`Γ1 = Δ ++ Γ`), so that the recursion can match on the precision
derivation: as an index of an inductive, `Δ ++ Γ` is not a variable. The
recursion is structural on the derivation. -/

mutual
/-- Renaming at position `|Δ|` preserves the precision of raw values, inserting
the types `τ` and `τ'` at that position of the two contexts. -/
theorem prec_rename_raw : ∀ {Γ1 Γ2 : List FTy} {u u' : Raw},
    PrecRaw Γ1 Γ2 u u' → ∀ {Δ Γ Δ' Γ' : List FTy} {τ τ' : FTy},
    Γ1 = Δ ++ Γ → Γ2 = Δ' ++ Γ' → Δ.length = Δ'.length →
    PrecRaw (Δ ++ τ :: Γ) (Δ' ++ τ' :: Γ')
      (u.rename Δ.length) (u'.rename Δ.length)
  | _, _, _, _, .real, _, _, _, _, _, _, _, _, _ => by
      simp only [Raw.rename]; exact .real
  | _, _, _, _, .bool, _, _, _, _, _, _, _, _, _ => by
      simp only [Raw.rename]; exact .bool
  | _, _, _, _, .lam (σ := σ0) (σ' := σ0') hσ hm, Δ, Γ, Δ', Γ', τ, τ',
      h1, h2, hlen => by
      simp only [Raw.rename]
      refine .lam hσ ?_
      have hlen2 : (σ0 :: Δ).length = (σ0' :: Δ').length := by simp [hlen]
      have h := prec_rename_tm hm (Δ := σ0 :: Δ) (Γ := Γ) (Δ' := σ0' :: Δ') (Γ' := Γ')
        (τ := τ) (τ' := τ') (by simp [h1]) (by simp [h2]) hlen2
      simpa using h
  termination_by structural Γ1 Γ2 u u' h => h
/-- Lemma 44 (weakening preserves precision), values: if `Δ ++ Γ ⊑ Δ' ++ Γ' ⊢
v ⊑ v'` with `|Δ| = |Δ'|`, then the values renamed at position `|Δ|` are
related under `Δ ++ τ :: Γ` and `Δ' ++ τ' :: Γ'`. -/
theorem prec_rename_val : ∀ {Γ1 Γ2 : List FTy} {v v' : Val},
    Γ1 ⊑ Γ2 ⊢ v ⊑ v' → ∀ {Δ Γ Δ' Γ' : List FTy} {τ τ' : FTy},
    Γ1 = Δ ++ Γ → Γ2 = Δ' ++ Γ' → Δ.length = Δ'.length →
    Δ ++ τ :: Γ ⊑ Δ' ++ τ' :: Γ' ⊢ v.rename Δ.length ⊑ v'.rename Δ.length
  | _, _, _, _, .var, _, _, _, _, _, _, _, _, _ => by
      simp only [Val.rename]; exact .var
  | Γ1, Γ2, _, _, .asc (u := u0) (u' := u0') hε hεL hu hσ, Δ, Γ, Δ', Γ', τ, τ',
      h1, h2, hlen => by
      simp only [Val.rename]
      refine .asc hε ?_ (prec_rename_raw hu h1 h2 hlen) hσ
      intro σv σv' hty hty'
      have hty2 : HasTyRaw Γ2 u0' σv' := by
        have h := hasTy_unrename_raw u0' (Δ := Δ') (Γ := Γ') (τ := τ') (σ := σv')
        rw [← hlen] at h
        rw [h2]; exact h hty'
      exact hεL (by rw [h1]; exact hasTy_unrename_raw u0 hty) hty2
  | _, _, _, _, .errV (v' := v0') hty hσ, Δ, Γ, Δ', Γ', τ, τ', h1, h2, hlen => by
      subst h1; subst h2
      simp only [Val.rename]
      refine .errV ?_ hσ
      have h := hasTy_wk_val v0' (Δ := Δ') (Γ := Γ') (τ := τ') hty
      rw [← hlen] at h
      exact h
  termination_by structural Γ1 Γ2 v v' h => h
/-- Lemma 44 (weakening preserves precision), terms: if `Δ ++ Γ ⊑ Δ' ++ Γ' ⊢
m ⊑ m'` with `|Δ| = |Δ'|`, then the terms renamed at position `|Δ|` are
related under `Δ ++ τ :: Γ` and `Δ' ++ τ' :: Γ'`. -/
theorem prec_rename_tm : ∀ {Γ1 Γ2 : List FTy} {m m' : Tm},
    Γ1 ⊑ Γ2 ⊢ m ⊑ m' → ∀ {Δ Γ Δ' Γ' : List FTy} {τ τ' : FTy},
    Γ1 = Δ ++ Γ → Γ2 = Δ' ++ Γ' → Δ.length = Δ'.length →
    Δ ++ τ :: Γ ⊑ Δ' ++ τ' :: Γ' ⊢ m.rename Δ.length ⊑ m'.rename Δ.length
  | _, _, _, _, .val hv, _, _, _, _, _, _, h1, h2, hlen => by
      simp only [Tm.rename]
      exact .val (prec_rename_val hv h1 h2 hlen)
  | _, _, _, _, .app hv hw, _, _, _, _, _, _, h1, h2, hlen => by
      simp only [Tm.rename]
      exact .app (prec_rename_val hv h1 h2 hlen)
        (prec_rename_val hw h1 h2 hlen)
  | Γ1, Γ2, _, _, @PrecT.letin _ _ m0 m0' _ _ ns ns' hm hbody hcoup,
      Δ, Γ, Δ', Γ', τ, τ', h1, h2, hlen => by
      rw [Tm.rename_letin, Tm.rename_letin]
      have hty1 : ∀ {D : FDist}, HasTyT (Δ ++ τ :: Γ) (m0.rename Δ.length) D →
          HasTyT Γ1 m0 D := fun hty => by rw [h1]; exact hasTy_unrename_tm m0 hty
      have hty2 : ∀ {D' : FDist}, HasTyT (Δ' ++ τ' :: Γ') (m0'.rename Δ.length) D' →
          HasTyT Γ2 m0' D' := by
        intro D' hty'
        have h := hasTy_unrename_tm m0' (Δ := Δ') (Γ := Γ') (τ := τ') (D := D')
        rw [← hlen] at h
        rw [h2]; exact h hty'
      refine .letin (prec_rename_tm hm h1 h2 hlen) ?_ ?_
      · intro D D' hty hty' i j hij hilen hjlen
        have hlen2 : (D.ty i :: Δ).length = (D'.ty j :: Δ').length := by
          simp [hlen]
        have h := prec_rename_tm (hbody (hty1 hty) (hty2 hty') i j hij hilen hjlen)
          (Δ := D.ty i :: Δ) (Γ := Γ) (Δ' := D'.ty j :: Δ') (Γ' := Γ') (τ := τ) (τ' := τ')
          (by simp [h1]) (by simp [h2]) hlen2
        simpa using h
      · intro D D' hty hty'
        exact hcoup (hty1 hty) (hty2 hty')
  | _, _, _, _, .choice hp hm hn, _, _, _, _, _, _, h1, h2, hlen => by
      simp only [Tm.rename]
      exact .choice hp (prec_rename_tm hm h1 h2 hlen)
        (prec_rename_tm hn h1 h2 hlen)
  | Γ1, Γ2, _, _, .ascT (m := m0) (n := m0') hε hεL hm hγ, Δ, Γ, Δ', Γ', τ, τ',
      h1, h2, hlen => by
      simp only [Tm.rename]
      have hty1 : ∀ {D : FDist}, HasTyT (Δ ++ τ :: Γ) (m0.rename Δ.length) D →
          HasTyT Γ1 m0 D := fun hty => by rw [h1]; exact hasTy_unrename_tm m0 hty
      have hty2 : ∀ {D' : FDist}, HasTyT (Δ' ++ τ' :: Γ') (m0'.rename Δ.length) D' →
          HasTyT Γ2 m0' D' := by
        intro D' hty'
        have h := hasTy_unrename_tm m0' (Δ := Δ') (Γ := Γ') (τ := τ') (D := D')
        rw [← hlen] at h
        rw [h2]; exact h hty'
      refine .ascT ?_ ?_ (prec_rename_tm hm h1 h2 hlen) hγ
      · intro D D' hty hty'
        exact hε (hty1 hty) (hty2 hty')
      · intro D D' hty hty'
        exact hεL (hty1 hty) (hty2 hty')
  | Γ1, Γ2, _, _, .ascV (v := v0) (v' := v0') hε hεL hv hσ, Δ, Γ, Δ', Γ', τ, τ',
      h1, h2, hlen => by
      simp only [Tm.rename]
      refine .ascV hε ?_ (prec_rename_val hv h1 h2 hlen) hσ
      intro σv σv' hty hty'
      have hty2 : HasTyV Γ2 v0' σv' := by
        have h := hasTy_unrename_val v0' (Δ := Δ') (Γ := Γ') (τ := τ') (σ := σv')
        rw [← hlen] at h
        rw [h2]; exact h hty'
      exact hεL (by rw [h1]; exact hasTy_unrename_val v0 hty) hty2
  | _, _, _, _, .ite hv hm hn, _, _, _, _, _, _, h1, h2, hlen => by
      simp only [Tm.rename]
      exact .ite (prec_rename_val hv h1 h2 hlen) (prec_rename_tm hm h1 h2 hlen)
        (prec_rename_tm hn h1 h2 hlen)
  | _, _, _, _, .add hv hw, _, _, _, _, _, _, h1, h2, hlen => by
      simp only [Tm.rename]
      exact .add (prec_rename_val hv h1 h2 hlen)
        (prec_rename_val hw h1 h2 hlen)
  | _, _, _, _, .errD hγ, _, _, _, _, _, _, _, _, _ => by
      simp only [Tm.rename]
      exact .errD hγ
  termination_by structural Γ1 Γ2 m m' h => h
end

/-! ## Substitution of related values preserves precision

Substituting a value at position `|Δ|` removes that type from both contexts.
The premises that quantify over typings of a subterm are transported by
inverting the typing of the substituted subterm (`hasTy_unsubst_*`). -/

mutual
/-- Substituting related values `w ⊑ w'`, typed at `τ` and `τ'`, at position
`|Δ|` preserves the precision of raw values, removing `τ` and `τ'` from the
two contexts. -/
theorem prec_subst_raw : ∀ {Γ1 Γ2 : List FTy} {u u' : Raw},
    PrecRaw Γ1 Γ2 u u' → ∀ {Δ Γ Δ' Γ' : List FTy} {τ τ' : FTy}
      {w w' : Val}, Γ1 = Δ ++ τ :: Γ → Γ2 = Δ' ++ τ' :: Γ' →
    Δ.length = Δ'.length → PrecV (Δ ++ Γ) (Δ' ++ Γ') w w' →
    HasTyV (Δ ++ Γ) w τ → HasTyV (Δ' ++ Γ') w' τ' →
    PrecRaw (Δ ++ Γ) (Δ' ++ Γ')
      (u.subst Δ.length w) (u'.subst Δ.length w')
  | _, _, _, _, .real, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
      simp only [Raw.subst]; exact .real
  | _, _, _, _, .bool, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
      simp only [Raw.subst]; exact .bool
  | _, _, _, _, .lam (σ := σ0) (σ' := σ0') hσ hm, Δ, Γ, Δ', Γ', τ, τ', w, w',
      h1, h2, hlen, hww', hw, hw' => by
      simp only [Raw.subst]
      refine .lam hσ ?_
      have hlen2 : (σ0 :: Δ).length = (σ0' :: Δ').length := by simp [hlen]
      have hwr := prec_rename_val hww' (Δ := ([] : List FTy)) (Δ' := [])
        (τ := σ0) (τ' := σ0') rfl rfl rfl
      have hwt : HasTyV (σ0 :: (Δ ++ Γ)) (w.rename 0) τ := by
        have h := hasTy_wk_val w (Δ := ([] : List FTy)) (τ := σ0) hw
        simpa using h
      have hwt' : HasTyV (σ0' :: (Δ' ++ Γ')) (w'.rename 0) τ' := by
        have h := hasTy_wk_val w' (Δ := ([] : List FTy)) (τ := σ0') hw'
        simpa using h
      have h := prec_subst_tm hm (Δ := σ0 :: Δ) (Γ := Γ) (Δ' := σ0' :: Δ') (Γ' := Γ')
        (τ := τ) (τ' := τ') (by simp [h1]) (by simp [h2]) hlen2 (by simpa using hwr)
        (by simpa using hwt) (by simpa using hwt')
      simpa using h
  termination_by structural Γ1 Γ2 u u' h => h
/-- Substituting related values `w ⊑ w'`, typed at `τ` and `τ'`, at position
`|Δ|` preserves value precision, removing `τ` and `τ'` from the two
contexts. -/
theorem prec_subst_val : ∀ {Γ1 Γ2 : List FTy} {v v' : Val},
    PrecV Γ1 Γ2 v v' → ∀ {Δ Γ Δ' Γ' : List FTy} {τ τ' : FTy}
      {w w' : Val}, Γ1 = Δ ++ τ :: Γ → Γ2 = Δ' ++ τ' :: Γ' →
    Δ.length = Δ'.length → PrecV (Δ ++ Γ) (Δ' ++ Γ') w w' →
    HasTyV (Δ ++ Γ) w τ → HasTyV (Δ' ++ Γ') w' τ' →
    PrecV (Δ ++ Γ) (Δ' ++ Γ')
      (v.subst Δ.length w) (v'.subst Δ.length w')
  | _, _, _, _, @PrecV.var _ _ x, Δ, Γ, Δ', Γ', τ, τ', w, w',
      h1, h2, hlen, hww', hw, hw' => by
      subst h1; subst h2
      simp only [Val.subst]
      by_cases hx : x = Δ.length
      · rw [if_pos hx, if_pos hx]
        exact hww'
      · rw [if_neg hx, if_neg hx]
        by_cases hx2 : x > Δ.length
        · rw [if_pos hx2]; exact .var
        · rw [if_neg hx2]; exact .var
  | Γ1, Γ2, _, _, .asc (u := u0) (u' := u0') hε hεL hu hσ, Δ, Γ, Δ', Γ', τ, τ',
      w, w', h1, h2, hlen, hww', hw, hw' => by
      simp only [Val.subst]
      refine .asc hε ?_ (prec_subst_raw hu h1 h2 hlen hww' hw hw') hσ
      intro σv σv' hty hty'
      have hty2 : HasTyRaw Γ2 u0' σv' := by
        have h : HasTyRaw (Δ' ++ Γ') (u0'.subst Δ'.length w') σv' := by
          rw [← hlen]; exact hty'
        rw [h2]; exact hasTy_unsubst_raw u0' hw' h
      exact hεL (by rw [h1]; exact hasTy_unsubst_raw u0 hw hty) hty2
  | _, _, _, _, .errV (v' := v0') hty hσ, Δ, Γ, Δ', Γ', τ, τ', w, w',
      h1, h2, hlen, hww', hw, hw' => by
      subst h1; subst h2
      simp only [Val.subst]
      refine .errV ?_ hσ
      have h := hasTy_subst_val v0' (Δ := Δ') (Γ := Γ') (τ := τ') hw' hty
      rw [hlen]
      exact h
  termination_by structural Γ1 Γ2 v v' h => h
/-- Lemma 43 (substitution preserves precision), at an arbitrary position:
substituting related values `w ⊑ w'`, typed at `τ` and `τ'`, at position
`|Δ|` preserves term precision, removing `τ` and `τ'` from the two
contexts. -/
theorem prec_subst_tm : ∀ {Γ1 Γ2 : List FTy} {m m' : Tm},
    PrecT Γ1 Γ2 m m' → ∀ {Δ Γ Δ' Γ' : List FTy} {τ τ' : FTy}
      {w w' : Val}, Γ1 = Δ ++ τ :: Γ → Γ2 = Δ' ++ τ' :: Γ' →
    Δ.length = Δ'.length → PrecV (Δ ++ Γ) (Δ' ++ Γ') w w' →
    HasTyV (Δ ++ Γ) w τ → HasTyV (Δ' ++ Γ') w' τ' →
    PrecT (Δ ++ Γ) (Δ' ++ Γ')
      (m.subst Δ.length w) (m'.subst Δ.length w')
  | _, _, _, _, .val hv, _, _, _, _, _, _, _, _, h1, h2, hlen, hww', hw, hw' => by
      simp only [Tm.subst]
      exact .val (prec_subst_val hv h1 h2 hlen hww' hw hw')
  | _, _, _, _, .app hv hu, _, _, _, _, _, _, _, _,
      h1, h2, hlen, hww', hw, hw' => by
      simp only [Tm.subst]
      exact .app (prec_subst_val hv h1 h2 hlen hww' hw hw')
        (prec_subst_val hu h1 h2 hlen hww' hw hw')
  | Γ1, Γ2, _, _, @PrecT.letin _ _ m0 m0' _ _ ns ns' hm hbody hcoup,
      Δ, Γ, Δ', Γ', τ, τ', w, w', h1, h2, hlen, hww', hw, hw' => by
      rw [Tm.subst_letin, Tm.subst_letin]
      have hty1 : ∀ {D : FDist}, HasTyT (Δ ++ Γ) (m0.subst Δ.length w) D →
          HasTyT Γ1 m0 D := fun hty => by rw [h1]; exact hasTy_unsubst_tm m0 hw hty
      have hty2 : ∀ {D' : FDist}, HasTyT (Δ' ++ Γ') (m0'.subst Δ.length w') D' →
          HasTyT Γ2 m0' D' := by
        intro D' hty'
        have h : HasTyT (Δ' ++ Γ') (m0'.subst Δ'.length w') D' := by
          rw [← hlen]; exact hty'
        rw [h2]; exact hasTy_unsubst_tm m0' hw' h
      refine .letin (prec_subst_tm hm h1 h2 hlen hww' hw hw') ?_ ?_
      · intro D D' hty hty' i j hij hilen hjlen
        have hlen2 : (D.ty i :: Δ).length = (D'.ty j :: Δ').length := by
          simp [hlen]
        have hwr := prec_rename_val hww' (Δ := ([] : List FTy)) (Δ' := [])
          (τ := D.ty i) (τ' := D'.ty j) rfl rfl rfl
        have hwt : HasTyV (D.ty i :: (Δ ++ Γ)) (w.rename 0) τ := by
          have h := hasTy_wk_val w (Δ := ([] : List FTy)) (τ := D.ty i) hw
          simpa using h
        have hwt' : HasTyV (D'.ty j :: (Δ' ++ Γ')) (w'.rename 0) τ' := by
          have h := hasTy_wk_val w' (Δ := ([] : List FTy)) (τ := D'.ty j) hw'
          simpa using h
        have h := prec_subst_tm (hbody (hty1 hty) (hty2 hty') i j hij hilen hjlen)
          (Δ := D.ty i :: Δ) (Γ := Γ) (Δ' := D'.ty j :: Δ') (Γ' := Γ')
          (τ := τ) (τ' := τ') (by simp [h1]) (by simp [h2]) hlen2 (by simpa using hwr)
          (by simpa using hwt) (by simpa using hwt')
        simpa using h
      · intro D D' hty hty'
        exact hcoup (hty1 hty) (hty2 hty')
  | _, _, _, _, .choice hp hm hn, _, _, _, _, _, _, _, _,
      h1, h2, hlen, hww', hw, hw' => by
      simp only [Tm.subst]
      exact .choice hp (prec_subst_tm hm h1 h2 hlen hww' hw hw')
        (prec_subst_tm hn h1 h2 hlen hww' hw hw')
  | Γ1, Γ2, _, _, .ascT (m := m0) (n := m0') hε hεL hm hγ, Δ, Γ, Δ', Γ', τ, τ',
      w, w', h1, h2, hlen, hww', hw, hw' => by
      simp only [Tm.subst]
      have hty1 : ∀ {D : FDist}, HasTyT (Δ ++ Γ) (m0.subst Δ.length w) D →
          HasTyT Γ1 m0 D := fun hty => by rw [h1]; exact hasTy_unsubst_tm m0 hw hty
      have hty2 : ∀ {D' : FDist}, HasTyT (Δ' ++ Γ') (m0'.subst Δ.length w') D' →
          HasTyT Γ2 m0' D' := by
        intro D' hty'
        have h : HasTyT (Δ' ++ Γ') (m0'.subst Δ'.length w') D' := by
          rw [← hlen]; exact hty'
        rw [h2]; exact hasTy_unsubst_tm m0' hw' h
      refine .ascT ?_ ?_ (prec_subst_tm hm h1 h2 hlen hww' hw hw') hγ
      · intro D D' hty hty'
        exact hε (hty1 hty) (hty2 hty')
      · intro D D' hty hty'
        exact hεL (hty1 hty) (hty2 hty')
  | Γ1, Γ2, _, _, .ascV (v := v0) (v' := v0') hε hεL hv hσ, Δ, Γ, Δ', Γ', τ, τ',
      w, w', h1, h2, hlen, hww', hw, hw' => by
      simp only [Tm.subst]
      refine .ascV hε ?_ (prec_subst_val hv h1 h2 hlen hww' hw hw') hσ
      intro σv σv' hty hty'
      have hty2 : HasTyV Γ2 v0' σv' := by
        have h : HasTyV (Δ' ++ Γ') (v0'.subst Δ'.length w') σv' := by
          rw [← hlen]; exact hty'
        rw [h2]; exact hasTy_unsubst_val v0' hw' h
      exact hεL (by rw [h1]; exact hasTy_unsubst_val v0 hw hty) hty2
  | _, _, _, _, .ite hv hm hn, _, _, _, _, _, _, _, _,
      h1, h2, hlen, hww', hw, hw' => by
      simp only [Tm.subst]
      exact .ite (prec_subst_val hv h1 h2 hlen hww' hw hw')
        (prec_subst_tm hm h1 h2 hlen hww' hw hw')
        (prec_subst_tm hn h1 h2 hlen hww' hw hw')
  | _, _, _, _, .add hv hu, _, _, _, _, _, _, _, _,
      h1, h2, hlen, hww', hw, hw' => by
      simp only [Tm.subst]
      exact .add (prec_subst_val hv h1 h2 hlen hww' hw hw')
        (prec_subst_val hu h1 h2 hlen hww' hw hw')
  | _, _, _, _, .errD hγ, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
      simp only [Tm.subst]
      exact .errD hγ
  termination_by structural Γ1 Γ2 m m' h => h
end

/-! ## Lemma 43: substitution preserves precision -/

/-- Lemma 43 (substitution preserves precision), for ordinary substitution:
substitution of closed, related, well-typed values at index 0 preserves
precision, the form used by the `let` and application cases of the dynamic
gradual guarantee. -/
theorem prec_subst0 {m m' : Tm} {w w' : Val} {τ τ' : FTy}
    (h : [τ] ⊑ [τ'] ⊢ m ⊑ m') (hww' : w ⊑ w')
    (hw : ⊢ w : τ) (hw' : ⊢ w' : τ') :
    m.subst0 w ⊑ m'.subst0 w' := by
  have h0 := prec_subst_tm h (Δ := ([] : List FTy)) (Γ := ([] : List FTy))
    (Δ' := ([] : List FTy)) (Γ' := ([] : List FTy)) (τ := τ) (τ' := τ')
    rfl rfl rfl hww' hw hw'
  simpa [Tm.subst0] using h0

/-- Lemma 43 (substitution preserves precision), with the function `sub` of
the article (`Tm.subErr`). The substituted values are not errors (they are
ascriptions `ε u :: σ`), so `sub` is ordinary substitution and the lemma
follows from `prec_subst0`. -/
theorem subep_noerr {m m' : Tm} {τ τ' : FTy} {ε ε' : TagTy} {u u' : Raw}
    {σ σ' : FTy} {γ γ' : FDist}
    (h : [τ] ⊑ [τ'] ⊢ m ⊑ m')
    (hww' : .asc ε u σ ⊑ .asc ε' u' σ')
    (hw : ⊢ .asc ε u σ : τ) (hw' : ⊢ .asc ε' u' σ' : τ') :
    m.subErr (.asc ε u σ) γ ⊑ m'.subErr (.asc ε' u' σ') γ' := by
  simp only [Tm.subErr_asc]
  exact prec_subst0 h hww' hw hw'

/-! ## Monotonicity of the reduction in its derivation index -/

/-- The big-step reduction is monotone in its derivation index (iterated
rule `dmon`); used to bring the reductions of several `let` bodies to a
common index. -/
theorem red_index_mono {n : Tm} {k : ℕ} {V : DConf} (h : Red n k V) :
    ∀ {k' : ℕ}, k ≤ k' → Red n k' V := by
  intro k' hle
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction d with
  | zero => exact h
  | succ d ih => exact Red.dmon ih

end GradualProb.TPLC
