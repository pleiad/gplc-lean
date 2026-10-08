import GradualProb.TPLC.Meet

/-!
# Elaboration from GPLC to TPLC

This module formalizes the elaboration of Figure 16 (Section 5.4) and
Lemma 11 (elaboration preserves types). Since GPLC is already typed with
formula types, a GPLC term typed `D` elaborates to a TPLC term typed at the
same formula type `D`. The elaboration inserts ascriptions with evidence at
the consistency points, each evidence set to the meet of the judged types,
and puts application, addition and the conditional in A-normal form: an
operand to be coerced is bound by a `let`, since a value ascription is a term.

## Main results

* `elaboration_preserves_types`, `elaboration_preserves_types_val`:
  Lemma 11 (elaboration preserves types), from the existence half
  `elab_exists_val`/`elab_exists_tm` and the preservation half
  `elab_preserves_val`/`elab_preserves_tm`.
* `elaboration_preserves_types_closed`: the closed form used by Theorem 4.
* `elab_sound_val`, `elab_sound_tm`: Lemma 51 (elaboration implies typing).
* `hasTy_wk0_val`, `hasTy_wk_tm`, `hasTy_letin1`: Lemma 33 (weakening and
  single-entry lets).

## Reading guide

The first section collects auxiliary facts for the A-normal forms: the
collapse of a `let` over a Dirac bound term (`letSem_point`) and weakening of
TPLC typing (`hasTy_wk_tm`). Then come the elaboration relation and the
results.
-/

namespace GradualProb.TPLC

open GradualProb.GPLC

open scoped BigOperators

/-! ## Auxiliary facts for the A-normal forms

* `letSem_point`: a `let` over a Dirac bound term collapses,
  `letSem {σ^1} F = F 0`, so each A-normal binding types at its body's type.
* `hasTy_wk0_tm`/`hasTy_wk0_val`: weakening of TPLC typing by one binder at
  the front, from the general `hasTy_wk_tm`/`hasTy_wk_val`. -/

/-- On a singleton index set, `finSigmaFinEquiv.symm` keeps the value of the
index. -/
theorem symm_snd_val (F : Fin 1 → FDist) (k : Fin (∑ i : Fin 1, (F i).n)) :
    ((finSigmaFinEquiv.symm k).2 : ℕ) = (k : ℕ) := by
  have happ := finSigmaFinEquiv_one (n := fun i : Fin 1 => (F i).n) (finSigmaFinEquiv.symm k)
  rw [Equiv.apply_symm_apply] at happ
  omega

/-- Entries of a family indexed by `Fin 1` at equal positions coincide. -/
theorem ty_at_one (F : Fin 1 → FDist) (a : Fin 1) (j : Fin (F a).n)
    (j0 : Fin (F 0).n) (h : (j : ℕ) = (j0 : ℕ)) : (F a).ty j = (F 0).ty j0 := by
  have ha : a = 0 := Subsingleton.elim a 0
  subst ha
  congr 1
  exact Fin.ext h

/-- Values of a family indexed by `Fin 1` at equal positions coincide. -/
theorem b_at_one (F : Fin 1 → FDist) (b : (i : Fin 1) → Fin (F i).n → ℝ) (a : Fin 1)
    (j : Fin (F a).n) (j0 : Fin (F 0).n) (h : (j : ℕ) = (j0 : ℕ)) : b a j = b 0 j0 := by
  have ha : a = 0 := Subsingleton.elim a 0
  subst ha
  congr 1
  exact Fin.ext h

/-- A `let` over the Dirac type `{σ^1}` collapses to its only branch. -/
theorem letSem_point (σ : FTy) (F : Fin (pointF σ).n → FDist) :
    letSem (pointF σ) F = F 0 := by
  have hn : (letSem (pointF σ) F).n = (F 0).n := by
    show (∑ i : Fin 1, (F i).n) = (F 0).n
    simp
  refine FDist.ext hn ?_ ?_
  · intro i
    exact ty_at_one F _ _ _ (by rw [symm_snd_val]; rfl)
  · intro p
    constructor
    · rintro ⟨p', hp'1, b, hb, hk⟩
      have hpeq : p = b 0 := by
        funext j
        have hk0 := hk (Fin.cast hn.symm j)
        simp only [] at hk0
        have e1 : Fin.cast hn (Fin.cast hn.symm j) = j := Fin.ext (by simp)
        rw [e1] at hk0
        have hp1 : p' (finSigmaFinEquiv.symm (Fin.cast hn.symm j)).1 = 1 := by
          rw [Subsingleton.elim (finSigmaFinEquiv.symm (Fin.cast hn.symm j)).1 0]; exact hp'1
        rw [hk0, hp1, one_mul]
        exact b_at_one F b _ _ j (by rw [symm_snd_val]; simp)
      rw [hpeq]; exact hb 0
    · intro hp
      refine ⟨fun _ => 1, rfl,
        fun i => fun x => p (Fin.cast (by rw [Subsingleton.elim i 0]) x), ?_, ?_⟩
      · intro i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        simpa using hp
      · intro k
        have h1 : (finSigmaFinEquiv.symm k).1 = 0 := Subsingleton.elim _ _
        show p (Fin.cast hn k)
            = (1 : ℝ) * p (Fin.cast _ (finSigmaFinEquiv.symm k).2)
        rw [one_mul]
        apply congrArg p
        apply Fin.ext
        simp only [Fin.coe_cast]
        rw [symm_snd_val]




/-- Lookup in an environment with one type inserted, at the renamed index. -/
theorem getElem?_insert {α} (Δ Γ : List α) (τ : α) (x : ℕ) :
    (Δ ++ τ :: Γ)[(if x < Δ.length then x else x + 1)]? = (Δ ++ Γ)[x]? := by
  by_cases h : x < Δ.length
  · simp only [if_pos h]
    rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · simp only [if_neg h]
    push_neg at h
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right h]
    have : x + 1 - Δ.length = (x - Δ.length) + 1 := by omega
    rw [this, List.getElem?_cons_succ]

mutual
/-- Weakening of raw-value typing: inserting a type in the environment. -/
theorem hasTy_wk_raw : ∀ (u : Raw) {Δ Γ : List FTy} {σ τ : FTy},
    HasTyRaw (Δ ++ Γ) u σ → HasTyRaw (Δ ++ τ :: Γ) (u.rename Δ.length) σ
  | .real _, _, _, _, _, h => by cases h; rw [Raw.rename]; exact .real
  | .bool _, _, _, _, _, h => by cases h; rw [Raw.rename]; exact .bool
  | .lam σ0 body, Δ, _, _, τ, h => by
      cases h with
      | lam hbody hg =>
        rw [Raw.rename]
        have ih := hasTy_wk_tm body (Δ := σ0 :: Δ) (τ := τ) hbody
        simp only [List.cons_append, List.length_cons] at ih
        exact .lam ih hg
/-- Weakening of value typing. -/
theorem hasTy_wk_val : ∀ (v : Val) {Δ Γ : List FTy} {σ τ : FTy},
    HasTyV (Δ ++ Γ) v σ → HasTyV (Δ ++ τ :: Γ) (v.rename Δ.length) σ
  | .var _, _, _, _, _, h => by
      cases h with
      | var hx => rw [Val.rename]; exact .var (by rw [getElem?_insert]; exact hx)
  | .asc _ u _, _, _, _, _, h => by
      cases h with
      | ascRaw hu hev hge hg => rw [Val.rename]; exact .ascRaw (hasTy_wk_raw u hu) hev hge hg
  | .err _, _, _, _, _, h => by
      cases h with | err hg => rw [Val.rename]; exact .err hg
/-- Lemma 33 (weakening and single-entry lets), terms: inserting a type in
the environment preserves term typing (the term is renamed accordingly). -/
theorem hasTy_wk_tm : ∀ (m : Tm) {Δ Γ : List FTy} {D : FDist} {τ : FTy},
    Δ ++ Γ ⊢ m : D → Δ ++ τ :: Γ ⊢ m.rename Δ.length : D
  | .val v, _, _, _, _, h => by
      cases h with | val hv => rw [Tm.rename]; exact .val (hasTy_wk_val v hv)
  | .app v w, _, _, _, _, h => by
      cases h with
      | app hv hw => rw [Tm.rename]; exact .app (hasTy_wk_val v hv) (hasTy_wk_val w hw)
  | .letin mm _ ns, Δ, _, _, τ, h => by
      cases h with
      | @letin _ _ _ ty _ _ F hm hbody =>
        rw [Tm.rename_letin]
        refine .letin (hasTy_wk_tm mm hm) (fun i => ?_)
        have ih := hasTy_wk_tm (ns i) (Δ := ty i :: Δ) (τ := τ) (hbody i)
        simp only [List.cons_append, List.length_cons] at ih
        exact ih
  | .choice _ m n, _, _, _, _, h => by
      cases h with
      | choice ha0 ha1 hm hn =>
        rw [Tm.rename]; exact .choice ha0 ha1 (hasTy_wk_tm m hm) (hasTy_wk_tm n hn)
      | choiceU hm hn =>
        rw [Tm.rename]; exact .choiceU (hasTy_wk_tm m hm) (hasTy_wk_tm n hn)
  | .ascT _ m _, _, _, _, _, h => by
      cases h with
      | ascT hm hev hge hg => rw [Tm.rename]; exact .ascT (hasTy_wk_tm m hm) hev hge hg
  | .ascV _ v _, _, _, _, _, h => by
      cases h with
      | ascV hv hev hge hg => rw [Tm.rename]; exact .ascV (hasTy_wk_val v hv) hev hge hg
  | .ite v m n, _, _, _, _, h => by
      cases h with
      | ite hv hm hn =>
        rw [Tm.rename]
        exact .ite (hasTy_wk_val v hv) (hasTy_wk_tm m hm) (hasTy_wk_tm n hn)
  | .add v w, _, _, _, _, h => by
      cases h with
      | add hv hw => rw [Tm.rename]; exact .add (hasTy_wk_val v hv) (hasTy_wk_val w hw)
  | .errD _, _, _, _, _, h => by
      cases h with | errD hg => rw [Tm.rename]; exact .errD hg
end

/-- Lemma 33 (weakening and single-entry lets), values: if `Γ ⊢ v : σ`, then
`τ :: Γ ⊢ v : σ`, with `v` renamed past the new binder. -/
theorem hasTy_wk0_val {Γ : List FTy} {v : Val} {σ τ : FTy} (h : Γ ⊢ v : σ) :
    τ :: Γ ⊢ v.rename 0 : σ :=
  hasTy_wk_val v (Δ := []) h

/-- Weakening of term typing by one binder at the front. -/
theorem hasTy_wk0_tm {Γ : List FTy} {m : Tm} {D : FDist} {τ : FTy}
    (h : HasTyT Γ m D) : HasTyT (τ :: Γ) (m.rename 0) D :=
  hasTy_wk_tm m (Δ := []) h

/-- Lemma 33 (weakening and single-entry lets), single-entry lets: if the
bound term has the Dirac type `pointF σ` and the body has type `D` under
`σ :: Γ`, then the single-entry `let` has type `D`. Each A-normal binding of
the elaboration is such a `let`. -/
theorem hasTy_letin1 {Γ : List FTy} {m : Tm} {σ : FTy} {body : Tm} {D : FDist}
    (hs : Γ ⊢ m : pointF σ) (hb : σ :: Γ ⊢ body : D) :
    Γ ⊢ .letin m 1 (fun _ => body) : D := by
  have h : HasTyT Γ (.letin m 1 (fun _ => body)) (letSem (pointF σ) (fun _ => D)) :=
    HasTyT.letin hs (fun _ => hb)
  rwa [letSem_point] at h

/-- The domain and codomain of a well-formed type are well-formed. -/
theorem domcod_good {σ s : FTy} {D : FDist} (hdc : DomCod σ s D) (hg : GoodTy σ) :
    GoodTy s ∧ GoodD D := by
  cases hdc with
  | arrow => cases hg with | arrow hs hD => exact ⟨hs, hD⟩
  | unk => exact ⟨.unk, goodD_topF⟩


/-- A well-formed `σ` is consistent with the arrow `dom(σ) → cod(σ)`, the
judgment of the function's coercion in rule (Eapp). -/
theorem domcod_cons {σ s : FTy} {D : FDist} (hdc : DomCod σ s D)
    (hg : GoodTy σ) : ConsTy σ (.arrow s D) := by
  cases hdc with
  | arrow => exact ConsTy.refl hg
  | unk => exact .unkL



/-! ## The elaboration relation (Figure 16)

`ElabV Γ v tv σ`: the GPLC value `v`, typed `σ` under `Γ`, elaborates to the
TPLC value `tv`. `ElabT Γ m tm D`: the GPLC term `m`, typed `D`, elaborates to
the TPLC term `tm`. The rules mirror the typing rules of GPLC premise by
premise, and every evidence is the meet of the judged types (`tagMeetTy`,
`tagMeetD`), so the elaboration is determined by the typing derivation. -/

mutual
/-- Elaboration of values (Figure 16). -/
inductive ElabV : List FTy → GPLC.Val → Val → FTy → Prop where
  /-- `(Ex)` variables elaborate to themselves. -/
  | evar  : ∀ {Γ x σ}, Γ[x]? = some σ → ElabV Γ (.var x) (.var x) σ
  /-- `(Er)` a real literal is ascribed to `Real` with reflexive evidence. -/
  | ereal : ∀ {Γ r}, ElabV Γ (.real r) (.asc .real (.real r) .real) .real
  /-- `(Eb)` a boolean literal is ascribed to `Bool`. -/
  | ebool : ∀ {Γ b}, ElabV Γ (.bool b) (.asc .bool (.bool b) .bool) .bool
  /-- `(Eλ)` a lambda is ascribed to its (lifted) arrow type, with the
  reflexive **diagonal** tagged evidence (`toTag`, identity tags). -/
  | elam  : ∀ {Γ τ m tm D}, ElabT (liftFTy τ :: Γ) m tm D → WfTy τ →
              ElabV Γ (.lam τ m)
                (.asc (FTy.arrow (liftFTy τ) D).toTag (.lam (liftFTy τ) tm)
                  (.arrow (liftFTy τ) D))
                (.arrow (liftFTy τ) D)
/-- Elaboration of terms (Figure 16). -/
inductive ElabT : List FTy → GPLC.Tm → Tm → FDist → Prop where
  /-- `(Ev)` a value as a term. -/
  | eval    : ∀ {Γ v tv σ}, ElabV Γ v tv σ → ElabT Γ (.val v) (.val tv) (pointF σ)
  /-- `(E⊕)` with a concrete probability — no ascription needed (exact result). -/
  | echoice : ∀ {Γ m tm n tn D1 D2} {a : ℝ}, 0 ≤ a → a ≤ 1 →
                ElabT Γ m tm D1 → ElabT Γ n tn D2 →
                ElabT Γ (.choice (.q a) m n) (.choice (.q a) tm tn)
                  (chooseSem a D1 D2)
  /-- `(E⊕)` with the unknown probability. -/
  | echoiceU : ∀ {Γ m tm n tn D1 D2}, ElabT Γ m tm D1 → ElabT Γ n tn D2 →
                ElabT Γ (.choice .unk m n) (.choice .unk tm tn)
                  (chooseSemU D1 D2)
  /-- `(Elet)`: the body is elaborated once per entry of the bound term's
  type. -/
  | eletin  : ∀ {Γ m tm k} {ty : Fin k → FTy} {C : (Fin k → ℝ) → Prop} {n}
                {tns : Fin k → Tm} {F : Fin k → FDist},
                ElabT Γ m tm ⟨k, ty, C⟩ →
                (∀ i, ElabT (ty i :: Γ) n (tns i) (F i)) →
                ElabT Γ (.letin m n) (.letin tm k tns) (letSem ⟨k, ty, C⟩ F)
  /-- `(E::σ)`: premises as in the GPLC rule (consistency `σ ∼ ⌈τ⌉`); the
  evidence is the meet `σ ⊓ ⌈τ⌉`. -/
  | eascV   : ∀ {Γ v tv σ} {ε : TagTy} {τ}, ElabV Γ v tv σ →
                ConsTy σ (liftFTy τ) → WfTy τ →
                tagMeetTy σ (liftFTy τ) = some ε →
                ElabT Γ (.ascV v τ) (.ascV ε tv (liftFTy τ)) (pointF (liftFTy τ))
  /-- `(E::μ)`: premises as in the GPLC rule; the evidence is the meet
  `D ⊓ ⌈T⌉`. -/
  | eascT   : ∀ {Γ m tm D} {T}, ElabT Γ m tm D →
                ConsD D (liftFDist T) → WfDTy T →
                ElabT Γ (.ascT m T)
                  (.ascT (tagMeetD D (liftFDist T)) tm (liftFDist T))
                  (liftFDist T)
  /-- `(Eapp)` in A-normal form: bind the coerced argument, then the coerced
  function, then apply. Premises as in the GPLC rule (`DomCod` and
  `σ' ∼ dom(σ)`); the evidences are the meets for `σ' ∼ dom(σ)` and
  `σ ∼ dom(σ) → cod(σ)`. The function `tv` is weakened (`rename 0`) under the
  argument's binder. -/
  | eapp    : ∀ {Γ v tv w tw σ σ' s D} {ε1 ε2 : TagTy}, ElabV Γ v tv σ →
                ElabV Γ w tw σ' →
                DomCod σ s D → ConsTy σ' s →
                tagMeetTy σ' s = some ε1 →
                tagMeetTy σ (.arrow s D) = some ε2 →
                ElabT Γ (.app v w)
                  (.letin (.ascV ε1 tw s) 1 fun _ =>
                    .letin (.ascV ε2 (tv.rename 0) (.arrow s D)) 1 fun _ =>
                      .app (.var 0) (.var 1))
                  D
  /-- `(E+)` in A-normal form: coerce both operands to `Real`, then add. The
  second operand is weakened under the first binder. -/
  | eadd    : ∀ {Γ v tv w tw σ1 σ2} {ε1 ε2 : TagTy}, ElabV Γ v tv σ1 →
                ElabV Γ w tw σ2 →
                ConsTy σ1 .real → ConsTy σ2 .real →
                tagMeetTy σ1 .real = some ε1 →
                tagMeetTy σ2 .real = some ε2 →
                ElabT Γ (.add v w)
                  (.letin (.ascV ε1 tv .real) 1 fun _ =>
                    .letin (.ascV ε2 (tw.rename 0) .real) 1 fun _ =>
                      .add (.var 1) (.var 0))
                  (pointF .real)
  /-- `(Eif)` in A-normal form: bind the coerced condition, then a TPLC
  conditional on the two weakened branches. The premises are those of the
  GPLC rule, including the branch consistency `D₁ ∼ D₂`; the branches are not
  coerced, since the TPLC conditional types at the hull `D₁ ⊕_? D₂`. -/
  | eite    : ∀ {Γ v tv m tm n tn σ D1 D2} {ε : TagTy}, ElabV Γ v tv σ →
                ElabT Γ m tm D1 → ElabT Γ n tn D2 →
                ConsTy σ .bool → ConsD D1 D2 →
                tagMeetTy σ .bool = some ε →
                ElabT Γ (.ite v m n)
                  (.letin (.ascV ε tv .bool) 1 fun _ =>
                    .ite (.var 0) (tm.rename 0) (tn.rename 0))
                  (chooseSemU D1 D2)
end

/-- `Γ ⊢ v : σ ⇝ tv`, the GPLC value `v` of type `σ` elaborates to the TPLC
value `tv` (Figure 16). In `ElabV Γ v tv σ` the type comes last; the notation
restores the article's order. -/
scoped notation:50 (name := elabVStx) Γ:51 " ⊢ " v:51 " : " σ:51 " ⇝ " tv:51 => ElabV Γ v tv σ
/-- `Γ ⊢ m : D ⇝ tm`, the GPLC term `m` of type `D` elaborates to the TPLC
term `tm` (Figure 16). -/
scoped notation:50 (name := elabTStx) Γ:51 " ⊢ " m:51 " : " D:51 " ⇝ " tm:51 => ElabT Γ m tm D
/-- `⊢ v : σ ⇝ tv`, the elaboration of closed values. -/
scoped notation:50 (name := elabVClosedStx) "⊢ " v:51 " : " σ:51 " ⇝ " tv:51 => ElabV [] v tv σ
/-- `⊢ m : D ⇝ tm`, the elaboration of closed terms. -/
scoped notation:50 (name := elabTClosedStx) "⊢ " m:51 " : " D:51 " ⇝ " tm:51 => ElabT [] m tm D

/-- Rule `(Elet)` for a bound term of an abstract type `D` (`FDist` has no
definitional eta, so `eletin` cannot be applied to `D` directly). -/
theorem ElabT.eletin' {Γ : List FTy} {m : GPLC.Tm} {tm : Tm} {D : FDist} {n : GPLC.Tm}
    {tns : Fin D.n → Tm} {F : Fin D.n → FDist}
    (hm : ElabT Γ m tm D) (hbody : ∀ i, ElabT (D.ty i :: Γ) n (tns i) (F i)) :
    ElabT Γ (.letin m n) (.letin tm D.n tns) (letSem D F) := by
  cases D; exact .eletin hm hbody

/-- The meet of two consistent well-formed types is a valid evidence for their
consistency, with a well-formed erasure: the facts the TPLC ascription rules
need about an elaborated evidence. -/
theorem hvtag_of_tagMeetTy {σ σ' : FTy} {ε : TagTy} (hg : GoodTy σ) (hg' : GoodTy σ')
    (hc : ConsTy σ σ') (hpin : tagMeetTy σ σ' = some ε) :
    HVTagTy ε σ σ' ∧ GoodTy ε.toF := by
  obtain ⟨e, he, hL, hR⟩ := hvtag_tagMeetTy hg hg' (econsTy_of_consTy hc)
  rw [hpin] at he
  obtain rfl := Option.some.inj he
  have htoF : meetTy σ σ' = some ε.toF := by
    have h := tagMeetTy_toF σ σ'
    rw [hpin, Option.map_some] at h
    exact h.symm
  exact ⟨⟨hL, hR⟩, goodTy_meetTy hg hg' (econsTy_of_consTy hc) htoF⟩

/-! ## Preservation

Every elaboration produces a well-typed TPLC term at the same formula type.
Well-formedness of the environment discharges the well-formedness premises of
the TPLC rules. -/

mutual
/-- Lemma 11 (elaboration preserves types), preservation half for values. -/
theorem elab_preserves_val : ∀ {Γ v tv σ}, ElabV Γ v tv σ → CtxGood Γ →
    HasTyV Γ tv σ
  | _, _, _, _, .evar hx, _ => .var hx
  | _, _, _, _, .ereal, _ => .ascRaw .real ⟨.real, .real⟩ .real .real
  | _, _, _, _, .ebool, _ => .ascRaw .bool ⟨.bool, .bool⟩ .bool .bool
  | Γ, _, _, _, .elam (τ := τ) (D := D) hm hτ, hΓ => by
      have hgτ : GoodTy (liftFTy τ) := goodTy_liftF hτ
      have hbody : HasTyT (liftFTy τ :: Γ) _ D :=
        elab_preserves_tm hm (ctxGood_cons hgτ hΓ)
      have hgD : GoodD D := wf_tm hbody (ctxGood_cons hgτ hΓ)
      have hgarr : GoodTy (.arrow (liftFTy τ) D) := .arrow hgτ hgD
      have hgtag : GoodTy ((FTy.arrow (liftFTy τ) D).toTag).toF := by
        rw [FTy.toTag_toF]; exact hgarr
      exact .ascRaw (.lam hbody hgτ) (hvtag_refl hgarr) hgtag hgarr
/-- Lemma 11 (elaboration preserves types), preservation half for terms. -/
theorem elab_preserves_tm : ∀ {Γ m tm D}, ElabT Γ m tm D → CtxGood Γ →
    HasTyT Γ tm D
  | _, _, _, _, .eval hv, hΓ => .val (elab_preserves_val hv hΓ)
  | _, _, _, _, .echoice ha0 ha1 hm hn, hΓ =>
      .choice ha0 ha1 (elab_preserves_tm hm hΓ) (elab_preserves_tm hn hΓ)
  | _, _, _, _, .echoiceU hm hn, hΓ =>
      .choiceU (elab_preserves_tm hm hΓ) (elab_preserves_tm hn hΓ)
  | Γ, _, _, _, .eletin hm hbody, hΓ =>
      have hmty := elab_preserves_tm hm hΓ
      have hgD := wf_tm hmty hΓ
      .letin hmty (fun i => elab_preserves_tm (hbody i) (ctxGood_cons (hgD.tys i) hΓ))
  | Γ, _, _, _, .eascV (τ := τ) hv hcons hτ hpin, hΓ => by
      have htv := elab_preserves_val hv hΓ
      obtain ⟨hev, hge⟩ := hvtag_of_tagMeetTy (wf_val htv hΓ) (goodTy_liftF hτ)
        hcons hpin
      exact .ascV htv hev hge (goodTy_liftF hτ)
  | Γ, _, _, _, .eascT (D := D) (T := T) hm hcons hT, hΓ => by
      have htm := elab_preserves_tm hm hΓ
      have hgD := wf_tm htm hΓ
      have hgT := goodD_liftFD hT
      have hge : GoodD (tagMeetD D (liftFDist T)).toF := by
        rw [tagMeetD_toF]
        exact goodD_meetD hgD hgT (econsD_of_consD hcons)
      exact .ascT htm ⟨(hvalid_tagMeetD hgD hgT).1,
        (hvalid_tagMeetD hgD hgT).2⟩ hge hgT
  | Γ, _, _, _, .eapp (s := s) (D := D) hv hw hdc hcons hpin1 hpin2, hΓ => by
      have htv := elab_preserves_val hv hΓ
      have htw := elab_preserves_val hw hΓ
      obtain ⟨hgs, hgD⟩ := domcod_good hdc (wf_val htv hΓ)
      obtain ⟨hev1, hge1⟩ := hvtag_of_tagMeetTy (wf_val htw hΓ) hgs hcons hpin1
      obtain ⟨hev2, hge2⟩ := hvtag_of_tagMeetTy (wf_val htv hΓ) (.arrow hgs hgD)
        (domcod_cons hdc (wf_val htv hΓ)) hpin2
      have hvar0 : HasTyV (.arrow s D :: s :: Γ) (.var 0) (.arrow s D) := .var (by simp)
      have hvar1 : HasTyV (.arrow s D :: s :: Γ) (.var 1) s := .var (by simp)
      have happ : HasTyT (.arrow s D :: s :: Γ) (.app (.var 0) (.var 1)) D := .app hvar0 hvar1
      have hinner := hasTy_letin1
        (.ascV (hasTy_wk0_val (τ := s) htv) hev2 hge2 (.arrow hgs hgD)) happ
      exact hasTy_letin1 (.ascV htw hev1 hge1 hgs) hinner
  | Γ, _, _, _, .eadd hv hw hcons1 hcons2 hpin1 hpin2, hΓ => by
      have htv := elab_preserves_val hv hΓ
      have htw := elab_preserves_val hw hΓ
      obtain ⟨hev1, hge1⟩ := hvtag_of_tagMeetTy (wf_val htv hΓ) .real hcons1 hpin1
      obtain ⟨hev2, hge2⟩ := hvtag_of_tagMeetTy (wf_val htw hΓ) .real hcons2 hpin2
      have hvar0 : HasTyV (.real :: .real :: Γ) (.var 0) .real := .var (by simp)
      have hvar1 : HasTyV (.real :: .real :: Γ) (.var 1) .real := .var (by simp)
      have hadd : HasTyT (.real :: .real :: Γ) (.add (.var 1) (.var 0)) (pointF .real) :=
        .add hvar1 hvar0
      have hinner := hasTy_letin1
        (.ascV (hasTy_wk0_val (τ := .real) htw) hev2 hge2 .real) hadd
      exact hasTy_letin1 (.ascV htv hev1 hge1 .real) hinner
  | Γ, _, _, _, .eite hv hm hn hconsb _ hpin, hΓ => by
      have htv := elab_preserves_val hv hΓ
      have htm := elab_preserves_tm hm hΓ
      have htn := elab_preserves_tm hn hΓ
      obtain ⟨hev, hge⟩ := hvtag_of_tagMeetTy (wf_val htv hΓ) .bool hconsb hpin
      have hcond : HasTyV (.bool :: Γ) (.var 0) .bool := .var (by simp)
      have hite := HasTyT.ite hcond
        (hasTy_wk0_tm (τ := .bool) htm) (hasTy_wk0_tm (τ := .bool) htn)
      exact hasTy_letin1 (.ascV htv hev hge .bool) hite
end

/-! ## Existence

Every well-typed GPLC term elaborates. The consistency premises of the typing
rules make every meet the elaboration computes defined (`hvtag_tagMeetTy`). -/

mutual
/-- Lemma 11 (elaboration preserves types), existence half for values. -/
theorem elab_exists_val : ∀ {Γ v σ}, GPLC.HasTyV Γ v σ → CtxGood Γ →
    ∃ tv, ElabV Γ v tv σ
  | _, _, _, .var hx, _ => ⟨_, .evar hx⟩
  | _, _, _, .real, _ => ⟨_, .ereal⟩
  | _, _, _, .bool, _ => ⟨_, .ebool⟩
  | Γ, _, _, .lam (τ := τ) hm hτ, hΓ => by
      obtain ⟨tm, htm⟩ := elab_exists_tm hm (ctxGood_cons (goodTy_liftF hτ) hΓ)
      exact ⟨_, .elam htm hτ⟩
/-- Lemma 11 (elaboration preserves types), existence half for terms. -/
theorem elab_exists_tm : ∀ {Γ m D}, GPLC.HasTyT Γ m D → CtxGood Γ →
    ∃ tm, ElabT Γ m tm D
  | Γ, _, _, .val hv, hΓ => by
      obtain ⟨tv, htv⟩ := elab_exists_val hv hΓ
      exact ⟨_, .eval htv⟩
  | Γ, _, _, .app (s := s) (D := D) hv hw hdc hcons, hΓ => by
      obtain ⟨tv, htv⟩ := elab_exists_val hv hΓ
      obtain ⟨tw, htw⟩ := elab_exists_val hw hΓ
      obtain ⟨hgs, hgD⟩ := domcod_good hdc (good_val hv hΓ)
      obtain ⟨ε1, hpin1, -, -⟩ := hvtag_tagMeetTy (good_val hw hΓ) hgs (econsTy_of_consTy hcons)
      obtain ⟨ε2, hpin2, -, -⟩ := hvtag_tagMeetTy (good_val hv hΓ)
        (.arrow hgs hgD) (econsTy_of_consTy (domcod_cons hdc (good_val hv hΓ)))
      exact ⟨_, .eapp htv htw hdc hcons hpin1 hpin2⟩
  | Γ, _, _, @GPLC.HasTyT.letin _ ms nb ⟨k, ty, C⟩ F hm hbody, hΓ => by
      obtain ⟨tm, htm⟩ := elab_exists_tm hm hΓ
      have hgD : GoodD ⟨k, ty, C⟩ := good_tm hm hΓ
      classical
      have hex : ∀ i, ∃ tn, ElabT (ty i :: Γ) nb tn (F i) := fun i =>
        elab_exists_tm (hbody i) (ctxGood_cons (hgD.tys i) hΓ)
      exact ⟨_, .eletin (tns := fun i => (hex i).choose)
        htm (fun i => (hex i).choose_spec)⟩
  | Γ, _, _, .choice ha0 ha1 hm hn, hΓ => by
      obtain ⟨tm, htm⟩ := elab_exists_tm hm hΓ
      obtain ⟨tn, htn⟩ := elab_exists_tm hn hΓ
      exact ⟨_, .echoice ha0 ha1 htm htn⟩
  | Γ, _, _, .choiceU hm hn, hΓ => by
      obtain ⟨tm, htm⟩ := elab_exists_tm hm hΓ
      obtain ⟨tn, htn⟩ := elab_exists_tm hn hΓ
      exact ⟨_, .echoiceU htm htn⟩
  | Γ, _, _, .ascT (D := D) (T := T) hm hcons hT, hΓ => by
      obtain ⟨tm, htm⟩ := elab_exists_tm hm hΓ
      exact ⟨_, .eascT htm hcons hT⟩
  | Γ, _, _, .ascV (σ := σ) (τ := τ) hv hcons hτ, hΓ => by
      obtain ⟨tv, htv⟩ := elab_exists_val hv hΓ
      obtain ⟨ε, hpin, -, -⟩ := hvtag_tagMeetTy (good_val hv hΓ)
        (goodTy_liftF hτ) (econsTy_of_consTy hcons)
      exact ⟨_, .eascV htv hcons hτ hpin⟩
  | Γ, _, _, .ite hv hcb hm hn hc, hΓ => by
      obtain ⟨tv, htv⟩ := elab_exists_val hv hΓ
      obtain ⟨tm, htm⟩ := elab_exists_tm hm hΓ
      obtain ⟨tn, htn⟩ := elab_exists_tm hn hΓ
      obtain ⟨ε, hpin, -, -⟩ := hvtag_tagMeetTy (good_val hv hΓ) .bool (econsTy_of_consTy hcb)
      exact ⟨_, .eite htv htm htn hcb hc hpin⟩
  | Γ, _, _, .add hv hc1 hw hc2, hΓ => by
      obtain ⟨tv, htv⟩ := elab_exists_val hv hΓ
      obtain ⟨tw, htw⟩ := elab_exists_val hw hΓ
      obtain ⟨ε1, hpin1, -, -⟩ := hvtag_tagMeetTy (good_val hv hΓ) .real (econsTy_of_consTy hc1)
      obtain ⟨ε2, hpin2, -, -⟩ := hvtag_tagMeetTy (good_val hw hΓ) .real (econsTy_of_consTy hc2)
      exact ⟨_, .eadd htv htw hc1 hc2 hpin1 hpin2⟩
end

/-! ## Soundness for the source typing

An elaborable term is well-typed at the elaboration's type: the elaboration
adds nothing beyond the typing derivation. -/

mutual
/-- Lemma 51 (elaboration implies typing), values: if the GPLC value `v`
elaborates to `tv` at type `σ` under `Γ`, then `Γ ⊢ v : σ` in GPLC. -/
theorem elab_sound_val : ∀ {Γ} {v : GPLC.Val} {tv σ}, Γ ⊢ v : σ ⇝ tv → Γ ⊢ v : σ
  | _, _, _, _, .evar hx => .var hx
  | _, _, _, _, .ereal => .real
  | _, _, _, _, .ebool => .bool
  | _, _, _, _, .elam hm hτ => .lam (elab_sound_tm hm) hτ
/-- Lemma 51 (elaboration implies typing), terms: if the GPLC term `m`
elaborates to `tm` at type `D` under `Γ`, then `Γ ⊢ m : D` in GPLC. -/
theorem elab_sound_tm : ∀ {Γ} {m : GPLC.Tm} {tm D}, Γ ⊢ m : D ⇝ tm → Γ ⊢ m : D
  | _, _, _, _, .eval hv => .val (elab_sound_val hv)
  | _, _, _, _, .echoice ha0 ha1 hm hn =>
      .choice ha0 ha1 (elab_sound_tm hm) (elab_sound_tm hn)
  | _, _, _, _, .echoiceU hm hn =>
      .choiceU (elab_sound_tm hm) (elab_sound_tm hn)
  | _, _, _, _, .eletin hm hbody =>
      .letin (elab_sound_tm hm) (fun i => elab_sound_tm (hbody i))
  | _, _, _, _, .eascV hv hcons hτ _ => .ascV (elab_sound_val hv) hcons hτ
  | _, _, _, _, .eascT hm hcons hT => .ascT (elab_sound_tm hm) hcons hT
  | _, _, _, _, .eapp hv hw hdc hcons _ _ =>
      .app (elab_sound_val hv) (elab_sound_val hw) hdc hcons
  | _, _, _, _, .eadd hv hw hc1 hc2 _ _ =>
      .add (elab_sound_val hv) hc1 (elab_sound_val hw) hc2
  | _, _, _, _, .eite hv hm hn hcb hc _ =>
      .ite (elab_sound_val hv) hcb (elab_sound_tm hm) (elab_sound_tm hn) hc
end

/-! ## Lemma 11: elaboration preserves types -/

/-- Lemma 11 (elaboration preserves types), item 1: a GPLC value well-typed
under a well-formed environment elaborates to a TPLC value of the same type. -/
theorem elaboration_preserves_types_val {Γ : List FTy} {v : GPLC.Val} {σ : FTy}
    (hty : GPLC.HasTyV Γ v σ) (hΓ : CtxGood Γ) :
    ∃ tv, ElabV Γ v tv σ ∧ HasTyV Γ tv σ := by
  obtain ⟨tv, hel⟩ := elab_exists_val hty hΓ
  exact ⟨tv, hel, elab_preserves_val hel hΓ⟩

/-- Lemma 11 (elaboration preserves types), item 2: a GPLC term well-typed
under a well-formed environment elaborates to a TPLC term of the same type. -/
theorem elaboration_preserves_types {Γ : List FTy} {m : GPLC.Tm} {D : FDist}
    (hty : Γ ⊢ m : D) (hΓ : CtxGood Γ) :
    ∃ tm, Γ ⊢ m : D ⇝ tm ∧ Γ ⊢ tm : D := by
  obtain ⟨tm, hel⟩ := elab_exists_tm hty hΓ
  exact ⟨tm, hel, elab_preserves_tm hel hΓ⟩

/-- Lemma 11 for closed terms, the form Theorem 4 (`GPLC.type_safety`)
uses. -/
theorem elaboration_preserves_types_closed {m : GPLC.Tm} {D : FDist}
    (hty : GPLC.HasTyT [] m D) :
    ∃ tm, ElabT [] m tm D ∧ HasTyT [] tm D :=
  elaboration_preserves_types hty (by intro σ h; simp at h)

end GradualProb.TPLC
