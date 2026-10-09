import GradualProb.TPLC.GradualGuaranteeConvergence

/-!
# Normalization of the aligned closed fragment of TPLC

This module proves that every closed TPLC term typed by the aligned typing
judgment `NTm` converges (`norm_closed`).  The result goes beyond the article,
which states no normalization theorem for TPLC.  `NTm` is the typing of TPLC
with an extra alignment premise at each evidence written in the term: the
types the evidence relates have equivalent skeletons (`SkelEq`, and
`AscTAlign` for distribution ascriptions).  The proof is a reducibility
argument indexed by skeletons, types without probabilities.

The module also holds the substitution and closure toolkit of TPLC
(free-variable bounds `FvBelow`, closing substitutions `closeAt`, which are
simultaneous substitutions), which
`TPLC/DynamicConservativeExtension` uses.

## Main results

* `norm_closed`: every closed term with an aligned typing converges (beyond
  the article).
* `norm_val`, `norm_tm`: the fundamental property of reducibility.

## Reading guide

* Skeletons (`Skel`, `skelFTy`, `skelFD`), their equivalence `SkelEq`, and
  reducibility `NormV`/`NormT` (with the reducible outcomes `NormOut`), its
  invariance under coercion and its transport along `SkelEq`.
* The substitution and closure toolkit of TPLC.
* One lemma per reduction rule (`normT_val` to `normT_letin`), then the
  aligned typing `NRaw`/`NVal`/`NTm` and the fundamental property.
-/

open scoped BigOperators

namespace GradualProb.TPLC

open GradualProb.GPLC

/-! ## Skeletons -/

/-- A skeleton: a type without probabilities, the only part of a type that
convergence depends on.  All base types (including `?`) have skeleton `base`;
the codomain of an arrow is the list of the skeletons of its entries.  The
list gives `List.sizeOf_lt_of_mem` for the termination of `NormV`. -/
inductive Skel where
  | base : Skel
  | arrow : Skel → List Skel → Skel
deriving Inhabited

mutual
/-- Skeleton of a simple formula type. -/
def skelFTy : FTy → Skel
  | .real => .base
  | .bool => .base
  | .unk  => .base
  | .arrow s D => .arrow (skelFTy s) (skelFD D)
/-- Skeletons of the entries of a formula distribution type. -/
def skelFD : FDist → List Skel
  | ⟨n, ty, _⟩ => List.ofFn (fun i : Fin n => skelFTy (ty i))
end

/-- The list of skeletons of `D` has one element per entry of `D`. -/
@[simp] theorem skelFD_length (D : FDist) : (skelFD D).length = D.n := by
  obtain ⟨n, ty, C⟩ := D
  simp [skelFD]

/-- The skeleton list of `D`, read at entry `i`, is the skeleton of the type of
entry `i`. -/
theorem skelFD_get (D : FDist) (i : Fin D.n) :
    (skelFD D).get (Fin.cast (skelFD_length D).symm i) = skelFTy (D.ty i) := by
  obtain ⟨n, ty, C⟩ := D
  simp [skelFD]

/-! ## Skeleton equivalence

Skeletons are not invariant under coercion at the level of lists: `{{ℝ¹}}` and
`{{ℝ^½, ℝ^½}}` give `[base]` and `[base, base]`.  What `NormT` looks at is the
set of skeletons, since it asks for reducibility in one of the declared ones. -/

/-- Skeleton equivalence: equal bases, equivalent domains, and every codomain
skeleton on each side equivalent to one on the other side.  The witnesses are
functions `f`, `g` between the indices of the two lists. -/

inductive SkelEq : Skel → Skel → Prop where
  | base : SkelEq .base .base
  | arrow : ∀ {a a' : Skel} {ds ds' : List Skel}
      (f : Fin ds.length → Fin ds'.length) (g : Fin ds'.length → Fin ds.length),
      SkelEq a a' →
      (∀ i, SkelEq (ds.get i) (ds'.get (f i))) →
      (∀ j, SkelEq (ds.get (g j)) (ds'.get j)) →
      SkelEq (.arrow a ds) (.arrow a' ds')

/-- Skeleton equivalence is reflexive. -/
theorem SkelEq.refl : ∀ (s : Skel), SkelEq s s
  | .base => .base
  | .arrow a ds =>
      .arrow id id (SkelEq.refl a)
        (fun i => SkelEq.refl (ds.get i)) (fun i => SkelEq.refl (ds.get i))
  termination_by s => sizeOf s
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | (have h2 := List.sizeOf_lt_of_mem (List.getElem_mem (i.isLt))
         omega)

/-! ### Symmetry and transitivity -/

/-- Skeleton equivalence is symmetric. -/
theorem SkelEq.symm : ∀ {s s' : Skel}, SkelEq s s' → SkelEq s' s
  | _, _, .base => .base
  | _, _, .arrow f g ha hf hg =>
      .arrow g f (SkelEq.symm ha)
        (fun j => SkelEq.symm (hg j)) (fun i => SkelEq.symm (hf i))

/-- Skeleton equivalence is transitive. -/
theorem SkelEq.trans : ∀ {s1 s2 s3 : Skel}, SkelEq s1 s2 → SkelEq s2 s3 →
    SkelEq s1 s3
  | _, _, _, .base, .base => .base
  | _, _, _, @SkelEq.arrow _ _ _ _ f1 g1 ha1 hf1 hg1, .arrow f2 g2 ha2 hf2 hg2 =>
      .arrow (f2 ∘ f1) (g1 ∘ g2) (SkelEq.trans ha1 ha2)
        (fun i => SkelEq.trans (hf1 i) (hf2 (f1 i)))
        (fun j => SkelEq.trans (hg1 (g2 j)) (hg2 j))

/-! ## Reducibility

`NormV s v`: the closed value `v` is reducible at skeleton `s`.
`NormT ds m`: the closed term `m` converges, and its outcomes are reducible at
the skeletons `ds` (`NormOut`). Only `NormV` is recursive; `NormOut` and
`NormT` are defined from it.

The arrow clause speaks of the β-redex of the raw λ, not of `app`: rule
(Dapp) strips the outer evidence with `tagDom`/`tagCod`, which changes with
each coercion, while the binder annotation `σl` and the body `tmb` do not.
This makes reducibility invariant under coercion (`normV_coerce`). -/

/-- Reducibility of a closed value at a skeleton. The arrow clause asks the
body, with any reducible argument substituted, to converge with reducible
outcomes; it is `NormT` below, spelled out because `NormT` is defined from
`NormV`. -/
def NormV : Skel → Val → Prop
  | .base, _ => True
  | .arrow s ds, v =>
      ∀ (σl : FTy) (tmb : Tm) (ε : TagTy) (σ : FTy),
        v = .asc ε (.lam σl tmb) σ →
        ∀ w : Val, HasTyV [] w σl → NormV s w →
          ∃ (k : ℕ) (V : DConf), Red (tmb.subst0 w) k V ∧
            ∀ i, ∃ j : Fin ds.length,
              SkelEq (skelFTy (V.val i).tyEntry) (ds.get j) ∧ NormV (ds.get j) (V.val i)
  termination_by t _ => sizeOf t
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have h1 : ds[(j : ℕ)] ∈ ds := List.getElem_mem (j.isLt)
         have h2 := List.sizeOf_lt_of_mem h1
         omega)

/-- Reducible outcomes: each outcome of `V` is reducible at one of the
declared skeletons `ds`, and that skeleton is equivalent to the skeleton of the
outcome's own runtime type; the entrywise coercions of rules (D::μ) and
(Dlet) need the latter to read reducibility at the target entry. -/
@[reducible] def NormOut (ds : List Skel) (V : DConf) : Prop :=
  ∀ i, ∃ j : Fin ds.length,
    SkelEq (skelFTy (V.val i).tyEntry) (ds.get j) ∧ NormV (ds.get j) (V.val i)

/-- Reducibility of a closed term: it converges, with reducible outcomes. -/
@[reducible] def NormT (ds : List Skel) (m : Tm) : Prop :=
  ∃ (k : ℕ) (V : DConf), Red m k V ∧ NormOut ds V

/-- The arrow clause of `NormV`, with `NormT`. -/
theorem normV_arrow {s : Skel} {ds : List Skel} {v : Val} :
    NormV (.arrow s ds) v ↔
      ∀ (σl : FTy) (tmb : Tm) (ε : TagTy) (σ : FTy),
        v = .asc ε (.lam σl tmb) σ →
        ∀ w : Val, HasTyV [] w σl → NormV s w → NormT ds (tmb.subst0 w) := by
  rw [NormV.eq_2]

/-- A reducible term converges. -/
theorem converges_of_normT {ds : List Skel} {m : Tm} (h : NormT ds m) :
    Converges m := by
  obtain ⟨k, V, hred, -⟩ := h
  exact ⟨k, V, hred⟩

/-! ## Values other than λ are reducible at every skeleton

The arrow clause is an implication whose premise is a syntactic equality with
a raw `λ`; a literal, a variable or an error never satisfies it. -/

/-- A value that is not an ascribed raw `λ` is reducible at every skeleton. -/
theorem normV_of_not_lam {s : Skel} {v : Val}
    (h : ∀ σl tmb ε σ, v ≠ .asc ε (.lam σl tmb) σ) : NormV s v := by
  cases s with
  | base => rw [NormV]; trivial
  | arrow a ds =>
      rw [NormV]
      intro σl tmb ε σ heq
      exact absurd heq (h σl tmb ε σ)

/-- An error is reducible at every skeleton. -/
theorem normV_err {s : Skel} {σ : FTy} : NormV s (.err σ) :=
  normV_of_not_lam (by intro σl tmb ε σ' h; cases h)

/-- A real literal is reducible at every skeleton. -/
theorem normV_real {s : Skel} {ε : TagTy} {r : ℝ} {σ : FTy} :
    NormV s (.asc ε (.real r) σ) :=
  normV_of_not_lam (by intro σl tmb ε' σ' h; cases h)

/-- A boolean literal is reducible at every skeleton. -/
theorem normV_bool {s : Skel} {ε : TagTy} {b : Bool} {σ : FTy} :
    NormV s (.asc ε (.bool b) σ) :=
  normV_of_not_lam (by intro σl tmb ε' σ' h; cases h)


/-! ## Invariance under coercion

Coercing a value leaves its raw part `u` untouched: rule (D::σ) changes the
evidence and the annotated type only.  Since the arrow clause speaks of the
raw part (binder annotation and body), reducibility carries over without
looking at the types. -/

/-- Reducibility of an ascribed raw value depends neither on its evidence nor on
its annotated type. -/
theorem normV_coerce {s : Skel} {ε1 ε3 : TagTy} {u : Raw} {σ σ' : FTy}
    (h : NormV s (.asc ε1 u σ)) : NormV s (.asc ε3 u σ') := by
  cases s with
  | base => rw [NormV]; trivial
  | arrow a ds =>
      rw [NormV] at h ⊢
      intro σl tmb ε σ0 heq
      cases heq
      exact h σl tmb ε1 σ rfl

/-- If a value ascription reduces (to a value or to an error), its outcomes are
reducible at the same skeleton as the ascribed value. -/
theorem normV_ascV {s : Skel} {ε : TagTy} {v : Val} {σ' : FTy} {k : ℕ}
    {W : DConf} (hv : NormV s v) (hred : Red (.ascV ε v σ') k W) :
    ∀ i, NormV s (W.val i) := by
  obtain ⟨w, hw, rfl⟩ := red_ascV_coerce hred
  cases v with
  | var x => exact nomatch hw
  | err σ0 => cases hw; exact fun i => normV_err
  | asc ε1 u σv =>
    rcases Val.coerce_asc_inv hw with ⟨ε3, -, -, rfl⟩ | ⟨-, rfl⟩
    · exact fun i => normV_coerce (ε3 := ε3) (σ' := σ') hv
    · exact fun i => normV_err

/-! ### Transport along skeleton equivalence

Stated in both directions at once: the arrow case is contravariant in the
domain, and structural recursion on the derivation accepts `(ih ha).2` (a
field application) but not a recursive call on `SkelEq.symm ha`. -/

/-- Reducibility is invariant under skeleton equivalence: if `SkelEq s s'`, then
a value is reducible at `s` if and only if it is reducible at `s'`. -/
theorem normV_skelEq : ∀ {s s' : Skel}, SkelEq s s' →
    (∀ v : Val, NormV s v → NormV s' v) ∧ (∀ v : Val, NormV s' v → NormV s v)
  | _, _, .base => by
      constructor <;> (intro v _; rw [NormV]; trivial)
  | _, _, @SkelEq.arrow a a' ds ds' f g ha hf hg => by
      have ih := normV_skelEq ha
      constructor
      · intro v h
        rw [NormV] at h ⊢
        intro σl tmb ε σ heq w hw hnw
        have hb := h σl tmb ε σ heq w hw (ih.2 w hnw)
        obtain ⟨k, V, hred, hout⟩ := hb
        refine ⟨k, V, hred, fun i => ?_⟩
        obtain ⟨j, hsk, hj⟩ := hout i
        exact ⟨f j, SkelEq.trans hsk (hf j), (normV_skelEq (hf j)).1 _ hj⟩
      · intro v h
        rw [NormV] at h ⊢
        intro σl tmb ε σ heq w hw hnw
        have hb := h σl tmb ε σ heq w hw (ih.1 w hnw)
        obtain ⟨k, V, hred, hout⟩ := hb
        refine ⟨k, V, hred, fun i => ?_⟩
        obtain ⟨j, hsk, hj⟩ := hout i
        exact ⟨g j, SkelEq.trans hsk (SkelEq.symm (hg j)), (normV_skelEq (hg j)).2 _ hj⟩


/-! ## Substitution toolkit of TPLC

Free-variable bounds and the substitution lemmas that the fundamental property
and `TPLC/DynamicConservativeExtension` need. -/

/-! ### Free-variable bounds -/

mutual
/-- Free variables of a TPLC raw value are `< n`. -/
def Raw.FvBelow : Raw → ℕ → Prop
  | .real _, _ => True
  | .bool _, _ => True
  | .lam _ m, n => Tm.FvBelow m (n + 1)
/-- Free variables of a TPLC value are `< n`. -/
def Val.FvBelow : Val → ℕ → Prop
  | .var x, n => x < n
  | .asc _ u _, n => u.FvBelow n
  | .err _, _ => True
/-- Free variables of a TPLC term are `< n`. -/
def Tm.FvBelow : Tm → ℕ → Prop
  | .val v, n => v.FvBelow n
  | .app v w, n => v.FvBelow n ∧ w.FvBelow n
  | .letin m _ ns, n => m.FvBelow n ∧ ∀ i, (ns i).FvBelow (n + 1)
  | .choice _ m1 m2, n => m1.FvBelow n ∧ m2.FvBelow n
  | .ascT _ m _, n => m.FvBelow n
  | .ascV _ v _, n => v.FvBelow n
  | .ite v m1 m2, n => v.FvBelow n ∧ m1.FvBelow n ∧ m2.FvBelow n
  | .add v w, n => v.FvBelow n ∧ w.FvBelow n
  | .errD _, _ => True
end

mutual
/-- The bound `FvBelow` is monotone in its index (raw values). -/
theorem Raw.fvBelow_mono : ∀ {u : Raw} {n n' : ℕ}, u.FvBelow n → n ≤ n' →
    u.FvBelow n'
  | .real _, _, _, _, _ => trivial
  | .bool _, _, _, _, _ => trivial
  | .lam _ m, _, _, h, hle => Tm.fvBelow_mono (m := m) h (by omega)
/-- The bound `FvBelow` is monotone in its index (values). -/
theorem Val.fvBelow_mono : ∀ {v : Val} {n n' : ℕ}, v.FvBelow n → n ≤ n' →
    v.FvBelow n'
  | .var _, _, _, h, hle => lt_of_lt_of_le h hle
  | .asc _ u _, _, _, h, hle => Raw.fvBelow_mono (u := u) h hle
  | .err _, _, _, _, _ => trivial
/-- The bound `FvBelow` is monotone in its index (terms). -/
theorem Tm.fvBelow_mono : ∀ {m : Tm} {n n' : ℕ}, m.FvBelow n → n ≤ n' →
    m.FvBelow n'
  | .val v, _, _, h, hle => Val.fvBelow_mono (v := v) h hle
  | .app v w, _, _, h, hle =>
      ⟨Val.fvBelow_mono (v := v) h.1 hle, Val.fvBelow_mono (v := w) h.2 hle⟩
  | .letin m _ ns, _, _, h, hle =>
      ⟨Tm.fvBelow_mono (m := m) h.1 hle,
        fun i => Tm.fvBelow_mono (m := ns i) (h.2 i) (by omega)⟩
  | .choice _ m1 m2, _, _, h, hle =>
      ⟨Tm.fvBelow_mono (m := m1) h.1 hle,
        Tm.fvBelow_mono (m := m2) h.2 hle⟩
  | .ascT _ m _, _, _, h, hle => Tm.fvBelow_mono (m := m) h hle
  | .ascV _ v _, _, _, h, hle => Val.fvBelow_mono (v := v) h hle
  | .ite v m1 m2, _, _, h, hle =>
      ⟨Val.fvBelow_mono (v := v) h.1 hle,
        Tm.fvBelow_mono (m := m1) h.2.1 hle,
        Tm.fvBelow_mono (m := m2) h.2.2 hle⟩
  | .add v w, _, _, h, hle =>
      ⟨Val.fvBelow_mono (v := v) h.1 hle, Val.fvBelow_mono (v := w) h.2 hle⟩
  | .errD _, _, _, _, _ => trivial
end

/-! ### Renaming and substitution above the bound are the identity -/

mutual
/-- Renaming at an index `c` at or above the bound leaves a raw value unchanged. -/
theorem Raw.rename_below : ∀ {u : Raw} {n c : ℕ}, u.FvBelow n → n ≤ c →
    u.rename c = u
  | .real _, _, _, _, _ => by simp [Raw.rename]
  | .bool _, _, _, _, _ => by simp [Raw.rename]
  | .lam σ m, n, c, h, hle => by
      simp only [Raw.rename]
      rw [Tm.rename_below (m := m) h (by omega)]
/-- Renaming at an index `c` at or above the bound leaves a value unchanged. -/
theorem Val.rename_below : ∀ {v : Val} {n c : ℕ}, v.FvBelow n → n ≤ c →
    v.rename c = v
  | .var x, n, c, h, hle => by
      have hx : x < n := h
      simp only [Val.rename, if_pos (lt_of_lt_of_le hx hle)]
  | .asc ε u σ, _, _, h, hle => by
      simp only [Val.rename]
      rw [Raw.rename_below (u := u) h hle]
  | .err _, _, _, _, _ => by simp [Val.rename]
/-- Renaming at an index `c` at or above the bound leaves a term unchanged. -/
theorem Tm.rename_below : ∀ {m : Tm} {n c : ℕ}, m.FvBelow n → n ≤ c →
    m.rename c = m
  | .val v, _, _, h, hle => by
      simp only [Tm.rename]; rw [Val.rename_below (v := v) h hle]
  | .app v w, _, _, h, hle => by
      simp only [Tm.rename]
      rw [Val.rename_below (v := v) h.1 hle,
        Val.rename_below (v := w) h.2 hle]
  | .letin m _ ns, n, c, h, hle => by
      rw [Tm.rename_letin, Tm.rename_below (m := m) h.1 hle]
      congr 1; funext i
      exact Tm.rename_below (m := ns i) (h.2 i) (by omega)
  | .choice _ m1 m2, _, _, h, hle => by
      simp only [Tm.rename]
      rw [Tm.rename_below (m := m1) h.1 hle,
        Tm.rename_below (m := m2) h.2 hle]
  | .ascT _ m _, _, _, h, hle => by
      simp only [Tm.rename]; rw [Tm.rename_below (m := m) h hle]
  | .ascV _ v _, _, _, h, hle => by
      simp only [Tm.rename]; rw [Val.rename_below (v := v) h hle]
  | .ite v m1 m2, _, _, h, hle => by
      simp only [Tm.rename]
      rw [Val.rename_below (v := v) h.1 hle,
        Tm.rename_below (m := m1) h.2.1 hle,
        Tm.rename_below (m := m2) h.2.2 hle]
  | .add v w, _, _, h, hle => by
      simp only [Tm.rename]
      rw [Val.rename_below (v := v) h.1 hle,
        Val.rename_below (v := w) h.2 hle]
  | .errD _, _, _, _, _ => by simp [Tm.rename]
end

mutual
/-- Substitution at an index `k` at or above the bound leaves a raw value
unchanged. -/
theorem Raw.subst_below : ∀ {u : Raw} {n k : ℕ} {w : Val}, u.FvBelow n →
    n ≤ k → u.subst k w = u
  | .real _, _, _, _, _, _ => by simp [Raw.subst]
  | .bool _, _, _, _, _, _ => by simp [Raw.subst]
  | .lam σ m, _, _, _, h, hle => by
      simp only [Raw.subst]
      rw [Tm.subst_below (m := m) h (by omega)]
/-- Substitution at an index `k` at or above the bound leaves a value unchanged. -/
theorem Val.subst_below : ∀ {v : Val} {n k : ℕ} {w : Val}, v.FvBelow n →
    n ≤ k → v.subst k w = v
  | .var x, n, k, w, h, hle => by
      have hx : x < n := h
      simp only [Val.subst, if_neg (by omega : ¬ x = k),
        if_neg (by omega : ¬ x > k)]
  | .asc ε u σ, _, _, _, h, hle => by
      simp only [Val.subst]
      rw [Raw.subst_below (u := u) h hle]
  | .err _, _, _, _, _, _ => by simp [Val.subst]
/-- Substitution at an index `k` at or above the bound leaves a term unchanged. -/
theorem Tm.subst_below : ∀ {m : Tm} {n k : ℕ} {w : Val}, m.FvBelow n →
    n ≤ k → m.subst k w = m
  | .val v, _, _, _, h, hle => by
      simp only [Tm.subst]; rw [Val.subst_below (v := v) h hle]
  | .app v w', _, _, _, h, hle => by
      simp only [Tm.subst]
      rw [Val.subst_below (v := v) h.1 hle,
        Val.subst_below (v := w') h.2 hle]
  | .letin m _ ns, n, k, w, h, hle => by
      rw [Tm.subst_letin, Tm.subst_below (m := m) h.1 hle]
      congr 1; funext i
      exact Tm.subst_below (m := ns i) (h.2 i) (by omega)
  | .choice _ m1 m2, _, _, _, h, hle => by
      simp only [Tm.subst]
      rw [Tm.subst_below (m := m1) h.1 hle,
        Tm.subst_below (m := m2) h.2 hle]
  | .ascT _ m _, _, _, _, h, hle => by
      simp only [Tm.subst]; rw [Tm.subst_below (m := m) h hle]
  | .ascV _ v _, _, _, _, h, hle => by
      simp only [Tm.subst]; rw [Val.subst_below (v := v) h hle]
  | .ite v m1 m2, _, _, _, h, hle => by
      simp only [Tm.subst]
      rw [Val.subst_below (v := v) h.1 hle,
        Tm.subst_below (m := m1) h.2.1 hle,
        Tm.subst_below (m := m2) h.2.2 hle]
  | .add v w', _, _, _, h, hle => by
      simp only [Tm.subst]
      rw [Val.subst_below (v := v) h.1 hle,
        Val.subst_below (v := w') h.2 hle]
  | .errD _, _, _, _, _, _ => by simp [Tm.subst]
end

/-! ### Substitution of a closed value lowers the bound -/

mutual
/-- Substituting a closed value at `k ≤ n` into a raw value bounded by `n + 1`
gives a raw value bounded by `n`. -/
theorem Raw.subst_pres_below : ∀ {u : Raw} {n k : ℕ} {w : Val},
    u.FvBelow (n + 1) → w.FvBelow 0 → k ≤ n → (u.subst k w).FvBelow n
  | .real _, _, _, _, _, _, _ => by simp only [Raw.subst]; trivial
  | .bool _, _, _, _, _, _, _ => by simp only [Raw.subst]; trivial
  | .lam σ m, n, k, w, h, hw, hk => by
      simp only [Raw.subst]
      rw [Val.rename_below hw (Nat.zero_le 0)]
      exact Tm.subst_pres_below (m := m) h hw (by omega)
/-- Substituting a closed value at `k ≤ n` into a value bounded by `n + 1` gives
a value bounded by `n`. -/
theorem Val.subst_pres_below : ∀ {v : Val} {n k : ℕ} {w : Val},
    v.FvBelow (n + 1) → w.FvBelow 0 → k ≤ n → (v.subst k w).FvBelow n
  | .var x, n, k, w, h, hw, hk => by
      have hx : x < n + 1 := h
      by_cases h1 : x = k
      · simp only [Val.subst, if_pos h1]
        exact Val.fvBelow_mono hw (Nat.zero_le n)
      · by_cases h2 : x > k
        · simp only [Val.subst, if_neg h1, if_pos h2]
          show x - 1 < n
          omega
        · simp only [Val.subst, if_neg h1, if_neg h2]
          show x < n
          omega
  | .asc ε u σ, _, _, _, h, hw, hk => by
      simp only [Val.subst]
      exact Raw.subst_pres_below (u := u) h hw hk
  | .err _, _, _, _, _, _, _ => by simp only [Val.subst]; trivial
/-- Substituting a closed value at `k ≤ n` into a term bounded by `n + 1` gives
a term bounded by `n`. -/
theorem Tm.subst_pres_below : ∀ {m : Tm} {n k : ℕ} {w : Val},
    m.FvBelow (n + 1) → w.FvBelow 0 → k ≤ n → (m.subst k w).FvBelow n
  | .val v, _, _, _, h, hw, hk => by
      simp only [Tm.subst]
      exact Val.subst_pres_below (v := v) h hw hk
  | .app v w', _, _, _, h, hw, hk => by
      simp only [Tm.subst]
      exact ⟨Val.subst_pres_below (v := v) h.1 hw hk,
        Val.subst_pres_below (v := w') h.2 hw hk⟩
  | .letin m _ ns, n, k, w, h, hw, hk => by
      rw [Tm.subst_letin, Val.rename_below hw (Nat.zero_le 0)]
      exact ⟨Tm.subst_pres_below (m := m) h.1 hw hk,
        fun i => Tm.subst_pres_below (m := ns i) (h.2 i) hw (by omega)⟩
  | .choice _ m1 m2, _, _, _, h, hw, hk => by
      simp only [Tm.subst]
      exact ⟨Tm.subst_pres_below (m := m1) h.1 hw hk,
        Tm.subst_pres_below (m := m2) h.2 hw hk⟩
  | .ascT _ m _, _, _, _, h, hw, hk => by
      simp only [Tm.subst]
      exact Tm.subst_pres_below (m := m) h hw hk
  | .ascV _ v _, _, _, _, h, hw, hk => by
      simp only [Tm.subst]
      exact Val.subst_pres_below (v := v) h hw hk
  | .ite v m1 m2, _, _, _, h, hw, hk => by
      simp only [Tm.subst]
      exact ⟨Val.subst_pres_below (v := v) h.1 hw hk,
        Tm.subst_pres_below (m := m1) h.2.1 hw hk,
        Tm.subst_pres_below (m := m2) h.2.2 hw hk⟩
  | .add v w', _, _, _, h, hw, hk => by
      simp only [Tm.subst]
      exact ⟨Val.subst_pres_below (v := v) h.1 hw hk,
        Val.subst_pres_below (v := w') h.2 hw hk⟩
  | .errD _, _, _, _, _, _, _ => by simp only [Tm.subst]; trivial
end

/-! ### Commutation of substitutions -/

mutual
/-- Substitutions of two closed values at adjacent indices commute (raw values). -/
theorem Raw.subst_comm : ∀ {u : Raw} {k : ℕ} {v w : Val}, v.FvBelow 0 →
    w.FvBelow 0 → (u.subst (k + 1) v).subst k w = (u.subst k w).subst k v
  | .real _, _, _, _, _, _ => by simp [Raw.subst]
  | .bool _, _, _, _, _, _ => by simp [Raw.subst]
  | .lam σ m, k, v, w, hv, hw => by
      simp only [Raw.subst]
      rw [Val.rename_below hv (Nat.zero_le 0),
        Val.rename_below hw (Nat.zero_le 0), Tm.subst_comm (m := m) hv hw]
  termination_by structural u _ _ _ _ _ => u
/-- Substitutions of two closed values at adjacent indices commute (values). -/
theorem Val.subst_comm : ∀ {u : Val} {k : ℕ} {v w : Val}, v.FvBelow 0 →
    w.FvBelow 0 → (u.subst (k + 1) v).subst k w = (u.subst k w).subst k v
  | .var x, k, v, w, hv, hw => by
      rcases Nat.lt_trichotomy x (k + 1) with hx | hx | hx
      · have h1 : (Val.var x).subst (k + 1) v = Val.var x := by
          simp only [Val.subst, if_neg (by omega : ¬ x = k + 1),
            if_neg (by omega : ¬ x > k + 1)]
        rw [h1]
        by_cases hxk : x = k
        · subst hxk
          have h2 : (Val.var x).subst x w = w := by simp [Val.subst]
          rw [h2, Val.subst_below hw (Nat.zero_le x)]
        · have h2 : (Val.var x).subst k w = Val.var x := by
            simp only [Val.subst, if_neg hxk, if_neg (by omega : ¬ x > k)]
          have h3 : (Val.var x).subst k v = Val.var x := by
            simp only [Val.subst, if_neg hxk, if_neg (by omega : ¬ x > k)]
          rw [h2, h3]
      · subst hx
        have h1 : (Val.var (k + 1)).subst (k + 1) v = v := by
          simp [Val.subst]
        have h2 : (Val.var (k + 1)).subst k w = Val.var k := by
          simp only [Val.subst, if_neg (by omega : ¬ k + 1 = k),
            if_pos (by omega : k + 1 > k), Nat.add_sub_cancel]
        rw [h1, h2, Val.subst_below hv (Nat.zero_le k)]
        simp [Val.subst]
      · have h1 : (Val.var x).subst (k + 1) v = Val.var (x - 1) := by
          simp only [Val.subst, if_neg (by omega : ¬ x = k + 1),
            if_pos (by omega : x > k + 1)]
        have h2 : (Val.var x).subst k w = Val.var (x - 1) := by
          simp only [Val.subst, if_neg (by omega : ¬ x = k),
            if_pos (by omega : x > k)]
        have h3 : (Val.var (x - 1)).subst k w = Val.var (x - 1 - 1) := by
          simp only [Val.subst, if_neg (by omega : ¬ x - 1 = k),
            if_pos (by omega : x - 1 > k)]
        have h4 : (Val.var (x - 1)).subst k v = Val.var (x - 1 - 1) := by
          simp only [Val.subst, if_neg (by omega : ¬ x - 1 = k),
            if_pos (by omega : x - 1 > k)]
        rw [h1, h3, h2, h4]
  | .asc ε u σ, _, _, _, hv, hw => by
      simp only [Val.subst]
      rw [Raw.subst_comm (u := u) hv hw]
  | .err _, _, _, _, _, _ => by simp [Val.subst]
  termination_by structural u _ _ _ _ _ => u
/-- Substitutions of two closed values at adjacent indices commute (terms). -/
theorem Tm.subst_comm : ∀ {m : Tm} {k : ℕ} {v w : Val}, v.FvBelow 0 →
    w.FvBelow 0 → (m.subst (k + 1) v).subst k w = (m.subst k w).subst k v
  | .val u, _, _, _, hv, hw => by
      simp only [Tm.subst]; rw [Val.subst_comm (u := u) hv hw]
  | .app u1 u2, _, _, _, hv, hw => by
      simp only [Tm.subst]
      rw [Val.subst_comm (u := u1) hv hw, Val.subst_comm (u := u2) hv hw]
  | .letin m _ ns, k, v, w, hv, hw => by
      rw [Tm.subst_letin, Tm.subst_letin, Tm.subst_letin, Tm.subst_letin,
        Val.rename_below hv (Nat.zero_le 0), Val.rename_below hw (Nat.zero_le 0),
        Tm.subst_comm (m := m) hv hw]
      congr 1; funext i
      exact Tm.subst_comm (m := ns i) hv hw
  | .choice _ m1 m2, _, _, _, hv, hw => by
      simp only [Tm.subst]
      rw [Tm.subst_comm (m := m1) hv hw, Tm.subst_comm (m := m2) hv hw]
  | .ascT _ m _, _, _, _, hv, hw => by
      simp only [Tm.subst]; rw [Tm.subst_comm (m := m) hv hw]
  | .ascV _ u _, _, _, _, hv, hw => by
      simp only [Tm.subst]; rw [Val.subst_comm (u := u) hv hw]
  | .ite u m1 m2, _, _, _, hv, hw => by
      simp only [Tm.subst]
      rw [Val.subst_comm (u := u) hv hw, Tm.subst_comm (m := m1) hv hw,
        Tm.subst_comm (m := m2) hv hw]
  | .add u1 u2, _, _, _, hv, hw => by
      simp only [Tm.subst]
      rw [Val.subst_comm (u := u1) hv hw, Val.subst_comm (u := u2) hv hw]
  | .errD _, _, _, _, _, _ => by simp [Tm.subst]
  termination_by structural m _ _ _ _ _ => m
end

/-! ## Closing open terms

`closeAt k ρ` substitutes the values of `ρ`, simultaneously, for the variables
`k, k + 1, …, k + ρ.length - 1`, lowers the variables above them by
`ρ.length`, and leaves the variables below `k` (bound by the binders crossed so
far) unchanged. The environments that close terms are closed, so the values
are not shifted under binders. The congruence equations hold by `rfl`;
`closeAt_cons` relates the closing to substitution, one value at a time. -/

mutual
/-- Close a TPLC raw value with the environment `ρ` at depth `k`. -/
def Raw.closeAt : Raw → ℕ → List Val → Raw
  | .real r, _, _ => .real r
  | .bool b, _, _ => .bool b
  | .lam σ m, k, ρ => .lam σ (m.closeAt (k + 1) ρ)
/-- Close a TPLC value with the environment `ρ` at depth `k`. -/
def Val.closeAt : Val → ℕ → List Val → Val
  | .var x, k, ρ =>
      if x < k then .var x else (ρ[x - k]?).getD (.var (x - ρ.length))
  | .asc ε u σ, k, ρ => .asc ε (u.closeAt k ρ) σ
  | .err σ, _, _ => .err σ
/-- Close a TPLC term with the environment `ρ` at depth `k`. -/
def Tm.closeAt : Tm → ℕ → List Val → Tm
  | .val v, k, ρ => .val (v.closeAt k ρ)
  | .app v w, k, ρ => .app (v.closeAt k ρ) (w.closeAt k ρ)
  | .letin m n ns, k, ρ => .letin (m.closeAt k ρ) n (fun i => (ns i).closeAt (k + 1) ρ)
  | .choice p m n, k, ρ => .choice p (m.closeAt k ρ) (n.closeAt k ρ)
  | .ascT ε m D, k, ρ => .ascT ε (m.closeAt k ρ) D
  | .ascV ε v σ, k, ρ => .ascV ε (v.closeAt k ρ) σ
  | .ite v m n, k, ρ => .ite (v.closeAt k ρ) (m.closeAt k ρ) (n.closeAt k ρ)
  | .add v w, k, ρ => .add (v.closeAt k ρ) (w.closeAt k ρ)
  | .errD D, _, _ => .errD D
end

/-- Close a TPLC value with a list of values at index 0. -/
@[reducible] def Val.close (u : Val) (ρ : List Val) : Val :=
  u.closeAt 0 ρ

/-- Close a TPLC term with a list of values at index 0. -/
@[reducible] def Tm.close (m : Tm) (ρ : List Val) : Tm := m.closeAt 0 ρ

mutual
/-- Closing at an index `k` at or above the bound leaves a raw value unchanged. -/
theorem Raw.closeAt_below : ∀ {ρ : List Val} {u : Raw} {n k : ℕ},
    u.FvBelow n → n ≤ k → u.closeAt k ρ = u
  | _, .real _, _, _, _, _ => rfl
  | _, .bool _, _, _, _, _ => rfl
  | _, .lam σ m, _, _, h, hle => by
      simp only [Raw.closeAt]; rw [Tm.closeAt_below (m := m) h (by omega)]
/-- Closing at an index `k` at or above the bound leaves a value unchanged. -/
theorem Val.closeAt_below : ∀ {ρ : List Val} {u : Val} {n k : ℕ},
    u.FvBelow n → n ≤ k → u.closeAt k ρ = u
  | _, .var x, n, k, h, hle => by
      have hx : x < n := h
      simp only [Val.closeAt, if_pos (lt_of_lt_of_le hx hle)]
  | _, .asc ε u σ, _, _, h, hle => by
      simp only [Val.closeAt]; rw [Raw.closeAt_below (u := u) h hle]
  | _, .err _, _, _, _, _ => rfl
/-- Closing at an index `k` at or above the bound leaves a term unchanged. -/
theorem Tm.closeAt_below : ∀ {ρ : List Val} {m : Tm} {n k : ℕ},
    m.FvBelow n → n ≤ k → m.closeAt k ρ = m
  | _, .val v, _, _, h, hle => by
      simp only [Tm.closeAt]; rw [Val.closeAt_below (u := v) h hle]
  | _, .app v w, _, _, h, hle => by
      simp only [Tm.closeAt]
      rw [Val.closeAt_below (u := v) h.1 hle, Val.closeAt_below (u := w) h.2 hle]
  | _, .letin m _ ns, _, _, h, hle => by
      simp only [Tm.closeAt]
      rw [Tm.closeAt_below (m := m) h.1 hle]
      congr 1; funext i
      exact Tm.closeAt_below (m := ns i) (h.2 i) (by omega)
  | _, .choice _ m1 m2, _, _, h, hle => by
      simp only [Tm.closeAt]
      rw [Tm.closeAt_below (m := m1) h.1 hle, Tm.closeAt_below (m := m2) h.2 hle]
  | _, .ascT _ m _, _, _, h, hle => by
      simp only [Tm.closeAt]; rw [Tm.closeAt_below (m := m) h hle]
  | _, .ascV _ v _, _, _, h, hle => by
      simp only [Tm.closeAt]; rw [Val.closeAt_below (u := v) h hle]
  | _, .ite v m1 m2, _, _, h, hle => by
      simp only [Tm.closeAt]
      rw [Val.closeAt_below (u := v) h.1 hle, Tm.closeAt_below (m := m1) h.2.1 hle,
        Tm.closeAt_below (m := m2) h.2.2 hle]
  | _, .add v w, _, _, h, hle => by
      simp only [Tm.closeAt]
      rw [Val.closeAt_below (u := v) h.1 hle, Val.closeAt_below (u := w) h.2 hle]
  | _, .errD _, _, _, _, _ => rfl
end

mutual
/-- Closing with the empty environment is the identity. -/
theorem Raw.closeAt_nil : ∀ {u : Raw} {k : ℕ}, u.closeAt k [] = u
  | .real _, _ => rfl
  | .bool _, _ => rfl
  | .lam σ m, _ => by simp only [Raw.closeAt]; rw [Tm.closeAt_nil (m := m)]
/-- Closing a value with the empty environment is the identity. -/
theorem Val.closeAt_nil : ∀ {u : Val} {k : ℕ}, u.closeAt k [] = u
  | .var x, k => by by_cases hx : x < k <;> simp [Val.closeAt, hx]
  | .asc ε u σ, _ => by simp only [Val.closeAt]; rw [Raw.closeAt_nil (u := u)]
  | .err _, _ => rfl
/-- Closing a term with the empty environment is the identity. -/
theorem Tm.closeAt_nil : ∀ {m : Tm} {k : ℕ}, m.closeAt k [] = m
  | .val u, _ => by simp only [Tm.closeAt]; rw [Val.closeAt_nil (u := u)]
  | .app u w, _ => by
      simp only [Tm.closeAt]; rw [Val.closeAt_nil (u := u), Val.closeAt_nil (u := w)]
  | .letin m _ ns, _ => by
      simp only [Tm.closeAt]; rw [Tm.closeAt_nil (m := m)]
      congr 1; funext i
      exact Tm.closeAt_nil (m := ns i)
  | .choice _ m1 m2, _ => by
      simp only [Tm.closeAt]; rw [Tm.closeAt_nil (m := m1), Tm.closeAt_nil (m := m2)]
  | .ascT _ m _, _ => by simp only [Tm.closeAt]; rw [Tm.closeAt_nil (m := m)]
  | .ascV _ u _, _ => by simp only [Tm.closeAt]; rw [Val.closeAt_nil (u := u)]
  | .ite u m1 m2, _ => by
      simp only [Tm.closeAt]
      rw [Val.closeAt_nil (u := u), Tm.closeAt_nil (m := m1), Tm.closeAt_nil (m := m2)]
  | .add u w, _ => by
      simp only [Tm.closeAt]; rw [Val.closeAt_nil (u := u), Val.closeAt_nil (u := w)]
  | .errD _, _ => rfl
end

mutual
/-- Closing with `v :: ρ` substitutes `v` first, then closes with `ρ`
(closed `v`). -/
theorem Raw.closeAt_cons : ∀ {u : Raw} {k : ℕ} {v : Val} {ρ : List Val},
    v.FvBelow 0 → u.closeAt k (v :: ρ) = (u.subst k v).closeAt k ρ
  | .real _, _, _, _, _ => by simp [Raw.closeAt, Raw.subst]
  | .bool _, _, _, _, _ => by simp [Raw.closeAt, Raw.subst]
  | .lam σ m, k, v, ρ, hv => by
      simp only [Raw.closeAt, Raw.subst]
      rw [Val.rename_below hv (Nat.zero_le 0), Tm.closeAt_cons (m := m) hv]
/-- Closing a value with `v :: ρ` substitutes `v` first, then closes with `ρ`
(closed `v`). -/
theorem Val.closeAt_cons : ∀ {u : Val} {k : ℕ} {v : Val} {ρ : List Val},
    v.FvBelow 0 → u.closeAt k (v :: ρ) = (u.subst k v).closeAt k ρ
  | .var x, k, v, ρ, hv => by
      rcases Nat.lt_trichotomy x k with hx | rfl | hx
      · simp [Val.closeAt, Val.subst, hx, Nat.ne_of_lt hx, Nat.not_lt_of_gt hx]
      · simp [Val.closeAt, Val.subst, Val.closeAt_below hv (Nat.zero_le x)]
      · have h1 : x - k = (x - 1 - k) + 1 := by omega
        simp only [Val.closeAt, Val.subst, if_neg (Nat.not_lt.2 (Nat.le_of_lt hx)),
          if_neg (Nat.ne_of_gt hx), if_pos hx,
          if_neg (show ¬ x - 1 < k by omega), h1, List.getElem?_cons_succ,
          List.length_cons]
        congr 2; omega
  | .asc ε u σ, _, _, _, hv => by
      simp only [Val.closeAt, Val.subst]; rw [Raw.closeAt_cons (u := u) hv]
  | .err _, _, _, _, _ => by simp [Val.closeAt, Val.subst]
/-- Closing a term with `v :: ρ` substitutes `v` first, then closes with `ρ`
(closed `v`). -/
theorem Tm.closeAt_cons : ∀ {m : Tm} {k : ℕ} {v : Val} {ρ : List Val},
    v.FvBelow 0 → m.closeAt k (v :: ρ) = (m.subst k v).closeAt k ρ
  | .val u, _, _, _, hv => by
      simp only [Tm.closeAt, Tm.subst]; rw [Val.closeAt_cons (u := u) hv]
  | .app u w, _, _, _, hv => by
      simp only [Tm.closeAt, Tm.subst]
      rw [Val.closeAt_cons (u := u) hv, Val.closeAt_cons (u := w) hv]
  | .letin m _ ns, _, _, _, hv => by
      rw [Tm.subst_letin, Val.rename_below hv (Nat.zero_le 0)]
      simp only [Tm.closeAt]
      rw [Tm.closeAt_cons (m := m) hv]
      congr 1; funext i
      exact Tm.closeAt_cons (m := ns i) hv
  | .choice _ m1 m2, _, _, _, hv => by
      simp only [Tm.closeAt, Tm.subst]
      rw [Tm.closeAt_cons (m := m1) hv, Tm.closeAt_cons (m := m2) hv]
  | .ascT _ m _, _, _, _, hv => by
      simp only [Tm.closeAt, Tm.subst]; rw [Tm.closeAt_cons (m := m) hv]
  | .ascV _ u _, _, _, _, hv => by
      simp only [Tm.closeAt, Tm.subst]; rw [Val.closeAt_cons (u := u) hv]
  | .ite u m1 m2, _, _, _, hv => by
      simp only [Tm.closeAt, Tm.subst]
      rw [Val.closeAt_cons (u := u) hv, Tm.closeAt_cons (m := m1) hv,
        Tm.closeAt_cons (m := m2) hv]
  | .add u w, _, _, _, hv => by
      simp only [Tm.closeAt, Tm.subst]
      rw [Val.closeAt_cons (u := u) hv, Val.closeAt_cons (u := w) hv]
  | .errD _, _, _, _, _ => by simp [Tm.closeAt, Tm.subst]
end

/-! ### TPLC closure homomorphisms

The congruence equations that the fundamental property rewrites with. -/

/-- Closing commutes with the conditional. -/
theorem Tm.closeAt_ite {ρ : List Val} {u : Val} {m1 m2 : Tm} {k : ℕ} :
    (Tm.ite u m1 m2).closeAt k ρ
      = .ite (u.closeAt k ρ) (m1.closeAt k ρ) (m2.closeAt k ρ) := rfl

/-- `closeAt` on an ascribed raw value. -/
theorem Val.closeAt_asc {ρ : List Val} {ε : TagTy} {u : Raw} {σ : FTy} {k : ℕ} :
    (Val.asc ε u σ).closeAt k ρ = .asc ε (u.closeAt k ρ) σ := rfl

/-- Closing a raw `lam` closes the body one binder up. -/
theorem Raw.closeAt_lam {ρ : List Val} {σ : FTy} {mb : Tm} {k : ℕ} :
    (Raw.lam σ mb).closeAt k ρ = .lam σ (mb.closeAt (k + 1) ρ) := rfl

/-- Closing a `letin` closes the family one binder up. -/
theorem Tm.closeAt_letin {ρ : List Val} {m : Tm} {n : ℕ} {ns : Fin n → Tm} {k : ℕ} :
    (Tm.letin m n ns).closeAt k ρ
      = .letin (m.closeAt k ρ) n (fun i => (ns i).closeAt (k + 1) ρ) := rfl

/-- Variable lookup under closure. -/
theorem Val.closeAt_var {ρ : List Val} {x k : ℕ} (hx : x < ρ.length) :
    (Val.var (k + x)).closeAt k ρ = ρ[x] := by
  simp [Val.closeAt, hx]

/-- A closing substitution (of closed values) commutes with a substitution at a
lower index: `(m.closeAt (k+1) ρ).subst k w = (m.subst k w).closeAt k ρ`. -/
theorem Tm.closeAt_subst_comm : ∀ {ρ : List Val} {m : Tm} {k : ℕ}
    {w : Val}, (∀ v ∈ ρ, v.FvBelow 0) → w.FvBelow 0 →
    (m.closeAt (k + 1) ρ).subst k w = (m.subst k w).closeAt k ρ
  | [], _, _, _, _, _ => by rw [Tm.closeAt_nil, Tm.closeAt_nil]
  | v :: ρ, m, k, w, hρ, hw => by
      have hv : v.FvBelow 0 := hρ v (by simp)
      rw [Tm.closeAt_cons hv, Tm.closeAt_cons hv,
        Tm.closeAt_subst_comm (ρ := ρ) (fun u hu => hρ u (by simp [hu])) hw,
        Tm.subst_comm (m := m) hv hw]

/-! ## Reducible environments -/

/-- A reducible environment: closed values, typed by the context, each
reducible at the skeleton of its type. -/
def NormEnv : List FTy → List Val → Prop
  | [], [] => True
  | σ :: Γ, w :: ρ =>
      HasTyV [] w σ ∧ NormV (skelFTy σ) w ∧ NormEnv Γ ρ
  | _, _ => False

/-- The empty environment is reducible. -/
theorem normEnv_nil : NormEnv [] [] := trivial

/-- Extending a reducible environment with a closed value of type `σ` that is
reducible at the skeleton of `σ` gives a reducible environment. -/
theorem normEnv_cons {σ : FTy} {Γ : List FTy} {w : Val} {ρ : List Val}
    (hty : HasTyV [] w σ) (hn : NormV (skelFTy σ) w)
    (hρ : NormEnv Γ ρ) : NormEnv (σ :: Γ) (w :: ρ) := ⟨hty, hn, hρ⟩

/-! ### Rule (Dv) and point types -/

/-- The skeleton list of a point type `pointF σ` is `[skelFTy σ]`. -/
@[simp] theorem skelFD_point (σ : FTy) : skelFD (pointF σ) = [skelFTy σ] := by
  simp [skelFD, List.ofFn_succ]

/-- The skeleton of a point type `pointF σ`, read at its only entry. -/
theorem skelFD_point_get (σ : FTy) :
    (skelFD (pointF σ)).get ⟨0, by simp⟩ = skelFTy σ := by
  simp only [List.get_eq_getElem]
  have := List.getElem_of_eq (skelFD_point σ)
    (by simp : 0 < (skelFD (pointF σ)).length)
  simpa using this

/-- Rule (Dv): a well-typed reducible value is a reducible term. -/
theorem normT_val {σ : FTy} {v : Val} (hty : HasTyV [] v σ)
    (h : NormV (skelFTy σ) v) : NormT (skelFD (pointF σ)) (.val v) := by
  refine ⟨1, DConf.point v, Red.dv, fun i => ?_⟩
  refine ⟨⟨0, by simp⟩, ?_, ?_⟩
  · rw [skelFD_point_get, show (DConf.point v).val i = v from rfl,
      tyEntry_of_hasTy hty]
    exact SkelEq.refl _
  · rw [skelFD_point_get]
    exact h

/-- Rule (Derr): the distribution error converges, with one `error` outcome per
entry, each at its own entry of the declared type. -/
theorem normT_errD {μ : FDist} : NormT (skelFD μ) (.errD μ) := by
  refine ⟨1, DConf.errAt μ, Red.derr, fun i => ?_⟩
  refine ⟨Fin.cast (skelFD_length μ).symm i, ?_, normV_err⟩
  rw [skelFD_get μ i]
  exact SkelEq.refl _

/-! ### Indices of the choice operators

`chooseSem`/`chooseSemU` concatenate entries, so a branch index is transported
with `Fin.castAdd`/`Fin.natAdd`.  The lemmas are stated with `get`, which is
all that `NormT` uses. -/

/-- The skeleton of `chooseSem a D1 D2` at a left index is that of `D1`. -/
theorem skelFD_choose_left (a : ℝ) (D1 D2 : FDist) (i : Fin D1.n) :
    (skelFD (chooseSem a D1 D2)).get
        (Fin.cast (skelFD_length _).symm (Fin.castAdd D2.n i))
      = skelFTy (D1.ty i) := by
  rw [skelFD_get (chooseSem a D1 D2) (Fin.castAdd D2.n i)]
  simp [chooseSem, Fin.append_left]

/-- The skeleton of `chooseSem a D1 D2` at a right index is that of `D2`. -/
theorem skelFD_choose_right (a : ℝ) (D1 D2 : FDist) (j : Fin D2.n) :
    (skelFD (chooseSem a D1 D2)).get
        (Fin.cast (skelFD_length _).symm (Fin.natAdd D1.n j))
      = skelFTy (D2.ty j) := by
  rw [skelFD_get (chooseSem a D1 D2) (Fin.natAdd D1.n j)]
  simp [chooseSem, Fin.append_right]

/-- The skeleton of `chooseSemU D1 D2` at a left index is that of `D1`: the
skeletons of `chooseSemU` are those of `chooseSem`, which has the same entries. -/
theorem skelFD_chooseU_left (D1 D2 : FDist) (i : Fin D1.n) :
    (skelFD (chooseSemU D1 D2)).get
        (Fin.cast (skelFD_length _).symm (Fin.castAdd D2.n i))
      = skelFTy (D1.ty i) :=
  skelFD_choose_left 0 D1 D2 i

/-- The skeleton of `chooseSemU D1 D2` at a right index is that of `D2`. -/
theorem skelFD_chooseU_right (D1 D2 : FDist) (j : Fin D2.n) :
    (skelFD (chooseSemU D1 D2)).get
        (Fin.cast (skelFD_length _).symm (Fin.natAdd D1.n j))
      = skelFTy (D2.ty j) :=
  skelFD_choose_right 0 D1 D2 j

/-! ### Cases of the fundamental property without alignment

Each lemma takes the induction hypotheses as premises. -/

/-- The outcomes of rule (D⊕): the concatenation of reducible outcomes is
reducible at the concatenated skeletons; each index is transported by
`castAdd`/`natAdd`. `DConf.chooseU` and `chooseSemU` have the same outcomes and
skeletons as `DConf.choose` and `chooseSem`, so this serves both rules. -/
theorem normOut_choose (a : ℝ) {D1 D2 : FDist} {V1 V2 : DConf}
    (ho1 : NormOut (skelFD D1) V1) (ho2 : NormOut (skelFD D2) V2) :
    NormOut (skelFD (chooseSem a D1 D2)) (DConf.choose a V1 V2) := by
  intro c
  refine Fin.addCases ?_ ?_ c
  · intro i
    obtain ⟨j, hsk, hj⟩ := ho1 i
    have hval : (DConf.choose a V1 V2).val (Fin.castAdd V2.n i) = V1.val i := by
      simp [DConf.choose, Fin.append_left]
    refine ⟨Fin.cast (skelFD_length _).symm
      (Fin.castAdd D2.n (Fin.cast (skelFD_length D1) j)), ?_, ?_⟩
    · rw [skelFD_choose_left, hval, ← skelFD_get D1 (Fin.cast (skelFD_length D1) j)]
      simpa using hsk
    · rw [skelFD_choose_left, hval, ← skelFD_get D1 (Fin.cast (skelFD_length D1) j)]
      simpa using hj
  · intro i
    obtain ⟨j, hsk, hj⟩ := ho2 i
    have hval : (DConf.choose a V1 V2).val (Fin.natAdd V1.n i) = V2.val i := by
      simp [DConf.choose, Fin.append_right]
    refine ⟨Fin.cast (skelFD_length _).symm
      (Fin.natAdd D1.n (Fin.cast (skelFD_length D2) j)), ?_, ?_⟩
    · rw [skelFD_choose_right, hval, ← skelFD_get D2 (Fin.cast (skelFD_length D2) j)]
      simpa using hsk
    · rw [skelFD_choose_right, hval, ← skelFD_get D2 (Fin.cast (skelFD_length D2) j)]
      simpa using hj

/-- Rule (D⊕) with a known probability: both branches converge and the outcomes
are concatenated. -/
theorem normT_choice {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {m n : Tm}
    {D1 D2 : FDist} (h1 : NormT (skelFD D1) m) (h2 : NormT (skelFD D2) n) :
    NormT (skelFD (chooseSem a D1 D2)) (.choice (.q a) m n) := by
  obtain ⟨k1, V1, hr1, ho1⟩ := h1
  obtain ⟨k2, V2, hr2, ho2⟩ := h2
  exact ⟨k1 + k2 + 1, DConf.choose a V1 V2, .dchoice ha0 ha1 hr1 hr2,
    normOut_choose a ho1 ho2⟩

/-- Rule (D⊕) with unknown probability: as `normT_choice`, over the hull. -/
theorem normT_choiceU {m n : Tm} {D1 D2 : FDist}
    (h1 : NormT (skelFD D1) m) (h2 : NormT (skelFD D2) n) :
    NormT (skelFD (chooseSemU D1 D2)) (.choice .unk m n) := by
  obtain ⟨k1, V1, hr1, ho1⟩ := h1
  obtain ⟨k2, V2, hr2, ho2⟩ := h2
  exact ⟨k1 + k2 + 1, DConf.chooseU V1 V2, .dchoiceU hr1 hr2, normOut_choose 0 ho1 ho2⟩

/-- Rule (Dit): the conditional takes the true branch; the declared type is the
hull, so the index is transported by `castAdd`. -/
theorem normT_ite_true {ε : TagTy} {m n : Tm} {D1 D2 : FDist}
    (h1 : NormT (skelFD D1) m) :
    NormT (skelFD (chooseSemU D1 D2)) (.ite (.asc ε (.bool true) .bool) m n) := by
  obtain ⟨k1, V1, hr1, ho1⟩ := h1
  refine ⟨k1 + 1, V1, .dit hr1, ?_⟩
  intro i
  obtain ⟨j, hsk, hj⟩ := ho1 i
  refine ⟨Fin.cast (skelFD_length _).symm
    (Fin.castAdd D2.n (Fin.cast (skelFD_length D1) j)), ?_, ?_⟩
  · rw [skelFD_chooseU_left, ← skelFD_get D1 (Fin.cast (skelFD_length D1) j)]
    simpa using hsk
  · rw [skelFD_chooseU_left, ← skelFD_get D1 (Fin.cast (skelFD_length D1) j)]
    simpa using hj

/-- Rule (Dif): the false branch, transported by `natAdd`. -/
theorem normT_ite_false {ε : TagTy} {m n : Tm} {D1 D2 : FDist}
    (h2 : NormT (skelFD D2) n) :
    NormT (skelFD (chooseSemU D1 D2)) (.ite (.asc ε (.bool false) .bool) m n) := by
  obtain ⟨k2, V2, hr2, ho2⟩ := h2
  refine ⟨k2 + 1, V2, .dif hr2, ?_⟩
  intro i
  obtain ⟨j, hsk, hj⟩ := ho2 i
  refine ⟨Fin.cast (skelFD_length _).symm
    (Fin.natAdd D1.n (Fin.cast (skelFD_length D2) j)), ?_, ?_⟩
  · rw [skelFD_chooseU_right, ← skelFD_get D2 (Fin.cast (skelFD_length D2) j)]
    simpa using hsk
  · rw [skelFD_chooseU_right, ← skelFD_get D2 (Fin.cast (skelFD_length D2) j)]
    simpa using hj

/-- Rule (D+): the sum reduces (`add_total`), and by `entriesIn_red` every
outcome has type `ℝ`, of skeleton `base`, where reducibility is trivial. -/
theorem normT_add {v w : Val} (h : HasTyT [] (.add v w) (pointF .real)) :
    NormT (skelFD (pointF .real)) (.add v w) := by
  obtain ⟨k, V, hred⟩ := add_total h
  have hent := entriesIn_red hred h
  refine ⟨k, V, hred, fun i => ?_⟩
  obtain ⟨j, hj⟩ := hent i
  have hreal : (V.val i).tyEntry = FTy.real := by rw [hj]
  refine ⟨⟨0, by simp⟩, ?_, ?_⟩
  · rw [skelFD_point_get, hreal, skelFTy]
    exact .base
  · rw [skelFD_point_get, skelFTy, NormV]
    exact trivial

/-! ### Cases of the fundamental property with alignment

The alignment enters as a `SkelEq` premise on the evidences written in the
term. -/

/-- Rule (D::σ), value ascription.  Every outcome (the coerced value or the
error) has the target type, so the clause on its own skeleton holds by
reflexivity; reducibility moves from the source skeleton to the target one by
the alignment premise. -/
theorem normT_ascV {ε : TagTy} {v : Val} {σv σ' : FTy}
    (hty : HasTyT [] (.ascV ε v σ') (pointF σ'))
    (halign : SkelEq (skelFTy σv) (skelFTy σ'))
    (hv : NormV (skelFTy σv) v) :
    NormT (skelFD (pointF σ')) (.ascV ε v σ') := by
  obtain ⟨k, V, hred⟩ := ascV_step hty
  refine ⟨k, V, hred, fun i => ?_⟩
  have hout : NormV (skelFTy σv) (V.val i) := normV_ascV hv hred i
  have htv : (V.val i).tyEntry = σ' := by
    obtain ⟨w, hw, rfl⟩ := red_ascV_coerce hred
    exact Val.coerce_tyEntry hw
  refine ⟨⟨0, by simp⟩, ?_, ?_⟩
  · rw [skelFD_point_get, htv]
    exact SkelEq.refl _
  · rw [skelFD_point_get]
    exact (normV_skelEq halign).1 _ hout

/-- An ascribed λ is reducible at the skeleton of its declared type as soon as
its body is reducible at the skeleton of its raw type (binder annotation and
body type), given that the two skeletons are aligned.  The arrow clause speaks
of the raw λ, so the induction hypothesis is the body's. -/
theorem normV_lam {ε : TagTy} {σl σa : FTy} {tmb : Tm} {Da Db : FDist}
    (halign : SkelEq (skelFTy (.arrow σl Db)) (skelFTy (.arrow σa Da)))
    (ih : ∀ w : Val, HasTyV [] w σl → NormV (skelFTy σl) w →
            NormT (skelFD Db) (tmb.subst0 w)) :
    NormV (skelFTy (.arrow σa Da)) (.asc ε (.lam σl tmb) (.arrow σa Da)) := by
  refine (normV_skelEq halign).1 _ ?_
  rw [skelFTy, NormV]
  intro σl' tmb' ε' σ' heq w hw hnw
  cases heq
  exact ih w hw hnw

/-! ### Environments and closedness -/


/- A term typed in a context has its free variables below the context's
length; hence a term typed in the empty context is closed. -/
mutual
/-- A raw value typed in `Γ` has its free variables below the length of `Γ`. -/
theorem hasTy_below_raw : ∀ {Γ : List FTy} {u : Raw} {σ : FTy},
    HasTyRaw Γ u σ → u.FvBelow Γ.length
  | _, _, _, .real => by rw [Raw.FvBelow]; trivial
  | _, _, _, .bool => by rw [Raw.FvBelow]; trivial
  | Γ, _, _, .lam hm _ => by
      rw [Raw.FvBelow]
      simpa using hasTy_below_tm hm
/-- A value typed in `Γ` has its free variables below the length of `Γ`. -/
theorem hasTy_below_val : ∀ {Γ : List FTy} {v : Val} {σ : FTy},
    HasTyV Γ v σ → v.FvBelow Γ.length
  | _, _, _, .var hx => by
      rw [Val.FvBelow]
      exact List.getElem?_eq_some_iff.mp hx |>.1
  | _, _, _, .ascRaw hu _ _ _ => by
      rw [Val.FvBelow]; exact hasTy_below_raw hu
  | _, _, _, .err _ => by rw [Val.FvBelow]; trivial
/-- A term typed in `Γ` has its free variables below the length of `Γ`. -/
theorem hasTy_below_tm : ∀ {Γ : List FTy} {m : Tm} {D : FDist},
    HasTyT Γ m D → m.FvBelow Γ.length
  | _, _, _, .val hv => by rw [Tm.FvBelow]; exact hasTy_below_val hv
  | _, _, _, .app hv hw => by
      rw [Tm.FvBelow]; exact ⟨hasTy_below_val hv, hasTy_below_val hw⟩
  | Γ, _, _, @HasTyT.letin _ _ _ _ _ ns F hm hF => by
      rw [Tm.FvBelow]
      exact ⟨hasTy_below_tm hm, fun i => by simpa using hasTy_below_tm (hF i)⟩
  | _, _, _, .choice _ _ h1 h2 => by
      rw [Tm.FvBelow]; exact ⟨hasTy_below_tm h1, hasTy_below_tm h2⟩
  | _, _, _, .choiceU h1 h2 => by
      rw [Tm.FvBelow]; exact ⟨hasTy_below_tm h1, hasTy_below_tm h2⟩
  | _, _, _, .ascT hm _ _ _ => by rw [Tm.FvBelow]; exact hasTy_below_tm hm
  | _, _, _, .ascV hv _ _ _ => by rw [Tm.FvBelow]; exact hasTy_below_val hv
  | _, _, _, .ite hv h1 h2 => by
      rw [Tm.FvBelow]
      exact ⟨hasTy_below_val hv, hasTy_below_tm h1, hasTy_below_tm h2⟩
  | _, _, _, .add hv hw => by
      rw [Tm.FvBelow]; exact ⟨hasTy_below_val hv, hasTy_below_val hw⟩
  | _, _, _, .errD _ => by rw [Tm.FvBelow]; trivial
end

/-- A value typed in the empty context is closed. -/
theorem hasTy_closed_val {v : Val} {σ : FTy} (h : HasTyV [] v σ) :
    v.FvBelow 0 := by simpa using hasTy_below_val h

/-- Every value of a reducible environment is closed. -/
theorem normEnv_closed : ∀ {Γ : List FTy} {ρ : List Val},
    NormEnv Γ ρ → ∀ v ∈ ρ, v.FvBelow 0
  | [], [], _, v, hv => by simp at hv
  | σ :: Γ, w :: ρ, h, v, hv => by
      rcases List.mem_cons.1 hv with rfl | hm
      · exact hasTy_closed_val h.1
      · exact normEnv_closed (Γ := Γ) (ρ := ρ) h.2.2 v hm

/-- If `Γ` assigns `σ` to `x` and `ρ` is reducible for `Γ`, then `ρ` has a closed
value of type `σ` at `x`, reducible at the skeleton of `σ`. -/
theorem normEnv_get : ∀ {Γ : List FTy} {ρ : List Val} {x : ℕ} {σ : FTy},
    NormEnv Γ ρ → Γ[x]? = some σ →
    ∃ w, ρ[x]? = some w ∧ HasTyV [] w σ ∧ NormV (skelFTy σ) w
  | [], [], _, _, _, hx => by simp at hx
  | σ0 :: Γ, w0 :: ρ, 0, σ, h, hx => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact ⟨w0, rfl, h.1, h.2.1⟩
  | σ0 :: Γ, w0 :: ρ, (x+1), σ, h, hx => by
      simp only [List.getElem?_cons_succ] at hx
      obtain ⟨w, hw, hty, hn⟩ := normEnv_get (Γ := Γ) (ρ := ρ) h.2.2 hx
      exact ⟨w, by simpa using hw, hty, hn⟩

/-! ### Alignment for distribution ascriptions

Rule (D::μ) composes the computed reordering `tagReorderD V.confF μ` with the
evidence `εd` written in the term.  The alignment it needs is entrywise: for
each entry of the composed evidence, the skeleton of the runtime type of the
source value and that of the target entry are equivalent. -/


/-- The skeleton alignment a distribution ascription `εd` from `μ` to `μb`
needs: for every configuration `V0` and every entry of the composed evidence
`emeetD (tagReorderD V0.confF μ) εd`, the runtime type of the source value and
the target entry have equivalent skeletons. -/
def AscTAlign (εd : TagD) (μ μb : FDist) : Prop :=
  ∀ (V0 : DConf) (c : Fin (emeetD (tagReorderD V0.confF μ) εd).n)
    (hR : (emeetD (tagReorderD V0.confF μ) εd).r c < μb.n),
    SkelEq (skelFTy (V0.val (reorderDL V0.confF μ
      (meetDL (tagReorderD V0.confF μ).toF εd.toF c))).tyEntry) (skelFTy (μb.ty ⟨_, hR⟩))

/-- Rule (D::μ), distribution ascription.  The proof rebuilds the reduction as
in `dascD_total` instead of inverting it, to keep the configuration the
induction hypothesis provides (no determinism result for the reduction of TPLC
is proved, so an inverted derivation need not reduce the ascribed term to that
configuration).

Every outcome (the entrywise coercion or `error`) has an entry of `μb` as its
type (`tyEntry_of_red_ascV`), so the clause on its own skeleton holds by
reflexivity; reducibility moves from the source skeleton to the target one by
the alignment premise `AscTAlign`. -/
theorem normT_ascT {εd : TagD} {m : Tm} {μ μb : FDist} {ds : List Skel}
    (hty : HasTyT [] (.ascT εd m μb) μb) (htm : HasTyT [] m μ)
    (ih : NormT ds m) (halign : AscTAlign εd μ μb) :
    NormT (skelFD μb) (.ascT εd m μb) := by
  classical
  obtain ⟨k1, V0, hred0, hout0⟩ := ih
  obtain ⟨htm', hval, hgεd, hgμb⟩ :
      HasTyT [] m μ ∧ εd.HValidFor μ μb ∧ GoodD εd.toF ∧ GoodD μb := by
    cases hty with
    | ascT a b c d =>
      have hh := det_tm a htm
      subst hh
      exact ⟨a, b, c, d⟩
  by_cases hsat : ∃ w, (emeetD (tagReorderD V0.confF μ) εd).toF.C w
  · have hR : ∀ c : Fin (emeetD (tagReorderD V0.confF μ) εd).n,
        (emeetD (tagReorderD V0.confF μ) εd).r c < μb.n :=
      fun c => hval.2.tag_lt _
    have hcells : ∀ c : Fin (emeetD (tagReorderD V0.confF μ) εd).n, ∃ w,
        Red (.ascV ((emeetD (tagReorderD V0.confF μ) εd).ty c)
          (V0.val (reorderDL V0.confF μ (meetDL (tagReorderD V0.confF μ).toF εd.toF c)))
          (μb.ty ⟨_, hR c⟩)) 1 (DConf.point w) :=
      fun c => ascV_total (type_safety_vals hred0 htm' _) _ _
    choose wv hwv using hcells
    refine ⟨k1 + 1, _, Red.dascD hval hred0 htm' hsat hwv, ?_⟩
    intro c
    have hwty : (wv c).tyEntry = μb.ty ⟨_, hR c⟩ := tyEntry_of_red_ascV (hwv c)
    obtain ⟨j, hsk, hj⟩ :=
      hout0 (reorderDL V0.confF μ (meetDL (tagReorderD V0.confF μ).toF εd.toF c))
    refine ⟨Fin.cast (skelFD_length μb).symm ⟨_, hR c⟩, ?_, ?_⟩
    · show SkelEq (skelFTy (wv c).tyEntry) _
      rw [hwty, skelFD_get μb ⟨_, hR c⟩]
      exact SkelEq.refl _
    · show NormV _ (wv c)
      rw [skelFD_get μb ⟨_, hR c⟩]
      refine (normV_skelEq ?_).1 _ (normV_ascV hj (hwv c) ⟨0, by simp [DConf.point]⟩)
      exact SkelEq.trans (SkelEq.symm hsk) (halign V0 c (hR c))
  · refine ⟨k1 + 1, _, Red.dascDErr hval hred0 htm' hsat, ?_⟩
    intro c
    refine ⟨Fin.cast (skelFD_length μb).symm c, ?_, normV_err⟩
    rw [skelFD_get μb c]
    exact SkelEq.refl _

/-- The coerced argument of an application is typed at the binder annotation.
The domain evidence is the flipped one (`tagDom` returns the domain of the
evidence with its sides swapped). -/
theorem dapp_arg_typed {ε : TagTy} {σ' σa : FTy} {mb : Tm} {Dres : FDist}
    {v w : Val} {s : TagTy} {k1 : ℕ}
    (hv : HasTyV [] (.asc ε (.lam σ' mb) (.arrow σa Dres)) (.arrow σa Dres))
    (hw : HasTyV [] v σa) (hdom : tagDom ε = some s)
    (hred1 : Red (.ascV s v σ') k1 (DConf.point w)) :
    HasTyV [] w σ' := by
  cases hv with
  | ascRaw hlam hevε hgeε hgarr =>
    cases hlam with
    | lam hbody hgσ' =>
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
              obtain ⟨w', hco, hpt⟩ := red_ascV_coerce hred1
              obtain rfl := DConf.point_inj hpt
              exact Val.coerce_typed hw
                ⟨hvtag_flip hs2, hvtag_flip hs1⟩ hgsf hgσ' hco

/-- Rule (Dapp).  The arrow clause of reducibility gives the convergence of the
body with the coerced argument substituted; it remains to wrap it in the
ascription to the codomain, which is `normT_ascT`.  If the function is an
error, rule (Derr app) propagates it and every outcome is an error, reducible
at every skeleton. -/
theorem normT_app {v w : Val} {σ : FTy} {D : FDist}
    (hv : HasTyV [] v (.arrow σ D)) (hw : HasTyV [] w σ)
    (hnv : NormV (skelFTy (.arrow σ D)) v) (hnw : NormV (skelFTy σ) w)
    (halign : ∀ (d : TagD) (μ0 : FDist), AscTAlign d μ0 D) :
    NormT (skelFD D) (.app v w) := by
  classical
  rcases (show (∃ ε u, v = .asc ε u (.arrow σ D)) ∨ v = .err (.arrow σ D) from by
      cases hv with
      | var hx => simp at hx
      | ascRaw _ _ _ _ => exact .inl ⟨_, _, rfl⟩
      | err _ => exact .inr rfl) with ⟨ε, u, rfl⟩ | rfl
  · obtain ⟨σu, hu, hev, hgeε, hgarr⟩ :
        ∃ σu, HasTyRaw [] u σu ∧ HVTagTy ε σu (.arrow σ D) ∧
          GoodTy ε.toF ∧ GoodTy (.arrow σ D) := by
      cases hv with | ascRaw a b c d => exact ⟨_, a, b, c, d⟩
    -- the raw value must be a λ: against an arrow the evidence is an arrow,
    -- and an arrow evidence is not left-valid against `Real`/`Bool`
    cases hu with
    | real => cases hev.2 with | arrow _ _ => cases hev.1
    | bool => cases hev.2 with | arrow _ _ => cases hev.1
    | @lam _ σ' mb Db hbody hgσ' =>
      cases ε with
      | real => cases hev.2
      | bool => cases hev.2
      | unk => cases hev.2
      | arrow s0 d0 =>
        have hdom : tagDom (TagTy.arrow s0 d0) = some s0.flip := rfl
        have hcod : tagCod (TagTy.arrow s0 d0) = some d0 := rfl
        obtain ⟨wc, hargred⟩ :=
          ascV_total (v := w) (by rw [tyEntry_of_hasTy hw]; exact hw) s0.flip σ'
        have hwc : HasTyV [] wc σ' :=
          dapp_arg_typed (mb := mb) hv hw hdom hargred
        have hnwc : NormV (skelFTy σ) wc :=
          normV_ascV hnw hargred ⟨0, by simp [DConf.point]⟩
        have hbodyN : NormT (skelFD D) (mb.subst0 wc) := by
          rw [skelFTy, NormV] at hnv
          exact hnv σ' mb (.arrow s0 d0) (.arrow σ D) rfl wc hwc hnwc
        have hcontr : HasTyT [] ((Tm.ascT d0 mb D).subErr wc D) D :=
          dapp_contractum_typed hv hw hdom hcod hargred
        have hcN : NormT (skelFD D) ((Tm.ascT d0 mb D).subErr wc D) := by
          cases hwcase : wc with
          | err σe =>
              rw [hwcase] at hcontr
              exact normT_errD
          | var x =>
              exfalso
              rw [hwcase] at hwc
              cases hwc with | var hx => simp at hx
          | asc εw uw σw =>
              rw [hwcase] at hcontr hbodyN
              rw [Tm.subErr_asc] at hcontr ⊢
              simp only [Tm.subst0, Tm.subst] at hcontr ⊢
              obtain ⟨μ0, htm0, -, -, -⟩ :
                  ∃ μ0, HasTyT [] (mb.subst0 (.asc εw uw σw)) μ0 ∧
                    d0.HValidFor μ0 D ∧ GoodD d0.toF ∧ GoodD D := by
                cases hcontr with | ascT a b c d => exact ⟨_, a, b, c, d⟩
              exact normT_ascT hcontr htm0 hbodyN (halign d0 μ0)
        obtain ⟨k2, V, hredc, houtc⟩ := hcN
        exact ⟨1 + k2 + 1, V, Red.dapp hdom hcod hargred hredc, houtc⟩
  · refine ⟨1, DConf.errAt D, Red.eApp, fun c => ?_⟩
    refine ⟨Fin.cast (skelFD_length D).symm c, ?_, normV_err⟩
    rw [skelFD_get D c]
    exact SkelEq.refl _

/-! ### Rule (Dlet)

This case needs no alignment premise: the routing evidence is
`tagReorderD V.confF μ`, whose entries pair types that are syntactically equal
(`reorderD_cell_eq`), so the entrywise coercion sends each value to its own type. -/

/-- The skeleton of the type `letSem D F` of a `let`, read at an entry. -/
theorem skelFD_letSem_get (D : FDist) (F : Fin D.n → FDist)
    (k : Fin (letSem D F).n) :
    (skelFD (letSem D F)).get (Fin.cast (skelFD_length _).symm k)
      = skelFTy ((F (finSigmaFinEquiv.symm k).1).ty
          (finSigmaFinEquiv.symm k).2) :=
  skelFD_get (letSem D F) k

/-- The entry of `μ` that an entry of the computed reordering targets is the
runtime type of the value it routes: the entries pair syntactically equal
types. -/
theorem tagReorderD_cell_eq (V : DConf) (μ : FDist)
    (c : Fin (tagReorderD V.confF μ).n) :
    (V.val (reorderDL V.confF μ c)).tyEntry = μ.ty (reorderDR V.confF μ c) :=
  reorderD_cell_eq V.confF μ c

/-- Rule (Dlet): if the bound term is reducible and each body, with its variable
replaced by a reducible closed value of its entry type, is reducible, then the
`let` is reducible at the skeletons of `letSem μ F`. -/
theorem normT_letin {m : Tm} {μ : FDist} {ns : Fin μ.n → Tm}
    {F : Fin μ.n → FDist}
    (htm : HasTyT [] m μ) (hgμ : GoodD μ)
    (hbty : ∀ i : Fin μ.n, HasTyT [μ.ty i] (ns i) (F i))
    (ih : NormT (skelFD μ) m)
    (ihb : ∀ (i : Fin μ.n) (w : Val), HasTyV [] w (μ.ty i) →
      NormV (skelFTy (μ.ty i)) w →
      NormT (skelFD (F i)) ((ns i).subErr w (F i))) :
    NormT (skelFD (letSem μ F)) (.letin m μ.n ns) := by
  classical
  obtain ⟨k1, V, hred0, hout0⟩ := ih
  have hVvals := type_safety_vals hred0 htm
  -- the entrywise coercion reduces
  have hcells : ∀ c : Fin (tagReorderD V.confF μ).n, ∃ w,
      Red (.ascV ((tagReorderD V.confF μ).ty c) (V.val (reorderDL V.confF μ c))
        (μ.ty (reorderDR V.confF μ c))) 1 (DConf.point w) :=
    fun c => ascV_total (hVvals _) _ _
  choose wv hwv using hcells
  have hwtyped : ∀ c, HasTyV [] (wv c) (μ.ty (reorderDR V.confF μ c)) :=
    fun c => dlet_cell_typed hVvals hgμ (hwv c)
  -- the coerced value is reducible at the skeleton of its own entry
  have hwnorm : ∀ c, NormV (skelFTy (μ.ty (reorderDR V.confF μ c))) (wv c) := by
    intro c
    obtain ⟨j, hsk, hj⟩ := hout0 (reorderDL V.confF μ c)
    have hcoer : NormV ((skelFD μ).get j) (wv c) :=
      normV_ascV hj (hwv c) ⟨0, by simp [DConf.point]⟩
    refine (normV_skelEq ?_).1 _ hcoer
    have heq := tagReorderD_cell_eq V μ c
    rw [heq] at hsk
    exact SkelEq.symm hsk
  -- each body converges; the derivation indices are raised to a common bound
  have hbodies : ∀ c : Fin (tagReorderD V.confF μ).n, NormT (skelFD (F (reorderDR V.confF μ c)))
      ((ns (reorderDR V.confF μ c)).subErr (wv c) (F (reorderDR V.confF μ c))) :=
    fun c => ihb (reorderDR V.confF μ c) (wv c) (hwtyped c) (hwnorm c)
  choose kb Vk hkb hVkout using hbodies
  set K := Finset.univ.sup kb with hK
  have hbred : ∀ c, Red ((ns (reorderDR V.confF μ c)).subErr (wv c) (F (reorderDR V.confF μ c)))
      K (Vk c) :=
    fun c => red_index_mono (hkb c) (Finset.le_sup (Finset.mem_univ c))
  refine ⟨k1 + K + 1, DConf.wsum (tagReorderD V.confF μ).toF.C Vk,
    Red.dlet' hred0 htm hwv (fun c => hbty _) hbred, ?_⟩
  -- the outcomes
  intro k
  set c := (finSigmaFinEquiv.symm k).1 with hc
  set i := (finSigmaFinEquiv.symm k).2 with hi
  obtain ⟨j, hsk, hj⟩ := hVkout c i
  refine ⟨Fin.cast (skelFD_length _).symm
    (finSigmaFinEquiv ⟨reorderDR V.confF μ c, Fin.cast (skelFD_length _) j⟩), ?_, ?_⟩
  · rw [skelFD_letSem_get, Equiv.symm_apply_apply]
    rw [← skelFD_get (F (reorderDR V.confF μ c)) (Fin.cast (skelFD_length _) j)]
    simpa using hsk
  · rw [skelFD_letSem_get, Equiv.symm_apply_apply]
    rw [← skelFD_get (F (reorderDR V.confF μ c)) (Fin.cast (skelFD_length _) j)]
    simpa using hj

/-! ### Weakening by append and closure

The typing of a closed term is obtained one value of the environment at a
time (`Tm.closeAt_cons`): each value is substituted at index 0 and must be
typed in the context of the remaining variables.  Hence weakening by append: a
term whose free variables lie within `Δ` has the same type in `Δ ++ Γ`. -/

mutual
/-- Weakening by append: a raw value typed in `Δ` with free variables below the
length of `Δ` has the same type in `Δ ++ Γ`. -/
theorem hasTy_wkapp_raw : ∀ {Δ : List FTy} {u : Raw} {s : FTy},
    HasTyRaw Δ u s → u.FvBelow Δ.length → ∀ Γ, HasTyRaw (Δ ++ Γ) u s
  | _, _, _, .real, _, _ => .real
  | _, _, _, .bool, _, _ => .bool
  | Δ, _, _, @HasTyRaw.lam _ σ0 mb Db hm hg, hb, Γ => by
      refine .lam ?_ hg
      have hb2 : mb.FvBelow (σ0 :: Δ).length := by
        rw [Raw.FvBelow] at hb; simpa using hb
      have := hasTy_wkapp_tm (Δ := σ0 :: Δ) hm hb2 Γ
      simpa using this
/-- Weakening by append: a value typed in `Δ` with free variables below the
length of `Δ` has the same type in `Δ ++ Γ`. -/
theorem hasTy_wkapp_val : ∀ {Δ : List FTy} {v : Val} {s : FTy},
    HasTyV Δ v s → v.FvBelow Δ.length → ∀ Γ, HasTyV (Δ ++ Γ) v s
  | Δ, _, _, .var hx, hb, Γ => by
      refine .var ?_
      rw [List.getElem?_append_left (by rw [Val.FvBelow] at hb; exact hb)]
      exact hx
  | _, _, _, .ascRaw hu hev hg1 hg2, hb, Γ =>
      .ascRaw (hasTy_wkapp_raw hu (by rw [Val.FvBelow] at hb; exact hb) Γ)
        hev hg1 hg2
  | _, _, _, .err hg, _, _ => .err hg
/-- Weakening by append: a term typed in `Δ` with free variables below the
length of `Δ` has the same type in `Δ ++ Γ`. -/
theorem hasTy_wkapp_tm : ∀ {Δ : List FTy} {m : Tm} {D : FDist},
    HasTyT Δ m D → m.FvBelow Δ.length → ∀ Γ, HasTyT (Δ ++ Γ) m D
  | _, _, _, .val hv, hb, Γ =>
      .val (hasTy_wkapp_val hv (by rw [Tm.FvBelow] at hb; exact hb) Γ)
  | _, _, _, .app hv hw, hb, Γ => by
      rw [Tm.FvBelow] at hb
      exact .app (hasTy_wkapp_val hv hb.1 Γ) (hasTy_wkapp_val hw hb.2 Γ)
  | Δ, _, _, @HasTyT.letin _ _ _ ty _ nsx Fx hm hF, hb, Γ => by
      rw [Tm.FvBelow] at hb
      refine .letin (hasTy_wkapp_tm hm hb.1 Γ) (fun i => ?_)
      have := hasTy_wkapp_tm (Δ := ty i :: Δ) (hF i) (by simpa using hb.2 i) Γ
      simpa using this
  | _, _, _, .choice ha0 ha1 h1 h2, hb, Γ => by
      rw [Tm.FvBelow] at hb
      exact .choice ha0 ha1 (hasTy_wkapp_tm h1 hb.1 Γ) (hasTy_wkapp_tm h2 hb.2 Γ)
  | _, _, _, .choiceU h1 h2, hb, Γ => by
      rw [Tm.FvBelow] at hb
      exact .choiceU (hasTy_wkapp_tm h1 hb.1 Γ) (hasTy_wkapp_tm h2 hb.2 Γ)
  | _, _, _, .ascT hm hval hg1 hg2, hb, Γ =>
      .ascT (hasTy_wkapp_tm hm (by rw [Tm.FvBelow] at hb; exact hb) Γ)
        hval hg1 hg2
  | _, _, _, .ascV hv hev hg1 hg2, hb, Γ =>
      .ascV (hasTy_wkapp_val hv (by rw [Tm.FvBelow] at hb; exact hb) Γ)
        hev hg1 hg2
  | _, _, _, .ite hv h1 h2, hb, Γ => by
      rw [Tm.FvBelow] at hb
      exact .ite (hasTy_wkapp_val hv hb.1 Γ) (hasTy_wkapp_tm h1 hb.2.1 Γ)
        (hasTy_wkapp_tm h2 hb.2.2 Γ)
  | _, _, _, .add hv hw, hb, Γ => by
      rw [Tm.FvBelow] at hb
      exact .add (hasTy_wkapp_val hv hb.1 Γ) (hasTy_wkapp_val hw hb.2 Γ)
  | _, _, _, .errD hg, _, _ => .errD hg
end

/-- A closed well-typed value has the same type in any context. -/
theorem hasTy_val_any {Γ : List FTy} {w : Val} {s : FTy}
    (h : HasTyV [] w s) : HasTyV Γ w s := by
  have := hasTy_wkapp_val h (by simpa using hasTy_closed_val h) Γ
  simpa using this

/-- Closing by a reducible environment preserves typing. -/
theorem hasTy_closeEnv_tm : ∀ {Γ : List FTy} {ρ : List Val} {m : Tm} {D : FDist},
    NormEnv Γ ρ → HasTyT Γ m D → HasTyT [] (m.close ρ) D
  | [], [], m, D, _, h => by rwa [Tm.close, Tm.closeAt_nil]
  | s0 :: Γ, w :: ρ, m, D, hrho, h => by
      rw [Tm.close, Tm.closeAt_cons (hasTy_closed_val hrho.1)]
      exact hasTy_closeEnv_tm hrho.2.2
        (hasTy_subst_tm m (Δ := []) (hasTy_val_any hrho.1) h)

/-- Closing a value by a reducible environment preserves its type. -/
theorem hasTy_closeEnv_val : ∀ {Γ : List FTy} {ρ : List Val} {v : Val} {s : FTy},
    NormEnv Γ ρ → HasTyV Γ v s → HasTyV [] (v.close ρ) s
  | [], [], v, s, _, h => by rwa [Val.close, Val.closeAt_nil]
  | s0 :: Γ, w :: ρ, v, s, hrho, h => by
      rw [Val.close, Val.closeAt_cons (hasTy_closed_val hrho.1)]
      exact hasTy_closeEnv_val hrho.2.2
        (hasTy_subst_val v (Δ := []) (hasTy_val_any hrho.1) h)

/-! ### The aligned typing judgment

A copy of the TPLC typing with alignment premises at the positions of the
evidences written in the term.  It is a judgment of its own, rather than a
predicate beside a typing derivation, so that the induction runs on a single
derivation. -/

mutual
/-- Aligned typing of raw values: TPLC typing of raw values. -/
inductive NRaw : List FTy → Raw → FTy → Prop where
  | real : ∀ {G r}, NRaw G (.real r) .real
  | bool : ∀ {G b}, NRaw G (.bool b) .bool
  | lam  : ∀ {G s m D}, NTm (s :: G) m D → GoodTy s ->
             NRaw G (.lam s m) (.arrow s D)
/-- Aligned typing of values: TPLC typing of values, with the skeletons of the
raw type and the ascribed type equivalent. -/
inductive NVal : List FTy → Val → FTy → Prop where
  | var    : ∀ {G x s}, G[x]? = some s → NVal G (.var x) s
  | ascRaw : ∀ {G} {e : TagTy} {u su s}, NRaw G u su → HVTagTy e su s ->
               GoodTy e.toF → GoodTy s → SkelEq (skelFTy su) (skelFTy s) ->
               NVal G (.asc e u s) s
  | err    : ∀ {G s}, GoodTy s → NVal G (.err s) s
/-- Aligned typing of terms: TPLC typing of terms, with alignment premises on
the evidences of `app` (via the codomain), `ascT` and `ascV`. -/
inductive NTm : List FTy → Tm → FDist → Prop where
  | val    : ∀ {G v s}, NVal G v s → NTm G (.val v) (pointF s)
  | app    : ∀ {G v w s D}, NVal G v (.arrow s D) → NVal G w s ->
               (∀ (d : TagD) (m0 : FDist), AscTAlign d m0 D) ->
               NTm G (.app v w) D
  | letin  : ∀ {G m n} {ty : Fin n → FTy} {C : (Fin n → ℝ) → Prop}
               {ns : Fin n → Tm} {F : Fin n → FDist},
               NTm G m ⟨n, ty, C⟩ → (∀ i, NTm (ty i :: G) (ns i) (F i)) ->
               NTm G (.letin m n ns) (letSem ⟨n, ty, C⟩ F)
  | choice : ∀ {G m n D1 D2} {a : ℝ}, 0 ≤ a → a ≤ 1 ->
               NTm G m D1 → NTm G n D2 ->
               NTm G (.choice (.q a) m n) (chooseSem a D1 D2)
  | choiceU : ∀ {G m n D1 D2}, NTm G m D1 → NTm G n D2 ->
               NTm G (.choice .unk m n) (chooseSemU D1 D2)
  | ascT   : ∀ {G} {e : TagD} {m D Db}, NTm G m D → e.HValidFor D Db ->
               GoodD e.toF → GoodD Db → AscTAlign e D Db ->
               NTm G (.ascT e m Db) Db
  | ascV   : ∀ {G} {e : TagTy} {v s s'}, NVal G v s → HVTagTy e s s' ->
               GoodTy e.toF → GoodTy s' → SkelEq (skelFTy s) (skelFTy s') ->
               NTm G (.ascV e v s') (pointF s')
  | ite    : ∀ {G v m n D1 D2}, NVal G v .bool → NTm G m D1 → NTm G n D2 ->
               NTm G (.ite v m n) (chooseSemU D1 D2)
  | add    : ∀ {G v w}, NVal G v .real → NVal G w .real ->
               NTm G (.add v w) (pointF .real)
  | errD   : ∀ {G} {D : FDist}, GoodD D → NTm G (.errD D) D
end

/-! ### Projection to the TPLC typing -/

mutual
/-- An aligned typing of a raw value is a TPLC typing. -/
theorem nraw_hasTy : ∀ {G : List FTy} {u : Raw} {s : FTy},
    NRaw G u s → HasTyRaw G u s
  | _, _, _, .real => .real
  | _, _, _, .bool => .bool
  | _, _, _, .lam hm hg => .lam (ntm_hasTy hm) hg
/-- An aligned typing of a value is a TPLC typing. -/
theorem nval_hasTy : ∀ {G : List FTy} {v : Val} {s : FTy},
    NVal G v s → HasTyV G v s
  | _, _, _, .var hx => .var hx
  | _, _, _, .ascRaw hu he hg1 hg2 _ => .ascRaw (nraw_hasTy hu) he hg1 hg2
  | _, _, _, .err hg => .err hg
/-- An aligned typing of a term is a TPLC typing. -/
theorem ntm_hasTy : ∀ {G : List FTy} {m : Tm} {D : FDist},
    NTm G m D → HasTyT G m D
  | _, _, _, .val hv => .val (nval_hasTy hv)
  | _, _, _, .app hv hw _ => .app (nval_hasTy hv) (nval_hasTy hw)
  | _, _, _, .letin hm hF => .letin (ntm_hasTy hm) (fun i => ntm_hasTy (hF i))
  | _, _, _, .choice h0 h1 hm hn => .choice h0 h1 (ntm_hasTy hm) (ntm_hasTy hn)
  | _, _, _, .choiceU hm hn => .choiceU (ntm_hasTy hm) (ntm_hasTy hn)
  | _, _, _, .ascT hm hv hg1 hg2 _ => .ascT (ntm_hasTy hm) hv hg1 hg2
  | _, _, _, .ascV hv he hg1 hg2 _ => .ascV (nval_hasTy hv) he hg1 hg2
  | _, _, _, .ite hv hm hn => .ite (nval_hasTy hv) (ntm_hasTy hm) (ntm_hasTy hn)
  | _, _, _, .add hv hw => .add (nval_hasTy hv) (nval_hasTy hw)
  | _, _, _, .errD hg => .errD hg
end

/-! ### Auxiliary lemmas for the fundamental property -/

/-- Closing under a context prefix `Δ`, as needed for the bodies of a `let`,
which keep one free variable. -/
theorem hasTy_closeEnvAt_tm : ∀ {Δ : List FTy} {G : List FTy} {ρ : List Val}
    {m : Tm} {D : FDist},
    NormEnv G ρ → HasTyT (Δ ++ G) m D → HasTyT Δ (m.closeAt Δ.length ρ) D
  | Δ, [], [], m, D, _, h => by rw [Tm.closeAt_nil]; simpa using h
  | Δ, σ0 :: G, w :: ρ, m, D, hρ, h => by
      rw [Tm.closeAt_cons (hasTy_closed_val hρ.1)]
      exact hasTy_closeEnvAt_tm hρ.2.2
        (hasTy_subst_tm m (Δ := Δ) (hasTy_val_any hρ.1) h)

/-! ## The fundamental property

Every term with an aligned typing, closed by a reducible environment, is
reducible.  By induction on the aligned derivation; each case is one of the
lemmas above. -/

mutual
/-- The fundamental property for values: a value with an aligned typing at `s`,
closed by a reducible environment, is reducible at the skeleton of `s`. -/
theorem norm_val : ∀ {G : List FTy} {v : Val} {s : FTy} {ρ : List Val},
    NVal G v s → NormEnv G ρ → NormV (skelFTy s) (v.close ρ)
  | _, _, s, ρ, @NVal.var _ x _ hx, hρ => by
      obtain ⟨w, hw, hty, hn⟩ := normEnv_get hρ hx
      have hxlt : x < ρ.length := (List.getElem?_eq_some_iff.mp hw).1
      have hcv := Val.closeAt_var (ρ := ρ) (x := x) (k := 0) hxlt
      have hwe : ρ[x] = w := by
        have := hw
        rw [List.getElem?_eq_getElem hxlt] at this
        exact Option.some_inj.mp this
      simp only [Val.close]
      rw [show (Val.var x) = Val.var (0 + x) by simp, hcv, hwe]
      exact hn
  | _, _, _, ρ, .err hg, hρ =>
      normV_err
  | _, _, _, ρ, .ascRaw .real _ _ _ _, hρ => by
      simp only [Val.close]
      rw [Val.closeAt_asc,
        Raw.closeAt_below (n := 0) (by rw [Raw.FvBelow]; trivial) (le_refl 0)]
      exact normV_real
  | _, _, _, ρ, .ascRaw .bool _ _ _ _, hρ => by
      simp only [Val.close]
      rw [Val.closeAt_asc,
        Raw.closeAt_below (n := 0) (by rw [Raw.FvBelow]; trivial) (le_refl 0)]
      exact normV_bool
  | _, _, s, ρ, @NVal.ascRaw _ e _ _ _ (@NRaw.lam _ sl mb Db hbody hgsl)
      hev hg1 hg2 halign, hρ => by
      simp only [Val.close]
      rw [Val.closeAt_asc, Raw.closeAt_lam]
      cases s with
      | real => rw [skelFTy, NormV]; trivial
      | bool => rw [skelFTy, NormV]; trivial
      | unk => rw [skelFTy, NormV]; trivial
      | arrow sa Da =>
          refine normV_lam (Db := Db) halign (fun w hw hnw => ?_)
          have hb := norm_tm (ρ := w :: ρ) hbody (normEnv_cons hw hnw hρ)
          rw [Tm.close, Tm.closeAt_cons (hasTy_closed_val hw),
            ← Tm.closeAt_subst_comm (ρ := ρ) (k := 0)
              (normEnv_closed hρ) (hasTy_closed_val hw)] at hb
          exact hb
  termination_by structural G v s ρ hd hρ => hd
/-- The fundamental property for terms: a term with an aligned typing at `D`,
closed by a reducible environment, is reducible at the skeletons of `D`. -/
theorem norm_tm : ∀ {G : List FTy} {m : Tm} {D : FDist} {ρ : List Val},
    NTm G m D → NormEnv G ρ → NormT (skelFD D) (m.close ρ)
  | _, _, _, ρ, .val hv, hρ =>
      normT_val (hasTy_closeEnv_val hρ (nval_hasTy hv)) (norm_val hv hρ)
  | _, _, _, ρ, .errD hg, hρ =>
      normT_errD
  | _, _, _, ρ, .add hv hw, hρ =>
      normT_add (.add (hasTy_closeEnv_val hρ (nval_hasTy hv))
        (hasTy_closeEnv_val hρ (nval_hasTy hw)))
  | _, _, _, ρ, .choice h0 h1 hm hn, hρ =>
      normT_choice h0 h1 (norm_tm hm hρ) (norm_tm hn hρ)
  | _, _, _, ρ, .choiceU hm hn, hρ =>
      normT_choiceU (norm_tm hm hρ) (norm_tm hn hρ)
  | _, _, _, ρ, .ascV hv hev hg1 hg2 halign, hρ =>
      normT_ascV
        (.ascV (hasTy_closeEnv_val hρ (nval_hasTy hv)) hev hg1 hg2)
        halign (norm_val hv hρ)
  | _, _, _, ρ, .ascT hm hval hg1 hg2 halign, hρ =>
      normT_ascT
        (.ascT (hasTy_closeEnv_tm hρ (ntm_hasTy hm)) hval hg1 hg2)
        (hasTy_closeEnv_tm hρ (ntm_hasTy hm)) (norm_tm hm hρ) halign
  | _, _, _, ρ, .app hv hw halign, hρ =>
      normT_app (hasTy_closeEnv_val hρ (nval_hasTy hv))
        (hasTy_closeEnv_val hρ (nval_hasTy hw))
        (norm_val hv hρ) (norm_val hw hρ) halign
  | _, _, _, ρ, @NTm.ite _ v0 m0 n0 D1 D2 hv hm hn, hρ => by
      rw [Tm.close, Tm.closeAt_ite]
      have hvc := hasTy_closeEnv_val hρ (nval_hasTy hv)
      simp only [Val.close] at hvc
      rcases closed_bool_val_shape hvc with ⟨b, hshape⟩ | ⟨σe, hshape⟩
      · rw [hshape]
        cases b with
        | true => exact normT_ite_true (norm_tm hm hρ)
        | false => exact normT_ite_false (norm_tm hn hρ)
      · rw [hshape]
        refine ⟨1, DConf.errAt (chooseSemU D1 D2),
          Red.eIte (hasTy_closeEnv_tm hρ (ntm_hasTy hm))
            (hasTy_closeEnv_tm hρ (ntm_hasTy hn)), fun c => ?_⟩
        refine ⟨Fin.cast (skelFD_length _).symm c, ?_, normV_err⟩
        rw [skelFD_get (chooseSemU D1 D2) c]
        exact SkelEq.refl _
  | G, _, _, ρ, @NTm.letin _ m0 n ty C ns F hm hF, hρ => by
      simp only [Tm.close]
      rw [Tm.closeAt_letin]
      refine normT_letin (μ := ⟨n, ty, C⟩) (F := F)
        (hasTy_closeEnv_tm hρ (ntm_hasTy hm))
        (wf_tm (hasTy_closeEnv_tm hρ (ntm_hasTy hm)) ctxGood_nil)
        (fun i => hasTy_closeEnvAt_tm (Δ := [ty i]) hρ (ntm_hasTy (hF i)))
        (norm_tm hm hρ)
        (fun i w hw hnw => by
          cases hwc : w with
          | err σe =>
              rw [show ((ns i).closeAt (0 + 1) ρ).subErr (Val.err σe) (F i)
                  = Tm.errD (F i) from rfl]
              exact normT_errD
          | var x =>
              exfalso
              rw [hwc] at hw
              cases hw with | var hx => simp at hx
          | asc εw uw σw =>
              rw [show ((ns i).closeAt (0 + 1) ρ).subErr (Val.asc εw uw σw) (F i)
                  = ((ns i).closeAt (0 + 1) ρ).subst0 (.asc εw uw σw) from rfl]
              have hb := norm_tm (ρ := (Val.asc εw uw σw) :: ρ) (hF i)
                (normEnv_cons (by rw [← hwc]; exact hw) (by rw [← hwc]; exact hnw) hρ)
              rw [Tm.close, Tm.closeAt_cons
                  (by rw [← hwc]; exact hasTy_closed_val hw),
                ← Tm.closeAt_subst_comm (ρ := ρ) (k := 0)
                  (normEnv_closed hρ) (by rw [← hwc]; exact hasTy_closed_val hw)] at hb
              exact hb)
  termination_by structural G m D ρ hd hρ => hd
end

/-- Normalization of the aligned closed fragment of TPLC (beyond the article):
every closed term with an aligned typing converges. -/
theorem norm_closed {m : Tm} {D : FDist} (h : NTm [] m D) : Converges m := by
  have := norm_tm (ρ := []) h normEnv_nil
  rw [Tm.close, Tm.closeAt_nil] at this
  exact converges_of_normT this

end GradualProb.TPLC
