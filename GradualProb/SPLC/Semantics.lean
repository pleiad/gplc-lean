import GradualProb.SPLC.Typing

/-!
# The dynamic semantics of SPLC

This module formalizes the big-step distribution semantics of SPLC
(Figure 3, Section 3.3): distribution values `DistVal`, their scaling, sum and
weighted sum, and the reduction relation `Red`.  It also provides the de Bruijn
machinery the metatheory needs: renaming, substitution, closing substitutions,
and their interaction.

## Reading guide

Renaming and substitution come first; then distribution values and `Red`;
then free-variable bounds and closing substitutions (`Tm.closeAt`, a
simultaneous substitution), used by the
logical relation of `SPLC/TypeSafety`; then the indexing lemmas of weighted sums
(`wsum_n`, `wsum_at`); then staticness is preserved by renaming, substitution
and closing, and by reduction (`red_static`, through `wsum_pair_at`); last,
`wsum_val_mem` and further lemmas on renaming and substitution.
-/

namespace GradualProb.SPLC

open scoped BigOperators
open GradualProb.CouplingLemma

/-! ## Renaming and substitution

De Bruijn renaming (shifting the free variables above a cutoff) and the
substitution of a value for an index, on values and terms. -/

mutual
/-- Shift the free variables `≥ c` of a value up by one. -/
def Val.rename : Val → ℕ → Val
  | .var x, c => .var (if x < c then x else x + 1)
  | .real r, _ => .real r
  | .bool b, _ => .bool b
  | .lam τ m, c => .lam τ (m.rename (c + 1))
/-- Shift the free variables `≥ c` of a term up by one. -/
def Tm.rename : Tm → ℕ → Tm
  | .val v, c => .val (v.rename c)
  | .app v w, c => .app (v.rename c) (w.rename c)
  | .letin m n, c => .letin (m.rename c) (n.rename (c + 1))
  | .choice p m n, c => .choice p (m.rename c) (n.rename c)
  | .ascT m T, c => .ascT (m.rename c) T
  | .ascV v τ, c => .ascV (v.rename c) τ
  | .ite v m n, c => .ite (v.rename c) (m.rename c) (n.rename c)
  | .add v w, c => .add (v.rename c) (w.rename c)
end

mutual
/-- Substitute the de Bruijn index `k` by the value `w` in a value (lifting
`w` under binders, decrementing higher indices). -/
def Val.subst : Val → ℕ → Val → Val
  | .var x, k, w => if x = k then w else if x > k then .var (x - 1) else .var x
  | .real r, _, _ => .real r
  | .bool b, _, _ => .bool b
  | .lam τ m, k, w => .lam τ (m.subst (k + 1) (w.rename 0))
/-- Substitute the de Bruijn index `k` by the value `w` in a term. -/
def Tm.subst : Tm → ℕ → Val → Tm
  | .val v, k, w => .val (v.subst k w)
  | .app v u, k, w => .app (v.subst k w) (u.subst k w)
  | .letin m n, k, w => .letin (m.subst k w) (n.subst (k + 1) (w.rename 0))
  | .choice p m n, k, w => .choice p (m.subst k w) (n.subst k w)
  | .ascT m T, k, w => .ascT (m.subst k w) T
  | .ascV v τ, k, w => .ascV (v.subst k w) τ
  | .ite v m n, k, w => .ite (v.subst k w) (m.subst k w) (n.subst k w)
  | .add v u, k, w => .add (v.subst k w) (u.subst k w)
end

/-- Substitution `m[w/x]` of the innermost bound variable, as in the reduction
rules for application and `let`. -/
@[reducible] def Tm.subst0 (m : Tm) (w : Val) : Tm := m.subst 0 w

/-! ## Distribution values

Distribution values of SPLC and the operations the reduction rules use on them:
the Dirac distribution, scaling, sum and weighted sum. -/

/-- A distribution value `{{v_i^{p_i}}}_{i ∈ I}` of SPLC (Figure 3): finitely
many values with their probabilities.  The index set `I` is `Fin n`, and the
multiset is a pair of functions on it. -/
structure DistVal where
  n : ℕ
  val : Fin n → Val
  mass : Fin n → ℝ

/-- The Dirac distribution `{{v^1}}` on a single value. -/
def DistVal.point (v : Val) : DistVal := ⟨1, fun _ => v, fun _ => 1⟩
/-- Scale all probabilities by `a`. -/
def DistVal.scale (a : ℝ) (V : DistVal) : DistVal := ⟨V.n, V.val, fun i => a * V.mass i⟩
/-- Sum of two distribution values: the union of the two multisets. -/
def DistVal.append (V1 V2 : DistVal) : DistVal :=
  ⟨V1.n + V2.n, Fin.append V1.val V2.val, Fin.append V1.mass V2.mass⟩
/-- Weighted sum of a list of `(weight, distribution-value)` pairs. -/
def DistVal.wsumList : List (ℝ × DistVal) → DistVal
  | [] => ⟨0, Fin.elim0, Fin.elim0⟩
  | (a, V) :: rest => (V.scale a).append (DistVal.wsumList rest)
/-- Weighted sum of a finite family of pairs `(ωₖ, Vₖ)` (`∑ₖ ωₖ · Vₖ`). -/
def DistVal.wsum {K : ℕ} (cells : Fin K → ℝ × DistVal) : DistVal :=
  DistVal.wsumList (List.ofFn cells)

/-! ## The reduction relation

The big-step reduction of SPLC and the monotonicity of its derivation index. -/

/-- The big-step reduction `m ⇓ₛ V` of SPLC (Figure 3).  `Red m k V` adds a
natural-number index `k`, which bounds the height of the derivation and serves
for induction; results quantify over it unconstrained, and `red_index_mono` shows
any larger index works too. -/
inductive Red : Tm → ℕ → DistVal → Prop where
  /-- A value reduces to its Dirac distribution. -/
  | sv : ∀ {v k}, Red (.val v) (k + 1) (DistVal.point v)
  /-- β: the argument is substituted in the body. -/
  | sapp : ∀ {τ m v k V}, Red (m.subst0 v) k V →
      Red (.app (.lam τ m) v) (k + 1) V
  /-- Probabilistic choice: scaled concatenation of the branch outcomes. -/
  | schoice : ∀ {p m n k1 k2 V1 V2}, Red m k1 V1 → Red n k2 V2 →
      Red (.choice p m n) (k1 + k2 + 1)
        ((V1.scale p).append (V2.scale (1 - p)))
  /-- `let`: reduce the bound term to `V`, reduce the body with every outcome of
  `V` substituted (zero-probability ones included, as the article's `∀ i ∈ I`),
  and take the weighted sum.  `cells` is a bijection `Fin K → Fin V.n`
  enumerating the outcomes of `V`. -/
  | slet : ∀ {m n k1 k2} {V : DistVal} {K : ℕ} {cells : Fin K → Fin V.n}
      {W : Fin K → DistVal},
      Red m k1 V →
      Function.Injective cells →
      (∀ i, ∃ j, cells j = i) →
      (∀ j, Red (n.subst0 (V.val (cells j))) k2 (W j)) →
      Red (.letin m n) (k1 + k2 + 1)
        (DistVal.wsum (fun j => (V.mass (cells j), W j)))
  /-- A value ascription is dropped. -/
  | sascV : ∀ {v τ k}, Red (.ascV v τ) (k + 1) (DistVal.point v)
  /-- A term ascription is dropped. -/
  | sascT : ∀ {m T k V}, Red m k V → Red (.ascT m T) (k + 1) V
  /-- Addition of real literals. -/
  | sadd : ∀ {r1 r2 k}, Red (.add (.real r1) (.real r2)) (k + 1)
      (DistVal.point (.real (r1 + r2)))
  /-- Conditional, true branch. -/
  | sit : ∀ {m n k V}, Red m k V → Red (.ite (.bool true) m n) (k + 1) V
  /-- Conditional, false branch. -/
  | sif : ∀ {m n k V}, Red n k V → Red (.ite (.bool false) m n) (k + 1) V

/-- `m ⇓ₛ[k] V`, the reduction `m ⇓ₛ V` of Figure 3 with its derivation index
`k`. -/
scoped notation:50 (name := redStx) m:51 " ⇓ₛ[" k "] " V:51 => Red m k V

/-- The index of `Red` can be increased by one. -/
theorem red_index_succ : ∀ {m k V}, Red m k V → Red m (k + 1) V
  | _, _, _, .sv => .sv
  | _, _, _, .sapp h => .sapp (red_index_succ h)
  | _, _, _, .schoice (p := p) h1 h2 => by
      have h := Red.schoice (p := p) (red_index_succ h1) h2
      simpa [Nat.add_right_comm] using h
  | _, _, _, .slet hm hinj hcompl hbody =>
      by
        have h := Red.slet (red_index_succ hm) hinj hcompl hbody
        simpa [Nat.add_right_comm] using h
  | _, _, _, .sascV => .sascV
  | _, _, _, .sascT h => .sascT (red_index_succ h)
  | _, _, _, .sadd => .sadd
  | _, _, _, .sit h => .sit (red_index_succ h)
  | _, _, _, .sif h => .sif (red_index_succ h)

/-- The index of `Red` can be increased to any larger index (used to give the
reductions of the `let` bodies a common index). -/
theorem red_index_mono {m : Tm} {k : ℕ} {V : DistVal} (h : Red m k V) :
    ∀ {k' : ℕ}, k ≤ k' → Red m k' V := by
  intro k' hle
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction d with
  | zero => exact h
  | succ d ih => exact red_index_succ ih

/-! ## Free-variable bounds

The predicate "every free variable is below `n`" and how renaming and the
substitution of closed values interact with it. -/

mutual
/-- The free variables of a value are `< n`. -/
def Val.FvBelow : Val → ℕ → Prop
  | .var x, n => x < n
  | .real _, _ => True
  | .bool _, _ => True
  | .lam _ m, n => Tm.FvBelow m (n + 1)
/-- The free variables of a term are `< n`. -/
def Tm.FvBelow : Tm → ℕ → Prop
  | .val v, n => v.FvBelow n
  | .app v w, n => v.FvBelow n ∧ w.FvBelow n
  | .letin m b, n => m.FvBelow n ∧ b.FvBelow (n + 1)
  | .choice _ m1 m2, n => m1.FvBelow n ∧ m2.FvBelow n
  | .ascT m _, n => m.FvBelow n
  | .ascV v _, n => v.FvBelow n
  | .ite v m1 m2, n => v.FvBelow n ∧ m1.FvBelow n ∧ m2.FvBelow n
  | .add v w, n => v.FvBelow n ∧ w.FvBelow n
end

mutual
/-- A bound on the free variables of a value can be raised. -/
theorem Val.fvBelow_mono : ∀ {v : Val} {n n' : ℕ}, v.FvBelow n → n ≤ n' →
    v.FvBelow n'
  | .var _, _, _, h, hle => lt_of_lt_of_le h hle
  | .real _, _, _, _, _ => trivial
  | .bool _, _, _, _, _ => trivial
  | .lam _ m, _, _, h, hle => Tm.fvBelow_mono (m := m) h (by omega)
  termination_by v _ _ _ _ => sizeOf v
/-- A bound on the free variables of a term can be raised. -/
theorem Tm.fvBelow_mono : ∀ {m : Tm} {n n' : ℕ}, m.FvBelow n → n ≤ n' →
    m.FvBelow n'
  | .val v, _, _, h, hle => Val.fvBelow_mono (v := v) h hle
  | .app v w, _, _, h, hle =>
      ⟨Val.fvBelow_mono (v := v) h.1 hle, Val.fvBelow_mono (v := w) h.2 hle⟩
  | .letin m b, _, _, h, hle =>
      ⟨Tm.fvBelow_mono (m := m) h.1 hle,
        Tm.fvBelow_mono (m := b) h.2 (by omega)⟩
  | .choice _ m1 m2, _, _, h, hle =>
      ⟨Tm.fvBelow_mono (m := m1) h.1 hle, Tm.fvBelow_mono (m := m2) h.2 hle⟩
  | .ascT m _, _, _, h, hle => Tm.fvBelow_mono (m := m) h hle
  | .ascV v _, _, _, h, hle => Val.fvBelow_mono (v := v) h hle
  | .ite v m1 m2, _, _, h, hle =>
      ⟨Val.fvBelow_mono (v := v) h.1 hle,
        Tm.fvBelow_mono (m := m1) h.2.1 hle,
        Tm.fvBelow_mono (m := m2) h.2.2 hle⟩
  | .add v w, _, _, h, hle =>
      ⟨Val.fvBelow_mono (v := v) h.1 hle, Val.fvBelow_mono (v := w) h.2 hle⟩
  termination_by m _ _ _ _ => sizeOf m
end

mutual
/-- Renaming at a cutoff `c` above every free variable leaves a value unchanged. -/
theorem Val.rename_below : ∀ {v : Val} {n c : ℕ}, v.FvBelow n → n ≤ c →
    v.rename c = v
  | .var x, n, c, h, hle => by
      have hx : x < n := h
      simp only [Val.rename, if_pos (lt_of_lt_of_le hx hle)]
  | .real _, _, _, _, _ => rfl
  | .bool _, _, _, _, _ => rfl
  | .lam τ m, n, c, h, hle => by
      simp only [Val.rename]
      rw [Tm.rename_below h (by omega)]
/-- Renaming at a cutoff `c` above every free variable leaves a term unchanged. -/
theorem Tm.rename_below : ∀ {m : Tm} {n c : ℕ}, m.FvBelow n → n ≤ c →
    m.rename c = m
  | .val v, _, _, h, hle => by
      simp only [Tm.rename]; rw [Val.rename_below (v := v) h hle]
  | .app v w, _, _, h, hle => by
      simp only [Tm.rename]
      rw [Val.rename_below h.1 hle, Val.rename_below h.2 hle]
  | .letin m b, _, _, h, hle => by
      simp only [Tm.rename]
      rw [Tm.rename_below h.1 hle, Tm.rename_below h.2 (by omega)]
  | .choice p m1 m2, _, _, h, hle => by
      simp only [Tm.rename]
      rw [Tm.rename_below h.1 hle, Tm.rename_below h.2 hle]
  | .ascT m T, _, _, h, hle => by
      simp only [Tm.rename]; rw [Tm.rename_below (m := m) h hle]
  | .ascV v τ, _, _, h, hle => by
      simp only [Tm.rename]; rw [Val.rename_below (v := v) h hle]
  | .ite v m1 m2, _, _, h, hle => by
      simp only [Tm.rename]
      rw [Val.rename_below h.1 hle, Tm.rename_below h.2.1 hle,
        Tm.rename_below h.2.2 hle]
  | .add v w, _, _, h, hle => by
      simp only [Tm.rename]
      rw [Val.rename_below h.1 hle, Val.rename_below h.2 hle]
end

mutual
/-- Substituting at an index `k` above every free variable leaves a value
unchanged. -/
theorem Val.subst_below : ∀ {v : Val} {n k : ℕ} {w : Val}, v.FvBelow n →
    n ≤ k → v.subst k w = v
  | .var x, n, k, w, h, hle => by
      have hx : x < n := h
      simp only [Val.subst, if_neg (by omega : ¬ x = k),
        if_neg (by omega : ¬ x > k)]
  | .real _, _, _, _, _, _ => rfl
  | .bool _, _, _, _, _, _ => rfl
  | .lam τ m, _, _, _, h, hle => by
      simp only [Val.subst]
      rw [Tm.subst_below h (by omega)]
/-- Substituting at an index `k` above every free variable leaves a term
unchanged. -/
theorem Tm.subst_below : ∀ {m : Tm} {n k : ℕ} {w : Val}, m.FvBelow n →
    n ≤ k → m.subst k w = m
  | .val v, _, _, _, h, hle => by
      simp only [Tm.subst]; rw [Val.subst_below (v := v) h hle]
  | .app v w', _, _, _, h, hle => by
      simp only [Tm.subst]
      rw [Val.subst_below h.1 hle, Val.subst_below h.2 hle]
  | .letin m b, _, _, _, h, hle => by
      simp only [Tm.subst]
      rw [Tm.subst_below h.1 hle, Tm.subst_below h.2 (by omega)]
  | .choice p m1 m2, _, _, _, h, hle => by
      simp only [Tm.subst]
      rw [Tm.subst_below h.1 hle, Tm.subst_below h.2 hle]
  | .ascT m T, _, _, _, h, hle => by
      simp only [Tm.subst]; rw [Tm.subst_below (m := m) h hle]
  | .ascV v τ, _, _, _, h, hle => by
      simp only [Tm.subst]; rw [Val.subst_below (v := v) h hle]
  | .ite v m1 m2, _, _, _, h, hle => by
      simp only [Tm.subst]
      rw [Val.subst_below h.1 hle, Tm.subst_below h.2.1 hle,
        Tm.subst_below h.2.2 hle]
  | .add v w', _, _, _, h, hle => by
      simp only [Tm.subst]
      rw [Val.subst_below h.1 hle, Val.subst_below h.2 hle]
end

mutual
/-- Substituting a closed value at `k ≤ n` lowers the bound `n+1` to `n` (values). -/
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
  | .real _, _, _, _, _, _, _ => trivial
  | .bool _, _, _, _, _, _, _ => trivial
  | .lam τ m, n, k, w, h, hw, hk => by
      simp only [Val.subst]
      rw [Val.rename_below hw (Nat.zero_le 0)]
      exact Tm.subst_pres_below h hw (by omega)
  termination_by v _ _ _ _ _ _ => sizeOf v
/-- Substituting a closed value at `k ≤ n` lowers the bound `n+1` to `n` (terms). -/
theorem Tm.subst_pres_below : ∀ {m : Tm} {n k : ℕ} {w : Val},
    m.FvBelow (n + 1) → w.FvBelow 0 → k ≤ n → (m.subst k w).FvBelow n
  | .val v, _, _, _, h, hw, hk => Val.subst_pres_below (v := v) h hw hk
  | .app v w', _, _, _, h, hw, hk =>
      ⟨Val.subst_pres_below h.1 hw hk, Val.subst_pres_below h.2 hw hk⟩
  | .letin m b, n, k, w, h, hw, hk => by
      refine ⟨Tm.subst_pres_below h.1 hw hk, ?_⟩
      rw [Val.rename_below hw (Nat.zero_le 0)]
      exact Tm.subst_pres_below h.2 hw (by omega)
  | .choice p m1 m2, _, _, _, h, hw, hk =>
      ⟨Tm.subst_pres_below h.1 hw hk, Tm.subst_pres_below h.2 hw hk⟩
  | .ascT m T, _, _, _, h, hw, hk => Tm.subst_pres_below (m := m) h hw hk
  | .ascV v τ, _, _, _, h, hw, hk => Val.subst_pres_below (v := v) h hw hk
  | .ite v m1 m2, _, _, _, h, hw, hk =>
      ⟨Val.subst_pres_below h.1 hw hk, Tm.subst_pres_below h.2.1 hw hk,
        Tm.subst_pres_below h.2.2 hw hk⟩
  | .add v w', _, _, _, h, hw, hk =>
      ⟨Val.subst_pres_below h.1 hw hk, Val.subst_pres_below h.2 hw hk⟩
  termination_by m _ _ _ _ _ _ => sizeOf m
end

mutual
/-- Substitutions of closed values at adjacent indices commute (values). -/
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
  | .real _, _, _, _, _, _ => rfl
  | .bool _, _, _, _, _, _ => rfl
  | .lam τ m, k, v, w, hv, hw => by
      simp only [Val.subst]
      rw [Val.rename_below hv (Nat.zero_le 0),
        Val.rename_below hw (Nat.zero_le 0), Tm.subst_comm hv hw]
/-- Substitutions of closed values at adjacent indices commute (terms). -/
theorem Tm.subst_comm : ∀ {m : Tm} {k : ℕ} {v w : Val}, v.FvBelow 0 →
    w.FvBelow 0 → (m.subst (k + 1) v).subst k w = (m.subst k w).subst k v
  | .val u, _, _, _, hv, hw => by
      simp only [Tm.subst]; rw [Val.subst_comm hv hw]
  | .app u1 u2, _, _, _, hv, hw => by
      simp only [Tm.subst]
      rw [Val.subst_comm hv hw, Val.subst_comm (u := u2) hv hw]
  | .letin m b, k, v, w, hv, hw => by
      simp only [Tm.subst]
      rw [Val.rename_below hv (Nat.zero_le 0),
        Val.rename_below hw (Nat.zero_le 0), Tm.subst_comm hv hw,
        Tm.subst_comm (m := b) hv hw]
  | .choice p m1 m2, _, _, _, hv, hw => by
      simp only [Tm.subst]
      rw [Tm.subst_comm (m := m1) hv hw, Tm.subst_comm (m := m2) hv hw]
  | .ascT m T, _, _, _, hv, hw => by
      simp only [Tm.subst]; rw [Tm.subst_comm hv hw]
  | .ascV u τ, _, _, _, hv, hw => by
      simp only [Tm.subst]; rw [Val.subst_comm hv hw]
  | .ite u m1 m2, _, _, _, hv, hw => by
      simp only [Tm.subst]
      rw [Val.subst_comm hv hw, Tm.subst_comm (m := m1) hv hw,
        Tm.subst_comm (m := m2) hv hw]
  | .add u1 u2, _, _, _, hv, hw => by
      simp only [Tm.subst]
      rw [Val.subst_comm hv hw, Val.subst_comm (u := u2) hv hw]
end

/-! ## Closing substitutions

`closeAt k ρ` substitutes the values of `ρ`, simultaneously, for the variables
`k, k + 1, …, k + ρ.length - 1`, lowers the variables above them by
`ρ.length`, and leaves the variables below `k` (bound by the binders crossed so
far) unchanged. The environments that close terms are closed, so the values
are not shifted under binders. Every case of the definition is an equation by
`rfl`; `closeAt_cons` relates the closing to substitution, one value at a
time. -/

mutual
/-- Close a value with the environment `ρ` at depth `k`. -/
def Val.closeAt : Val → ℕ → List Val → Val
  | .var x, k, ρ =>
      if x < k then .var x else (ρ[x - k]?).getD (.var (x - ρ.length))
  | .real r, _, _ => .real r
  | .bool b, _, _ => .bool b
  | .lam τ m, k, ρ => .lam τ (m.closeAt (k + 1) ρ)
/-- Close a term with the environment `ρ` at depth `k`. -/
def Tm.closeAt : Tm → ℕ → List Val → Tm
  | .val v, k, ρ => .val (v.closeAt k ρ)
  | .app v w, k, ρ => .app (v.closeAt k ρ) (w.closeAt k ρ)
  | .letin m n, k, ρ => .letin (m.closeAt k ρ) (n.closeAt (k + 1) ρ)
  | .choice p m n, k, ρ => .choice p (m.closeAt k ρ) (n.closeAt k ρ)
  | .ascT m T, k, ρ => .ascT (m.closeAt k ρ) T
  | .ascV v τ, k, ρ => .ascV (v.closeAt k ρ) τ
  | .ite v m n, k, ρ => .ite (v.closeAt k ρ) (m.closeAt k ρ) (n.closeAt k ρ)
  | .add v w, k, ρ => .add (v.closeAt k ρ) (w.closeAt k ρ)
end

/-- Close a value with the environment `ρ`. -/
@[reducible] def Val.close (u : Val) (ρ : List Val) : Val := u.closeAt 0 ρ

/-- Close a term with the environment `ρ`. -/
@[reducible] def Tm.close (m : Tm) (ρ : List Val) : Tm := m.closeAt 0 ρ

mutual
/-- Closing at an index above every free variable leaves a value unchanged. -/
theorem Val.closeAt_below : ∀ {ρ : List Val} {u : Val} {n k : ℕ},
    u.FvBelow n → n ≤ k → u.closeAt k ρ = u
  | _, .var x, n, k, h, hle => by
      have hx : x < n := h
      simp only [Val.closeAt, if_pos (lt_of_lt_of_le hx hle)]
  | _, .real _, _, _, _, _ => rfl
  | _, .bool _, _, _, _, _ => rfl
  | _, .lam τ m, _, _, h, hle => by
      simp only [Val.closeAt]; rw [Tm.closeAt_below (m := m) h (by omega)]
/-- Closing at an index above every free variable leaves a term unchanged. -/
theorem Tm.closeAt_below : ∀ {ρ : List Val} {m : Tm} {n k : ℕ},
    m.FvBelow n → n ≤ k → m.closeAt k ρ = m
  | _, .val v, _, _, h, hle => by
      simp only [Tm.closeAt]; rw [Val.closeAt_below (u := v) h hle]
  | _, .app v w, _, _, h, hle => by
      simp only [Tm.closeAt]
      rw [Val.closeAt_below (u := v) h.1 hle, Val.closeAt_below (u := w) h.2 hle]
  | _, .letin m b, _, _, h, hle => by
      simp only [Tm.closeAt]
      rw [Tm.closeAt_below (m := m) h.1 hle, Tm.closeAt_below (m := b) h.2 (by omega)]
  | _, .choice p m1 m2, _, _, h, hle => by
      simp only [Tm.closeAt]
      rw [Tm.closeAt_below (m := m1) h.1 hle, Tm.closeAt_below (m := m2) h.2 hle]
  | _, .ascT m T, _, _, h, hle => by
      simp only [Tm.closeAt]; rw [Tm.closeAt_below (m := m) h hle]
  | _, .ascV v τ, _, _, h, hle => by
      simp only [Tm.closeAt]; rw [Val.closeAt_below (u := v) h hle]
  | _, .ite v m1 m2, _, _, h, hle => by
      simp only [Tm.closeAt]
      rw [Val.closeAt_below (u := v) h.1 hle, Tm.closeAt_below (m := m1) h.2.1 hle,
        Tm.closeAt_below (m := m2) h.2.2 hle]
  | _, .add v w, _, _, h, hle => by
      simp only [Tm.closeAt]
      rw [Val.closeAt_below (u := v) h.1 hle, Val.closeAt_below (u := w) h.2 hle]
end

/-- The congruence equations of closing used by the fundamental lemma hold by
`rfl`. -/
theorem Tm.closeAt_ite {ρ : List Val} {u : Val} {m1 m2 : Tm} {k : ℕ} :
    (Tm.ite u m1 m2).closeAt k ρ
      = .ite (u.closeAt k ρ) (m1.closeAt k ρ) (m2.closeAt k ρ) := rfl

/-- Closing commutes with addition. -/
theorem Tm.closeAt_add {ρ : List Val} {u w : Val} {k : ℕ} :
    (Tm.add u w).closeAt k ρ = .add (u.closeAt k ρ) (w.closeAt k ρ) := rfl

/-- Closing a `lam` closes the body one binder up. -/
theorem Val.closeAt_lam {ρ : List Val} {τ : Ty} {mb : Tm} {k : ℕ} :
    (Val.lam τ mb).closeAt k ρ = .lam τ (mb.closeAt (k + 1) ρ) := rfl

/-- Closing a `letin` closes the body one binder up. -/
theorem Tm.closeAt_letin {ρ : List Val} {m b : Tm} {k : ℕ} :
    (Tm.letin m b).closeAt k ρ
      = .letin (m.closeAt k ρ) (b.closeAt (k + 1) ρ) := rfl

/-- Variable lookup under closure. -/
theorem Val.closeAt_var {ρ : List Val} {x k : ℕ} (hx : x < ρ.length) :
    (Val.var (k + x)).closeAt k ρ = ρ[x] := by
  simp [Val.closeAt, hx]

mutual
/-- Closing with `v :: ρ` substitutes `v` first, then closes with `ρ`
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
  | .real _, _, _, _, _ => rfl
  | .bool _, _, _, _, _ => rfl
  | .lam τ m, k, v, ρ, hv => by
      simp only [Val.closeAt, Val.subst]
      rw [Val.rename_below hv (Nat.zero_le 0), Tm.closeAt_cons (m := m) hv]
/-- Closing a term with `v :: ρ` substitutes `v` first, then closes with `ρ`
(closed `v`). -/
theorem Tm.closeAt_cons : ∀ {m : Tm} {k : ℕ} {v : Val} {ρ : List Val},
    v.FvBelow 0 → m.closeAt k (v :: ρ) = (m.subst k v).closeAt k ρ
  | .val u, _, _, _, hv => by
      simp only [Tm.closeAt, Tm.subst]; rw [Val.closeAt_cons (u := u) hv]
  | .app u w, _, _, _, hv => by
      simp only [Tm.closeAt, Tm.subst]
      rw [Val.closeAt_cons (u := u) hv, Val.closeAt_cons (u := w) hv]
  | .letin m b, _, _, _, hv => by
      simp only [Tm.closeAt, Tm.subst]
      rw [Val.rename_below hv (Nat.zero_le 0), Tm.closeAt_cons (m := m) hv,
        Tm.closeAt_cons (m := b) hv]
  | .choice p m1 m2, _, _, _, hv => by
      simp only [Tm.closeAt, Tm.subst]
      rw [Tm.closeAt_cons (m := m1) hv, Tm.closeAt_cons (m := m2) hv]
  | .ascT m T, _, _, _, hv => by
      simp only [Tm.closeAt, Tm.subst]; rw [Tm.closeAt_cons (m := m) hv]
  | .ascV u τ, _, _, _, hv => by
      simp only [Tm.closeAt, Tm.subst]; rw [Val.closeAt_cons (u := u) hv]
  | .ite u m1 m2, _, _, _, hv => by
      simp only [Tm.closeAt, Tm.subst]
      rw [Val.closeAt_cons (u := u) hv, Tm.closeAt_cons (m := m1) hv,
        Tm.closeAt_cons (m := m2) hv]
  | .add u w, _, _, _, hv => by
      simp only [Tm.closeAt, Tm.subst]
      rw [Val.closeAt_cons (u := u) hv, Val.closeAt_cons (u := w) hv]
end

mutual
/-- Closing with the empty environment is the identity. -/
theorem Val.closeAt_nil : ∀ {u : Val} {k : ℕ}, u.closeAt k [] = u
  | .var x, k => by by_cases hx : x < k <;> simp [Val.closeAt, hx]
  | .real _, _ => rfl
  | .bool _, _ => rfl
  | .lam τ m, _ => by simp only [Val.closeAt]; rw [Tm.closeAt_nil (m := m)]
/-- Closing a term with the empty environment is the identity. -/
theorem Tm.closeAt_nil : ∀ {m : Tm} {k : ℕ}, m.closeAt k [] = m
  | .val u, _ => by simp only [Tm.closeAt]; rw [Val.closeAt_nil (u := u)]
  | .app u w, _ => by
      simp only [Tm.closeAt]; rw [Val.closeAt_nil (u := u), Val.closeAt_nil (u := w)]
  | .letin m b, _ => by
      simp only [Tm.closeAt]; rw [Tm.closeAt_nil (m := m), Tm.closeAt_nil (m := b)]
  | .choice p m1 m2, _ => by
      simp only [Tm.closeAt]; rw [Tm.closeAt_nil (m := m1), Tm.closeAt_nil (m := m2)]
  | .ascT m T, _ => by simp only [Tm.closeAt]; rw [Tm.closeAt_nil (m := m)]
  | .ascV u τ, _ => by simp only [Tm.closeAt]; rw [Val.closeAt_nil (u := u)]
  | .ite u m1 m2, _ => by
      simp only [Tm.closeAt]
      rw [Val.closeAt_nil (u := u), Tm.closeAt_nil (m := m1), Tm.closeAt_nil (m := m2)]
  | .add u w, _ => by
      simp only [Tm.closeAt]; rw [Val.closeAt_nil (u := u), Val.closeAt_nil (u := w)]
end

/-- A closing substitution (of closed values) commutes with a substitution at a
lower index: `(m.closeAt (k+1) ρ).subst k w = (m.subst k w).closeAt k ρ`. -/
theorem Tm.closeAt_subst_comm : ∀ {ρ : List Val} {m : Tm} {k : ℕ} {w : Val},
    (∀ v ∈ ρ, v.FvBelow 0) → w.FvBelow 0 →
    (m.closeAt (k + 1) ρ).subst k w = (m.subst k w).closeAt k ρ
  | [], _, _, _, _, _ => by rw [Tm.closeAt_nil, Tm.closeAt_nil]
  | v :: ρ, m, k, w, hρ, hw => by
      have hv : v.FvBelow 0 := hρ v (by simp)
      rw [Tm.closeAt_cons hv, Tm.closeAt_cons hv,
        Tm.closeAt_subst_comm (ρ := ρ) (fun u hu => hρ u (by simp [hu])) hw,
        Tm.subst_comm hv hw]

/-! ## Indexing weighted sums

The number of outcomes of a weighted sum and the value and probability found at
each of its positions. -/

/-- Unfolding a weighted sum of `K+1` summands: the first summand, scaled,
followed by the weighted sum of the others. -/
theorem wsum_succ {K : ℕ} (cells : Fin (K + 1) → ℝ × DistVal) :
    DistVal.wsum cells
      = ((cells 0).2.scale (cells 0).1).append
          (DistVal.wsum (fun k => cells k.succ)) := by
  rw [DistVal.wsum, List.ofFn_succ]
  rfl

/-- Number of outcomes of a weighted sum. -/
theorem wsum_n : ∀ {K : ℕ} (cells : Fin K → ℝ × DistVal),
    (DistVal.wsum cells).n = ∑ k, (cells k).2.n
  | 0, cells => by simp [DistVal.wsum, List.ofFn_zero, DistVal.wsumList]
  | (K + 1), cells => by
      rw [wsum_succ]
      show (cells 0).2.n + (DistVal.wsum (fun k => cells k.succ)).n = _
      rw [wsum_n (fun k => cells k.succ), Fin.sum_univ_succ]

/-- Equal distribution values have the same value and probability at the same
position. -/
theorem distVal_at_congr {D1 D2 : DistVal} (hD : D1 = D2) (v : ℕ)
    (h1 : v < D1.n) (h2 : v < D2.n) :
    (D1.val ⟨v, h1⟩, D1.mass ⟨v, h1⟩) = (D2.val ⟨v, h2⟩, D2.mass ⟨v, h2⟩) := by
  subst hD; rfl

/-- Value and probability of a weighted sum at offset positions. -/
theorem wsum_at : ∀ {K : ℕ} (cells : Fin K → ℝ × DistVal)
    (k : Fin K) (j : Fin (cells k).2.n) {v : ℕ},
    v = (∑ i : Fin (k : ℕ), (cells (Fin.castLE k.isLt.le i)).2.n) + (j : ℕ) →
    ∀ h : v < (DistVal.wsum cells).n,
    ((DistVal.wsum cells).val ⟨v, h⟩, (DistVal.wsum cells).mass ⟨v, h⟩)
      = ((cells k).2.val j, (cells k).1 * (cells k).2.mass j)
  | 0, _, k, _, _, _, _ => absurd k.isLt (by simp)
  | (K + 1), cells, k, j, v, hv, h => by
      have hEq := wsum_succ cells
      have h2 : v < (((cells 0).2.scale (cells 0).1).append
          (DistVal.wsum (fun i => cells i.succ))).n := by
        rw [← hEq]; exact h
      rw [distVal_at_congr hEq v h h2]
      revert hv
      revert j
      induction k using Fin.cases with
      | zero =>
          intro j hv
          have hv0 : v = (j : ℕ) := by simpa using hv
          have hjlt : v < ((cells 0).2.scale (cells 0).1).n := by
            rw [hv0]; exact j.isLt
          show (Fin.append ((cells 0).2.scale (cells 0).1).val
              (DistVal.wsum (fun i => cells i.succ)).val (Fin.castAdd _ ⟨v, hjlt⟩),
            Fin.append ((cells 0).2.scale (cells 0).1).mass
              (DistVal.wsum (fun i => cells i.succ)).mass
                (Fin.castAdd _ ⟨v, hjlt⟩)) = _
          rw [Fin.append_left, Fin.append_left]
          have hj : (⟨v, hjlt⟩ : Fin ((cells 0).2.scale (cells 0).1).n) = j :=
            Fin.ext hv0
          rw [hj]
          rfl
      | succ kp =>
          intro j hv
          have hsum : (∑ i : Fin ((kp.succ : Fin (K + 1)) : ℕ),
              (cells (Fin.castLE (kp.succ : Fin (K + 1)).isLt.le i)).2.n)
              = (cells 0).2.n
                + ∑ i : Fin (kp : ℕ),
                    ((fun t => cells t.succ) (Fin.castLE kp.isLt.le i)).2.n := by
            show (∑ i : Fin ((kp : ℕ) + 1), _) = _
            rw [Fin.sum_univ_succ]
            have h0 : (Fin.castLE (kp.succ : Fin (K + 1)).isLt.le
                (0 : Fin ((kp : ℕ) + 1))) = (0 : Fin (K + 1)) :=
              Fin.ext (by simp)
            rw [h0]
            congr 1
          have hge : (cells 0).2.n ≤ v := by
            rw [hv, hsum]; omega
          have h2n : v < (cells 0).2.n
              + (DistVal.wsum (fun i => cells i.succ)).n := h2
          have hlt2 : v - (cells 0).2.n
              < (DistVal.wsum (fun i => cells i.succ)).n := by
            omega
          have hidx : (⟨v, h2⟩ : Fin ((((cells 0).2.scale (cells 0).1).append
              (DistVal.wsum (fun i => cells i.succ))).n))
              = Fin.natAdd ((cells 0).2.scale (cells 0).1).n
                  ⟨v - (cells 0).2.n, hlt2⟩ := by
            apply Fin.ext
            simp only [Fin.val_natAdd]
            show v = (cells 0).2.n + (v - (cells 0).2.n)
            omega
          rw [hidx]
          show (Fin.append ((cells 0).2.scale (cells 0).1).val
              (DistVal.wsum (fun i => cells i.succ)).val (Fin.natAdd _ _),
            Fin.append ((cells 0).2.scale (cells 0).1).mass
              (DistVal.wsum (fun i => cells i.succ)).mass (Fin.natAdd _ _)) = _
          rw [Fin.append_right, Fin.append_right]
          have hrest : v - (cells 0).2.n
              = (∑ i : Fin (kp : ℕ),
                  ((fun t => cells t.succ)
                    (Fin.castLE kp.isLt.le i)).2.n) + (j : ℕ) := by
            rw [hv, hsum]; omega
          exact wsum_at (fun t => cells t.succ) kp j hrest hlt2

/-! ## Staticness under renaming, substitution and reduction

Renaming, substituting and closing with static values preserve staticness, and
reducing a static term yields static values. -/

mutual
/-- Renaming preserves staticness of values. -/
theorem isStaticVal_rename : ∀ {v : Val} {c : ℕ}, IsStaticVal v → IsStaticVal (v.rename c)
  | .var x, c, _ => by
      simp only [Val.rename]
      split <;> exact .var
  | .real r, _, _ => by simp only [Val.rename]; exact .real
  | .bool b, _, _ => by simp only [Val.rename]; exact .bool
  | .lam τ m, c, h => by
      cases h with
      | lam hτ hm =>
        simp only [Val.rename]
        exact .lam hτ (isStaticTm_rename hm)
/-- Renaming preserves staticness of terms. -/
theorem isStaticTm_rename : ∀ {m : Tm} {c : ℕ}, IsStaticTm m → IsStaticTm (m.rename c)
  | .val v, _, h => by
      cases h with
      | val hv => simp only [Tm.rename]; exact .val (isStaticVal_rename hv)
  | .app v w, _, h => by
      cases h with
      | app hv hw =>
        simp only [Tm.rename]
        exact .app (isStaticVal_rename hv) (isStaticVal_rename hw)
  | .letin m n, _, h => by
      cases h with
      | letin hm hn =>
        simp only [Tm.rename]
        exact .letin (isStaticTm_rename hm) (isStaticTm_rename hn)
  | .choice p m n, _, h => by
      cases h with
      | choice hp0 hp1 hm hn =>
        simp only [Tm.rename]
        exact .choice hp0 hp1 (isStaticTm_rename hm) (isStaticTm_rename hn)
  | .ascT m T, _, h => by
      cases h with
      | ascT hm hT => simp only [Tm.rename]; exact .ascT (isStaticTm_rename hm) hT
  | .ascV v τ, _, h => by
      cases h with
      | ascV hv hτ => simp only [Tm.rename]; exact .ascV (isStaticVal_rename hv) hτ
  | .ite v m n, _, h => by
      cases h with
      | ite hv hm hn =>
        simp only [Tm.rename]
        exact .ite (isStaticVal_rename hv) (isStaticTm_rename hm) (isStaticTm_rename hn)
  | .add v w, _, h => by
      cases h with
      | add hv hw =>
        simp only [Tm.rename]
        exact .add (isStaticVal_rename hv) (isStaticVal_rename hw)
end

mutual
/-- Substituting a static value preserves staticness of values. -/
theorem isStaticVal_subst : ∀ {v : Val} {k : ℕ} {w : Val}, IsStaticVal v → IsStaticVal w →
    IsStaticVal (v.subst k w)
  | .var x, k, w, _, hw => by
      simp only [Val.subst]
      split
      · exact hw
      · split <;> exact .var
  | .real r, _, _, _, _ => by simp only [Val.subst]; exact .real
  | .bool b, _, _, _, _ => by simp only [Val.subst]; exact .bool
  | .lam τ m, k, w, h, hw => by
      cases h with
      | lam hτ hm =>
        simp only [Val.subst]
        exact .lam hτ (isStaticTm_subst hm (isStaticVal_rename hw))
/-- Substituting a static value preserves staticness of terms. -/
theorem isStaticTm_subst : ∀ {m : Tm} {k : ℕ} {w : Val}, IsStaticTm m → IsStaticVal w →
    IsStaticTm (m.subst k w)
  | .val v, _, _, h, hw => by
      cases h with
      | val hv => simp only [Tm.subst]; exact .val (isStaticVal_subst hv hw)
  | .app v u, _, _, h, hw => by
      cases h with
      | app hv hu =>
        simp only [Tm.subst]
        exact .app (isStaticVal_subst hv hw) (isStaticVal_subst hu hw)
  | .letin m n, _, _, h, hw => by
      cases h with
      | letin hm hn =>
        simp only [Tm.subst]
        exact .letin (isStaticTm_subst hm hw) (isStaticTm_subst hn (isStaticVal_rename hw))
  | .choice p m n, _, _, h, hw => by
      cases h with
      | choice hp0 hp1 hm hn =>
        simp only [Tm.subst]
        exact .choice hp0 hp1 (isStaticTm_subst hm hw) (isStaticTm_subst hn hw)
  | .ascT m T, _, _, h, hw => by
      cases h with
      | ascT hm hT => simp only [Tm.subst]; exact .ascT (isStaticTm_subst hm hw) hT
  | .ascV v τ, _, _, h, hw => by
      cases h with
      | ascV hv hτ => simp only [Tm.subst]; exact .ascV (isStaticVal_subst hv hw) hτ
  | .ite v m n, _, _, h, hw => by
      cases h with
      | ite hv hm hn =>
        simp only [Tm.subst]
        exact .ite (isStaticVal_subst hv hw) (isStaticTm_subst hm hw) (isStaticTm_subst hn hw)
  | .add v u, _, _, h, hw => by
      cases h with
      | add hv hu =>
        simp only [Tm.subst]
        exact .add (isStaticVal_subst hv hw) (isStaticVal_subst hu hw)
end

/-- Closing with closed static values preserves staticness of values. -/
theorem isStaticVal_closeAt : ∀ {ρ : List Val} {u : Val} {k : ℕ}, IsStaticVal u →
    (∀ v ∈ ρ, IsStaticVal v ∧ v.FvBelow 0) → IsStaticVal (u.closeAt k ρ)
  | [], _, _, hu, _ => by rwa [Val.closeAt_nil]
  | v :: ρ, u, k, hu, hρ => by
      rw [Val.closeAt_cons (hρ v (by simp)).2]
      exact isStaticVal_closeAt (isStaticVal_subst hu (hρ v (by simp)).1)
        (fun w hw => hρ w (by simp [hw]))

/-- Closing with closed static values preserves staticness of terms. -/
theorem isStaticTm_closeAt : ∀ {ρ : List Val} {m : Tm} {k : ℕ}, IsStaticTm m →
    (∀ v ∈ ρ, IsStaticVal v ∧ v.FvBelow 0) → IsStaticTm (m.closeAt k ρ)
  | [], _, _, hm, _ => by rwa [Tm.closeAt_nil]
  | v :: ρ, m, k, hm, hρ => by
      rw [Tm.closeAt_cons (hρ v (by simp)).2]
      exact isStaticTm_closeAt (isStaticTm_subst hm (hρ v (by simp)).1)
        (fun w hw => hρ w (by simp [hw]))

/-- Value and probability of a weighted sum at a position, through the
decomposition `finSigmaFinEquiv` of the position into summand and offset. -/
theorem wsum_pair_at {K : ℕ} (ω : Fin K → ℝ) (Vk : Fin K → DistVal)
    (hn : (DistVal.wsum (fun c => (ω c, Vk c))).n = ∑ c, (Vk c).n)
    (i : Fin (DistVal.wsum (fun c => (ω c, Vk c))).n) :
    ((DistVal.wsum (fun c => (ω c, Vk c))).val i,
      (DistVal.wsum (fun c => (ω c, Vk c))).mass i)
    = ((Vk (finSigmaFinEquiv.symm (Fin.cast hn i)).1).val
         (finSigmaFinEquiv.symm (Fin.cast hn i)).2,
       ω (finSigmaFinEquiv.symm (Fin.cast hn i)).1
         * (Vk (finSigmaFinEquiv.symm (Fin.cast hn i)).1).mass
           (finSigmaFinEquiv.symm (Fin.cast hn i)).2) := by
  set sk := (finSigmaFinEquiv.symm (Fin.cast hn i)).1 with hsk
  set si := (finSigmaFinEquiv.symm (Fin.cast hn i)).2 with hsi
  have hv : (i : ℕ) = (∑ r : Fin ((sk : ℕ)),
      ((fun c => (ω c, Vk c)) (Fin.castLE sk.isLt.le r)).2.n) + (si : ℕ) := by
    have heq : finSigmaFinEquiv (⟨sk, si⟩ : Σ c : Fin K, Fin ((Vk c).n))
        = Fin.cast hn i := Equiv.apply_symm_apply _ _
    have happ := finSigmaFinEquiv_apply
      (⟨sk, si⟩ : Σ c : Fin K, Fin ((Vk c).n))
    rw [heq] at happ
    exact happ
  exact wsum_at (fun c => (ω c, Vk c)) sk si hv i.isLt

/-- The value at any position of a weighted sum is a value of one of its
summands. -/
theorem wsum_val_decomp {K : ℕ} (ω : Fin K → ℝ) (Vk : Fin K → DistVal)
    (i : Fin (DistVal.wsum (fun k => (ω k, Vk k))).n) :
    ∃ (k : Fin K) (x : Fin (Vk k).n),
      (DistVal.wsum (fun k => (ω k, Vk k))).val i = (Vk k).val x :=
  ⟨_, _, congrArg Prod.fst (wsum_pair_at ω Vk (wsum_n _) i)⟩

/-- All values in the result of reducing a static term are static. -/
theorem red_static : ∀ {m : Tm} {k : ℕ} {V : DistVal}, Red m k V → IsStaticTm m →
    ∀ i, IsStaticVal (V.val i)
  | _, _, _, .sv, hs, i => by
      cases hs with
      | val hv => exact hv
  | _, _, _, .sapp h, hs, i => by
      cases hs with
      | app hsv hsw =>
        cases hsv with
        | lam hτ hm => exact red_static h (isStaticTm_subst hm hsw) i
  | _, _, _, .schoice h1 h2, hs, i => by
      cases hs with
      | choice hp0 hp1 hsm hsn =>
        induction i using Fin.addCases with
        | left i1 =>
            have := red_static h1 hsm i1
            simpa [DistVal.append, DistVal.scale, Fin.append_left] using this
        | right i2 =>
            have := red_static h2 hsn i2
            simpa [DistVal.append, DistVal.scale, Fin.append_right] using this
  | _, _, _, .slet hm hinj hcompl hbody, hs, i => by
      cases hs with
      | letin hsm hsn =>
        obtain ⟨k0, x, hval⟩ := wsum_val_decomp _ _ i
        rw [hval]
        exact red_static (hbody k0)
          (isStaticTm_subst hsn (red_static hm hsm _)) x
  | _, _, _, .sascV, hs, i => by
      cases hs with
      | ascV hv hτ => exact hv
  | _, _, _, .sascT h, hs, i => by
      cases hs with
      | ascT hm hT => exact red_static h hm i
  | _, _, _, .sadd, hs, i => .real
  | _, _, _, .sit h, hs, i => by
      cases hs with
      | ite hv hm hn => exact red_static h hm i
  | _, _, _, .sif h, hs, i => by
      cases hs with
      | ite hv hm hn => exact red_static h hn i

/-! ## Weighted sums, further lemmas

Every value of a summand is a value of the weighted sum. -/

/-- Every value of a summand appears in the weighted sum, whatever its weight
(the converse of `wsum_val_decomp`). -/
theorem wsum_val_mem {K : ℕ} (ω : Fin K → ℝ) (Vk : Fin K → DistVal)
    (a : Fin K) (x : Fin (Vk a).n) :
    ∃ i, (DistVal.wsum (fun k => (ω k, Vk k))).val i = (Vk a).val x := by
  have hn1 : (DistVal.wsum (fun k => (ω k, Vk k))).n = ∑ c, (Vk c).n := wsum_n _
  refine ⟨Fin.cast hn1.symm
    (finSigmaFinEquiv (⟨a, x⟩ : Σ c : Fin K, Fin (Vk c).n)), ?_⟩
  have hp : (finSigmaFinEquiv.symm (Fin.cast hn1
      (Fin.cast hn1.symm (finSigmaFinEquiv (⟨a, x⟩ : Σ c : Fin K, Fin (Vk c).n)))))
      = (⟨a, x⟩ : Σ c : Fin K, Fin (Vk c).n) := by
    rw [show Fin.cast hn1 (Fin.cast hn1.symm
      (finSigmaFinEquiv (⟨a, x⟩ : Σ c : Fin K, Fin (Vk c).n)))
      = finSigmaFinEquiv (⟨a, x⟩ : Σ c : Fin K, Fin (Vk c).n) from Fin.ext rfl]
    exact Equiv.symm_apply_apply _ _
  have h := congrArg Prod.fst (wsum_pair_at ω Vk hn1
    (Fin.cast hn1.symm (finSigmaFinEquiv (⟨a, x⟩ : Σ c : Fin K, Fin (Vk c).n))))
  rw [hp] at h
  exact h

/-! ## Renaming and substitution, further lemmas

Free-variable bounds after renaming, and the commutation of renaming with
substitution. -/

mutual
/-- Renaming a value whose free variables are `< n` gives free variables `< n+1`. -/
theorem Val.rename_fvBelow : ∀ (v : Val) (n c : ℕ), v.FvBelow n →
    (v.rename c).FvBelow (n + 1)
  | .var x, n, c, h => by
      by_cases hx : x < c
      · simp only [Val.rename, if_pos hx]; exact Nat.lt_succ_of_lt h
      · simp only [Val.rename, if_neg hx]; exact Nat.succ_lt_succ h
  | .real _, _, _, _ => trivial
  | .bool _, _, _, _ => trivial
  | .lam _ m, n, c, h => Tm.rename_fvBelow m (n + 1) (c + 1) h
/-- Renaming a term whose free variables are `< n` gives free variables `< n+1`. -/
theorem Tm.rename_fvBelow : ∀ (m : Tm) (n c : ℕ), m.FvBelow n →
    (m.rename c).FvBelow (n + 1)
  | .val v, n, c, h => Val.rename_fvBelow v n c h
  | .app v w, n, c, h =>
      ⟨Val.rename_fvBelow v n c h.1, Val.rename_fvBelow w n c h.2⟩
  | .letin m b, n, c, h =>
      ⟨Tm.rename_fvBelow m n c h.1, Tm.rename_fvBelow b (n + 1) (c + 1) h.2⟩
  | .choice _ m1 m2, n, c, h =>
      ⟨Tm.rename_fvBelow m1 n c h.1, Tm.rename_fvBelow m2 n c h.2⟩
  | .ascT m _, n, c, h => Tm.rename_fvBelow m n c h
  | .ascV v _, n, c, h => Val.rename_fvBelow v n c h
  | .ite v m1 m2, n, c, h =>
      ⟨Val.rename_fvBelow v n c h.1, Tm.rename_fvBelow m1 n c h.2.1,
       Tm.rename_fvBelow m2 n c h.2.2⟩
  | .add v w, n, c, h =>
      ⟨Val.rename_fvBelow v n c h.1, Val.rename_fvBelow w n c h.2⟩
end

mutual
/-- Substituting at the cutoff `c` undoes renaming at `c` (values). -/
theorem Val.subst_rename_cancel : ∀ (v : Val) (c : ℕ) (w : Val),
    (v.rename c).subst c w = v
  | .var x, c, w => by
      by_cases hx : x < c
      · simp only [Val.rename, if_pos hx, Val.subst,
          if_neg (by omega : ¬ x = c), if_neg (by omega : ¬ x > c)]
      · simp only [Val.rename, if_neg hx, Val.subst,
          if_neg (by omega : ¬ x + 1 = c), if_pos (by omega : x + 1 > c),
          Nat.add_sub_cancel]
  | .real _, _, _ => rfl
  | .bool _, _, _ => rfl
  | .lam τ m, c, w => by
      simp only [Val.rename, Val.subst]
      rw [Tm.subst_rename_cancel m (c + 1) (w.rename 0)]
/-- Substituting at the cutoff `c` undoes renaming at `c` (terms). -/
theorem Tm.subst_rename_cancel : ∀ (m : Tm) (c : ℕ) (w : Val),
    (m.rename c).subst c w = m
  | .val v, c, w => by
      simp only [Tm.rename, Tm.subst]; rw [Val.subst_rename_cancel v c w]
  | .app v u, c, w => by
      simp only [Tm.rename, Tm.subst]
      rw [Val.subst_rename_cancel v c w, Val.subst_rename_cancel u c w]
  | .letin m b, c, w => by
      simp only [Tm.rename, Tm.subst]
      rw [Tm.subst_rename_cancel m c w,
        Tm.subst_rename_cancel b (c + 1) (w.rename 0)]
  | .choice p m1 m2, c, w => by
      simp only [Tm.rename, Tm.subst]
      rw [Tm.subst_rename_cancel m1 c w, Tm.subst_rename_cancel m2 c w]
  | .ascT m T, c, w => by
      simp only [Tm.rename, Tm.subst]; rw [Tm.subst_rename_cancel m c w]
  | .ascV v τ, c, w => by
      simp only [Tm.rename, Tm.subst]; rw [Val.subst_rename_cancel v c w]
  | .ite v m1 m2, c, w => by
      simp only [Tm.rename, Tm.subst]
      rw [Val.subst_rename_cancel v c w, Tm.subst_rename_cancel m1 c w,
        Tm.subst_rename_cancel m2 c w]
  | .add v u, c, w => by
      simp only [Tm.rename, Tm.subst]
      rw [Val.subst_rename_cancel v c w, Val.subst_rename_cancel u c w]
end

mutual
/-- Renaming at `c ≤ k` commutes with substituting a closed value at `k`, with
the index shifted to `k+1` after renaming (values). -/
theorem Val.rename_subst : ∀ (v : Val) (c k : ℕ), c ≤ k → ∀ (w : Val),
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
  | .real _, _, _, _, _, _ => rfl
  | .bool _, _, _, _, _, _ => rfl
  | .lam τ m, c, k, hck, w, hw => by
      simp only [Val.rename, Val.subst]
      rw [Val.rename_below hw (Nat.zero_le 0)]
      rw [Tm.rename_subst m (c + 1) (k + 1) (by omega) w hw]
/-- Renaming at `c ≤ k` commutes with substituting a closed value at `k`, with
the index shifted to `k+1` after renaming (terms). -/
theorem Tm.rename_subst : ∀ (m : Tm) (c k : ℕ), c ≤ k → ∀ (w : Val),
    w.FvBelow 0 → (m.rename c).subst (k + 1) w = (m.subst k w).rename c
  | .val v, c, k, hck, w, hw => by
      simp only [Tm.rename, Tm.subst]; rw [Val.rename_subst v c k hck w hw]
  | .app v u, c, k, hck, w, hw => by
      simp only [Tm.rename, Tm.subst]
      rw [Val.rename_subst v c k hck w hw, Val.rename_subst u c k hck w hw]
  | .letin m b, c, k, hck, w, hw => by
      simp only [Tm.rename, Tm.subst]
      rw [Tm.rename_subst m c k hck w hw, Val.rename_below hw (Nat.zero_le 0)]
      rw [Tm.rename_subst b (c + 1) (k + 1) (by omega) w hw]
  | .choice p m1 m2, c, k, hck, w, hw => by
      simp only [Tm.rename, Tm.subst]
      rw [Tm.rename_subst m1 c k hck w hw, Tm.rename_subst m2 c k hck w hw]
  | .ascT m T, c, k, hck, w, hw => by
      simp only [Tm.rename, Tm.subst]; rw [Tm.rename_subst m c k hck w hw]
  | .ascV v τ, c, k, hck, w, hw => by
      simp only [Tm.rename, Tm.subst]; rw [Val.rename_subst v c k hck w hw]
  | .ite v m1 m2, c, k, hck, w, hw => by
      simp only [Tm.rename, Tm.subst]
      rw [Val.rename_subst v c k hck w hw, Tm.rename_subst m1 c k hck w hw,
        Tm.rename_subst m2 c k hck w hw]
  | .add v u, c, k, hck, w, hw => by
      simp only [Tm.rename, Tm.subst]
      rw [Val.rename_subst v c k hck w hw, Val.rename_subst u c k hck w hw]
end

end GradualProb.SPLC
