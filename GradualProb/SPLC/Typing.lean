import GradualProb.SPLC.Equality

/-!
# The syntax and type system of SPLC

This module formalizes the static language SPLC of Section 3: well-formedness
of static types and contexts (Definitions 12 and 13), the operations on
distribution types used by the typing rules (scaling, sum, and the weighted sum
of rule (Tlet)), the term syntax, and the typing judgment of Figure 2 (`HasTyV`
for values, `HasTyT` for terms).  The side conditions `=ₛ` of the rules are the
coupling equality `EqTy`/`EqD` of `SPLC/Equality`, which coincides with `=ₛ` by
Lemma 2.

## Main results

* `wf_val`, `wf_tm`: Lemma 1 (type well-formedness), also Lemma 14 of the
  appendix.
* `wf_eq_ty`, `wf_eq_d`, `wf_eqD_entries`: Lemma 13 (well-formedness
  (equality)).
* `eqD_singleton`, `eqD_scale`, `eqD_add`, `eqD_letRes`: Lemma 15 (equality
  and the type operators).
* `det_val`, `det_tm`: typing is deterministic.
* `det_eq_val`, `det_eq_tm`: Lemma 16 (determinism modulo equality): the types
  of a static term under pointwise equal contexts are equal.

## Reading guide

Well-formedness and the operations on distribution types come first, with
the lemmas on their total probability; then the syntax, the staticness predicate on terms, the
typing judgment and Lemma 1; then the congruence of the type operations under `EqD`
(`eqD_scale`, `eqD_add`, `eqD_letRes`), used by `det_eq_tm`, each from the
construction on liftings of the same shape (`Lift.smul`, `Lift.append`,
`Lift.sigmaFin`) through `eqD_ofFn_iff`; then determinism and Lemma 16; last,
Lemma 13.
-/

namespace GradualProb.SPLC

open scoped BigOperators
open GradualProb.CouplingLemma
open Classical


/-! ## Well-formedness of static types -/

/- Well-formedness of static types (Definition 12): base types are
well-formed, an arrow is well-formed when its domain and codomain are, and a
distribution type is well-formed when its probabilities sum to `1` and every
entry is well-formed. -/
mutual
/-- Definition 12 (well-formedness of types), simple types: base types are
well-formed, and an arrow is well-formed when its domain and codomain are. -/
inductive WfTy : Ty → Prop where
  | real : WfTy .real
  | bool : WfTy .bool
  | arrow : ∀ {s d}, WfTy s → WfDTy d → WfTy (.arrow s d)
/-- Definition 12 (well-formedness of types), distribution types: every entry is
well-formed and the probabilities sum to `1`. -/
inductive WfDTy : DTy → Prop where
  | dist : ∀ {es : List (Ty × GProb)}, (∀ e ∈ es, WfTy e.1) →
             (es.map (fun e => pval e.2)).sum = 1 → WfDTy (.dist es)
end

/-- Every simple type of an entry list is well-formed. -/
abbrev WfEntries (es : List (Ty × GProb)) : Prop := ∀ e ∈ es, WfTy e.1

/-- The Dirac type on a well-formed simple type is well-formed. -/
theorem WfDTy.point {τ : Ty} (h : WfTy τ) : WfDTy (.dist [(τ, .q 1)]) :=
  .dist (fun _ he => by obtain rfl := List.mem_singleton.1 he; exact h) (by simp [pval])

/-- Total probability of an entry list. -/
def pmass (es : List (Ty × GProb)) : ℝ := (es.map (fun e => pval e.2)).sum
/-- Total probability of a distribution type. -/
def dmass : DTy → ℝ | .dist es => pmass es

/-- `WfEntriesD T`: the simple types in `T`'s entries are well-formed. -/
def WfEntriesD : DTy → Prop | .dist es => WfEntries es

/-! ## Operations on distribution types -/

/-- Scaling `c · T` of a distribution type (Figure 2): every probability is
multiplied by `c`. -/
def scaleD (c : ℝ) : DTy → DTy
  | .dist es => .dist (es.map (fun e => (e.1, GProb.q (c * pval e.2))))

/-- Sum `T1 + T2` of distribution types (Figure 2): the union of the two
multisets, as list concatenation.  The article defines the sum only when the total
probability is at most `1`; here it is total.  Where the typing rules use it, the
operands come from well-typed terms under a well-formed context, so they have
total probability `1` and are scaled by factors summing to `1` (Lemma 1), and the article's
condition holds. -/
def addD : DTy → DTy → DTy
  | .dist es1, .dist es2 => .dist (es1 ++ es2)

/-- The sum `Σ_k p_k · T_k` of a list of scaled distribution types. -/
def sumScaledList (L : List (ℝ × DTy)) : DTy :=
  L.foldr (fun pT acc => addD (scaleD pT.1 pT.2) acc) (.dist [])

/-- The type `Σ_i p_i · T_i` of a `let` (rule (Tlet)): each body type `T i`
scaled by the probability of the `i`-th entry of the bound term's type. -/
def letRes (es : List (Ty × GProb)) (T : Fin es.length → DTy) : DTy :=
  sumScaledList (List.ofFn (fun i => (pval (es.get i).2, T i)))

/-- The probability of a concrete probability `q c` is `c`. -/
@[simp] theorem pval_q (c : ℝ) : pval (GProb.q c) = c := rfl
/-- The empty distribution type has total probability `0`. -/
@[simp] theorem dmass_empty : dmass (.dist []) = 0 := rfl

/-! ## Total probability under the type operations -/

/-- Scaling every probability of an entry list by `c` scales its total probability
by `c`. -/
theorem pmass_scale (c : ℝ) (es : List (Ty × GProb)) :
    pmass (es.map (fun e => (e.1, GProb.q (c * pval e.2)))) = c * pmass es := by
  unfold pmass
  induction es with
  | nil => simp
  | cons a es ih => simp only [List.map_cons, List.sum_cons, pval_q]; rw [ih]; ring

/-- The total probability of `c · T` is `c` times that of `T`. -/
theorem dmass_scale (c : ℝ) (T : DTy) : dmass (scaleD c T) = c * dmass T := by
  cases T; simp only [scaleD, dmass]; exact pmass_scale c _

/-- The total probability of `T1 + T2` is the sum of their total probabilities. -/
theorem dmass_add (T1 T2 : DTy) : dmass (addD T1 T2) = dmass T1 + dmass T2 := by
  cases T1; cases T2
  simp only [addD, dmass, pmass, List.map_append, List.sum_append]

/-- The total probability of `Σ_k p_k · T_k` is the sum over `k` of `p_k`
times the total probability of `T_k`. -/
theorem dmass_sumScaledList (L : List (ℝ × DTy)) :
    dmass (sumScaledList L) = (L.map (fun pT => pT.1 * dmass pT.2)).sum := by
  induction L with
  | nil => simp [sumScaledList]
  | cons a L ih =>
      show dmass (addD (scaleD a.1 a.2) (sumScaledList L)) = _
      rw [dmass_add, dmass_scale, ih, List.map_cons, List.sum_cons]

/-- The total probability of an entry list as a `Finset` sum over its positions. -/
theorem pmass_eq_sum (es : List (Ty × GProb)) :
    pmass es = ∑ i, pval (es.get i).2 := by
  unfold pmass
  have : es.map (fun e => pval e.2) = List.ofFn (fun i => pval (es.get i).2) := by
    conv_lhs => rw [← List.ofFn_get es]
    rw [List.map_ofFn]; rfl
  rw [this, List.sum_ofFn]

/-- If every body type `T i` has total probability `1`, then the type
`Σ_i p_i · T_i` of a `let` has the total probability of the bound term's entries. -/
theorem dmass_letRes (es : List (Ty × GProb)) (T : Fin es.length → DTy)
    (hT : ∀ i, dmass (T i) = 1) : dmass (letRes es T) = pmass es := by
  unfold letRes
  rw [dmass_sumScaledList, List.map_ofFn, List.sum_ofFn, pmass_eq_sum]
  exact Finset.sum_congr rfl (fun i _ => by simp [Function.comp, hT i])

/-! ## Well-formedness of entries under the type operations -/

/-- Concatenating two lists of well-formed entries gives well-formed entries. -/
theorem wfEntries_append {es1 es2 : List (Ty × GProb)} (h1 : WfEntries es1)
    (h2 : WfEntries es2) : WfEntries (es1 ++ es2) :=
  List.forall_mem_append.2 ⟨h1, h2⟩

/-- Scaling the probabilities of an entry list preserves well-formed entries. -/
theorem wfEntries_scale (c : ℝ) {es : List (Ty × GProb)} (h : WfEntries es) :
    WfEntries (es.map (fun e => (e.1, GProb.q (c * pval e.2)))) :=
  List.forall_mem_map.2 fun e he => h e he

/-- `c · T` has well-formed entries when `T` does. -/
theorem wfEntriesD_scale (c : ℝ) {T : DTy} (h : WfEntriesD T) : WfEntriesD (scaleD c T) := by
  cases T with | dist es => exact wfEntries_scale c h

/-- `T1 + T2` has well-formed entries when `T1` and `T2` do. -/
theorem wfEntriesD_add {T1 T2 : DTy} (h1 : WfEntriesD T1) (h2 : WfEntriesD T2) :
    WfEntriesD (addD T1 T2) := by
  cases T1; cases T2; exact wfEntries_append h1 h2

/-- `Σ_k p_k · T_k` has well-formed entries when every `T_k` does. -/
theorem wfEntriesD_sumScaledList : ∀ {L : List (ℝ × DTy)},
    (∀ pT ∈ L, WfEntriesD pT.2) → WfEntriesD (sumScaledList L)
  | [], _ => List.forall_mem_nil _
  | a :: L, h => by
      exact wfEntriesD_add (wfEntriesD_scale a.1 (h a List.mem_cons_self))
        (wfEntriesD_sumScaledList (fun pT hpT => h pT (List.mem_cons_of_mem _ hpT)))

/-- The type `Σ_i p_i · T_i` of a `let` has well-formed entries when every body
type `T i` does. -/
theorem wfEntriesD_letRes (es : List (Ty × GProb)) (T : Fin es.length → DTy)
    (hT : ∀ i, WfEntriesD (T i)) : WfEntriesD (letRes es T) := by
  refine wfEntriesD_sumScaledList ?_
  intro pT hpT
  rw [List.mem_ofFn] at hpT
  obtain ⟨i, rfl⟩ := hpT
  exact hT i

/-- Assemble `WfDTy` from well-formed entries and total probability `1`. -/
theorem wfDTy_of (T : DTy) (he : WfEntriesD T) (hm : dmass T = 1) : WfDTy T := by
  cases T with | dist es => exact WfDTy.dist he hm

/-! ## Terms, contexts and the typing judgment -/

/-- Typing environments.  Variables are de Bruijn indices, so an environment is
a list of simple types indexed by position: the head is the type of the
innermost bound variable. -/
abbrev Ctx := List Ty

/- The terms of SPLC (Figure 1): values `Val` and computations `Tm`, with de
Bruijn variables.  Annotations range over the shared type syntax `Ty`/`DTy`;
`IsStaticVal`/`IsStaticTm` below cut out the terms of SPLC proper. -/
mutual
/-- Values of SPLC. -/
inductive Val where
  | var  : ℕ → Val
  | real : ℝ → Val
  | bool : Bool → Val
  | lam  : Ty → Tm → Val
/-- Computations of SPLC. -/
inductive Tm where
  | val    : Val → Tm
  | app    : Val → Val → Tm
  | letin  : Tm → Tm → Tm
  | choice : ℝ → Tm → Tm → Tm
  | ascT   : Tm → DTy → Tm
  | ascV   : Val → Ty → Tm
  | ite    : Val → Tm → Tm → Tm
  | add    : Val → Val → Tm
end

/-- Definition 13 (well-formedness of contexts): every type in the context is
well-formed. -/
def CtxWf (Γ : Ctx) : Prop := ∀ τ ∈ Γ, WfTy τ

/-! ## Inversion lemmas for well-formedness -/

/-- Extending a well-formed context with a well-formed type gives a well-formed
context. -/
theorem ctxWf_cons {τ : Ty} {Γ : Ctx} (hτ : WfTy τ) (hΓ : CtxWf Γ) : CtxWf (τ :: Γ) :=
  List.forall_mem_cons.2 ⟨hτ, hΓ⟩

/-- The codomain of a well-formed function type is well-formed. -/
theorem wfTy_cod : ∀ {s : Ty} {d : DTy}, WfTy (.arrow s d) → WfDTy d
  | _, _, .arrow _ hd => hd

/-- A well-formed distribution type has well-formed entries. -/
theorem wfDTy_wfEntriesD : ∀ {T : DTy}, WfDTy T → WfEntriesD T
  | _, .dist he _ => he

/-- A well-formed distribution type has total probability `1`. -/
theorem wfDTy_mass : ∀ {T : DTy}, WfDTy T → dmass T = 1
  | _, .dist _ hm => hm

/-- Inversion of `WfDTy` on a distribution type: well-formed entries and total
probability `1`. -/
theorem wfDTy_dist_inv {es : List (Ty × GProb)} (h : WfDTy (.dist es)) :
    WfEntries es ∧ pmass es = 1 := ⟨wfDTy_wfEntriesD h, wfDTy_mass h⟩


/- Static terms: every annotation is a static type and every choice
probability is in `[0,1]`, as the grammar of SPLC requires.  SPLC is the fragment
of GPLC without `?`: the terms of SPLC are the terms of this syntax that satisfy
`IsStaticVal`/`IsStaticTm`, and `GPLC.embedV`/`GPLC.embedT` include them in the
terms of GPLC. -/
mutual
/-- A value of SPLC with static annotations. -/
inductive IsStaticVal : Val → Prop where
  | var  : ∀ {x}, IsStaticVal (.var x)
  | real : ∀ {r}, IsStaticVal (.real r)
  | bool : ∀ {b}, IsStaticVal (.bool b)
  | lam  : ∀ {τ m}, IsStaticTy τ → IsStaticTm m → IsStaticVal (.lam τ m)
/-- A term of SPLC with static annotations and choice probabilities in `[0,1]`. -/
inductive IsStaticTm : Tm → Prop where
  | val    : ∀ {v}, IsStaticVal v → IsStaticTm (.val v)
  | app    : ∀ {v w}, IsStaticVal v → IsStaticVal w → IsStaticTm (.app v w)
  | letin  : ∀ {m n}, IsStaticTm m → IsStaticTm n → IsStaticTm (.letin m n)
  | choice : ∀ {p m n}, 0 ≤ p → p ≤ 1 → IsStaticTm m → IsStaticTm n → IsStaticTm (.choice p m n)
  | ascT   : ∀ {m T}, IsStaticTm m → IsStaticDTy T → IsStaticTm (.ascT m T)
  | ascV   : ∀ {v τ}, IsStaticVal v → IsStaticTy τ → IsStaticTm (.ascV v τ)
  | ite    : ∀ {v m n}, IsStaticVal v → IsStaticTm m → IsStaticTm n → IsStaticTm (.ite v m n)
  | add    : ∀ {v w}, IsStaticVal v → IsStaticVal w → IsStaticTm (.add v w)
end

/-- Every type in the context is static. -/
def CtxStatic (Γ : Ctx) : Prop := ∀ τ ∈ Γ, IsStaticTy τ

/-- Extending a static context with a static type gives a static context. -/
theorem ctxStatic_cons {τ : Ty} {Γ : Ctx} (hτ : IsStaticTy τ) (hΓ : CtxStatic Γ) :
    CtxStatic (τ :: Γ) :=
  List.forall_mem_cons.2 ⟨hτ, hΓ⟩

/-- Concatenating two static entry lists gives a static entry list. -/
theorem isStaticEntries_append {es1 es2 : List (Ty × GProb)} (h1 : IsStaticEntries es1)
    (h2 : IsStaticEntries es2) : IsStaticEntries (es1 ++ es2) :=
  List.forall_mem_append.2 ⟨h1, h2⟩

/-- Scaling a static entry list by `c ∈ [0,1]` gives a static entry list. -/
theorem isStaticEntries_scale {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) {es : List (Ty × GProb)}
    (h : IsStaticEntries es) :
    IsStaticEntries (es.map (fun e => (e.1, GProb.q (c * pval e.2)))) := by
  refine List.forall_mem_map.2 fun e he => ?_
  obtain ⟨ht, r, hp, hrnn, hr1⟩ := h e he
  refine ⟨ht, _, rfl, ?_, ?_⟩
  · rw [hp]; exact mul_nonneg hc hrnn
  · rw [hp]; exact mul_le_one₀ hc1 hrnn hr1

/-- `c · T` is static when `T` is static and `c ∈ [0,1]`. -/
theorem isStatic_scaleD {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) : ∀ {T : DTy},
    IsStaticDTy T → IsStaticDTy (scaleD c T)
  | .dist _, h => .ofEntries (isStaticEntries_scale hc hc1 h.entries)

/-- `T1 + T2` is static when `T1` and `T2` are. -/
theorem isStatic_addD : ∀ {T1 T2 : DTy}, IsStaticDTy T1 → IsStaticDTy T2 →
    IsStaticDTy (addD T1 T2)
  | .dist _, .dist _, h1, h2 => .ofEntries (isStaticEntries_append h1.entries h2.entries)

/-- `Σ_k p_k · T_k` is static when every `T_k` is static and every `p_k ∈ [0,1]`. -/
theorem isStatic_sumScaledList : ∀ {L : List (ℝ × DTy)},
    (∀ pT ∈ L, 0 ≤ pT.1 ∧ pT.1 ≤ 1 ∧ IsStaticDTy pT.2) → IsStaticDTy (sumScaledList L)
  | [], _ => .dist (List.forall_mem_nil _) (List.forall_mem_nil _)
  | a :: L, h => by
      obtain ⟨hnn, h1, hT⟩ := h a List.mem_cons_self
      exact isStatic_addD (isStatic_scaleD hnn h1 hT)
        (isStatic_sumScaledList (fun pT hpT => h pT (List.mem_cons_of_mem _ hpT)))

/-- The type `Σ_i p_i · T_i` of a `let` is static when the bound term's entries
and every body type `T i` are static. -/
theorem isStatic_letRes {es : List (Ty × GProb)} {T : Fin es.length → DTy}
    (hes : IsStaticEntries es) (hT : ∀ i, IsStaticDTy (T i)) :
    IsStaticDTy (letRes es T) := by
  refine isStatic_sumScaledList ?_
  intro pT hpT
  rw [List.mem_ofFn] at hpT
  obtain ⟨i, rfl⟩ := hpT
  exact ⟨pval_nonneg_mem hes _ (List.get_mem es i), pval_le_one_mem hes _ (List.get_mem es i),
    hT i⟩


/-- The entry list of a distribution type. -/
@[reducible] def dentries : DTy → List (Ty × GProb)
  | .dist es => es

/-- The entries of `{es}` are `es`. -/
@[simp] theorem dentries_dist (es : List (Ty × GProb)) : dentries (.dist es) = es := rfl

/-- The entries of `c · T`. -/
theorem dentries_scaleD (c : ℝ) (T : DTy) :
    dentries (scaleD c T) = (dentries T).map (fun e => (e.1, GProb.q (c * pval e.2))) := by
  cases T; rfl

/-- The entries of `T1 + T2`. -/
theorem dentries_addD (T1 T2 : DTy) :
    dentries (addD T1 T2) = dentries T1 ++ dentries T2 := by
  cases T1; cases T2; rfl

/-- Length of the entries of a `sumScaledList` over an `ofFn` list. -/
theorem dentries_sumScaled_length {nn : ℕ} (f : Fin nn → ℝ × DTy) :
    (dentries (sumScaledList (List.ofFn f))).length
      = ∑ j, (dentries (f j).2).length := by
  induction nn with
  | zero => simp [sumScaledList, List.ofFn_zero]
  | succ n ih =>
    rw [List.ofFn_succ]
    show (dentries (addD (scaleD (f 0).1 (f 0).2)
      (sumScaledList (List.ofFn fun i => f i.succ)))).length = _
    rw [dentries_addD, dentries_scaleD, List.length_append, List.length_map,
      ih, Fin.sum_univ_succ]

/-- Entries of a `sumScaledList` over an `ofFn` list, at offset positions:
position `(∑ i < j, lenᵢ) + l` holds the `l`-th entry of the `j`-th block,
scaled. -/
theorem dentries_sumScaled_getElem : ∀ {nn : ℕ} (f : Fin nn → ℝ × DTy)
    (j : Fin nn) (l : Fin (dentries (f j).2).length) {v : ℕ},
    v = (∑ i : Fin (j : ℕ),
      (dentries (f (Fin.castLE j.isLt.le i)).2).length) + (l : ℕ) →
    ∀ h : v < (dentries (sumScaledList (List.ofFn f))).length,
    (dentries (sumScaledList (List.ofFn f)))[v]
      = (((dentries (f j).2).get l).1,
         GProb.q ((f j).1 * pval ((dentries (f j).2).get l).2))
  | 0, f, j, l, v, hv, h => absurd j.isLt (by simp)
  | (n + 1), f, j, l, v, hv, h => by
      have hlists : dentries (sumScaledList (List.ofFn f))
          = (dentries (f 0).2).map (fun e => (e.1, GProb.q ((f 0).1 * pval e.2)))
            ++ dentries (sumScaledList (List.ofFn fun i => f i.succ)) := by
        rw [List.ofFn_succ]
        show dentries (addD (scaleD (f 0).1 (f 0).2) _) = _
        rw [dentries_addD, dentries_scaleD]
        rfl
      rw [List.getElem_of_eq hlists h]
      revert hv
      revert l
      induction j using Fin.cases with
      | zero =>
        intro l hv
        have hv0 : v = (l : ℕ) := by simpa using hv
        subst hv0
        rw [List.getElem_append_left (by simpa using l.isLt)]
        rw [List.getElem_map]
        rfl
      | succ jp =>
        intro l hv
        -- peel the head block off the offset
        have hsum : (∑ i : Fin ((jp.succ : Fin (n + 1)) : ℕ),
            (dentries (f (Fin.castLE (jp.succ : Fin (n + 1)).isLt.le i)).2).length)
            = (dentries (f 0).2).length
              + ∑ i : Fin (jp : ℕ),
                (dentries ((fun k => f k.succ)
                  (Fin.castLE jp.isLt.le i)).2).length := by
          show (∑ i : Fin ((jp : ℕ) + 1), _) = _
          rw [Fin.sum_univ_succ]
          have h0 : (Fin.castLE (jp.succ : Fin (n + 1)).isLt.le (0 : Fin ((jp : ℕ) + 1)))
              = (0 : Fin (n + 1)) := Fin.ext (by simp)
          rw [h0]
          congr 1
        have hge : ((dentries (f 0).2).map
            (fun e => (e.1, GProb.q ((f 0).1 * pval e.2)))).length ≤ v := by
          rw [List.length_map, hv, hsum]
          omega
        rw [List.getElem_append_right hge]
        have hrest : v - ((dentries (f 0).2).map
            (fun e => (e.1, GProb.q ((f 0).1 * pval e.2)))).length
            = (∑ i : Fin (jp : ℕ),
                (dentries ((fun k => f k.succ)
                  (Fin.castLE jp.isLt.le i)).2).length) + (l : ℕ) := by
          rw [List.length_map, hv, hsum]
          omega
        have hbound : v - ((dentries (f 0).2).map
            (fun e => (e.1, GProb.q ((f 0).1 * pval e.2)))).length
            < (dentries (sumScaledList (List.ofFn fun i => f i.succ))).length := by
          have h2 := h
          rw [hlists, List.length_append] at h2
          omega
        exact dentries_sumScaled_getElem (fun k => f k.succ) jp l hrest hbound

/-- Sum transport: a sum over the flattened static index, with the summand
pre-composed with the (cast of the) packing equivalence, decomposes into the
double sum. -/
theorem sum_sigma_proj_cast {m : ℕ} {n : Fin m → ℕ} {N : ℕ} (h : N = ∑ i, n i)
    (g : (i : Fin m) → Fin (n i) → ℝ) :
    (∑ κ : Fin N, g (finSigmaFinEquiv.symm (Fin.cast h κ)).1
        (finSigmaFinEquiv.symm (Fin.cast h κ)).2)
      = ∑ i, ∑ k, g i k := by
  rw [← sum_sigma_proj g]
  exact Equiv.sum_comp (finCongr h)
    (fun κ => g (finSigmaFinEquiv.symm κ).1 (finSigmaFinEquiv.symm κ).2)

/-- A distribution type is the distribution type of its entries. -/
theorem dist_dentries : ∀ T : DTy, DTy.dist (dentries T) = T
  | .dist _ => rfl

/-- The entries of `Σ_j p_j · T_j` as a family over the dependent concatenation
of the entry lists of the `T_j`: the entry at position `κ` is the entry
`(finSigmaFinEquiv.symm κ).2` of the block `(finSigmaFinEquiv.symm κ).1`,
scaled by the weight of the block. -/
theorem dentries_sumScaled_ofFn {nn : ℕ} (f : Fin nn → ℝ × DTy) :
    dentries (sumScaledList (List.ofFn f))
      = List.ofFn fun κ : Fin (∑ j, (dentries (f j).2).length) =>
          (((dentries (f (finSigmaFinEquiv.symm κ).1).2).get (finSigmaFinEquiv.symm κ).2).1,
            GProb.q ((f (finSigmaFinEquiv.symm κ).1).1
              * pval ((dentries (f (finSigmaFinEquiv.symm κ).1).2).get
                  (finSigmaFinEquiv.symm κ).2).2)) := by
  refine List.ext_getElem (by rw [dentries_sumScaled_length, List.length_ofFn]) fun v h1 h2 => ?_
  rw [List.getElem_ofFn]
  refine dentries_sumScaled_getElem f _ _ ?_ h1
  have hv := congrArg Fin.val (finSigmaFinEquiv.apply_symm_apply ⟨v, by simpa using h2⟩)
  rw [finSigmaFinEquiv_apply] at hv
  exact hv.symm

/-- The premises of an equality of distribution types, on the entry lists of
the two types: the lifting of `EqTy` to the entries, and coverage in both
directions. -/
theorem EqD.entries : ∀ {T T' : DTy}, EqD T T' →
    Lift (fun i j => EqTy ((dentries T).get i).1 ((dentries T').get j).1)
      (fun i => pval ((dentries T).get i).2) (fun j => pval ((dentries T').get j).2) ∧
    (∀ i, ∃ j, EqTy ((dentries T).get i).1 ((dentries T').get j).1) ∧
    (∀ j, ∃ i, EqTy ((dentries T).get i).1 ((dentries T').get j).1)
  | .dist _, .dist _, h => ⟨h.coup, h.cov⟩

/- The typing judgment of SPLC (Figure 2): `HasTyV Γ v τ` is `Γ ⊢ₛ v : τ` and
`HasTyT Γ m T` is `Γ ⊢ₛ m : T`.  The `=ₛ` premises are `EqTy`/`EqD`.  Rule (Tv)
is the constructor `HasTyT.val`; rule (Tlet) types the body once for every entry
of the bound term's type.  Rule (V), for distribution values, is
`DistValHasTy` in `SPLC/TypeSafety`. -/
mutual
/-- Typing of values. -/
inductive HasTyV : Ctx → Val → Ty → Prop where
  | var  : ∀ {Γ x τ}, Γ[x]? = some τ → HasTyV Γ (.var x) τ
  | real : ∀ {Γ r}, HasTyV Γ (.real r) .real
  | bool : ∀ {Γ b}, HasTyV Γ (.bool b) .bool
  | lam  : ∀ {Γ τ m T}, HasTyT (τ :: Γ) m T → WfTy τ →
             HasTyV Γ (.lam τ m) (.arrow τ T)
/-- Typing of terms. -/
inductive HasTyT : Ctx → Tm → DTy → Prop where
  | val   : ∀ {Γ v τ}, HasTyV Γ v τ → HasTyT Γ (.val v) (.dist [(τ, .q 1)])
  | app   : ∀ {Γ v w s d τ2}, HasTyV Γ v (.arrow s d) → HasTyV Γ w τ2 →
              EqTy s τ2 → HasTyT Γ (.app v w) d
  | letin : ∀ {Γ m n es} {T : Fin es.length → DTy},
              HasTyT Γ m (.dist es) →
              (∀ i, HasTyT ((es.get i).1 :: Γ) n (T i)) →
              HasTyT Γ (.letin m n) (letRes es T)
  | choice : ∀ {Γ p m n T1 T2}, HasTyT Γ m T1 → HasTyT Γ n T2 →
               HasTyT Γ (.choice p m n) (addD (scaleD p T1) (scaleD (1 - p) T2))
  | ascT  : ∀ {Γ m T T'}, HasTyT Γ m T' → EqD T' T → WfDTy T →
              HasTyT Γ (.ascT m T) T
  | ascV  : ∀ {Γ v τ τ'}, HasTyV Γ v τ' → EqTy τ' τ → WfTy τ →
              HasTyT Γ (.ascV v τ) (.dist [(τ, .q 1)])
  | add   : ∀ {Γ v w τ1 τ2}, HasTyV Γ v τ1 → EqTy τ1 .real → HasTyV Γ w τ2 →
              EqTy τ2 .real → HasTyT Γ (.add v w) (.dist [(.real, .q 1)])
  | ite   : ∀ {Γ v m n τ T1 T2}, HasTyV Γ v τ → EqTy τ .bool →
              HasTyT Γ m T1 → HasTyT Γ n T2 → EqD T1 T2 →
              HasTyT Γ (.ite v m n) T1
end

/-- `Γ ⊢ₛ v : τ`, the typing of values of SPLC (Figure 2). -/
scoped notation:50 (name := hasTyVStx) Γ:51 " ⊢ₛ " v:51 " : " τ:51 => HasTyV Γ v τ
/-- `Γ ⊢ₛ m : T`, the typing of terms of SPLC (Figure 2). -/
scoped notation:50 (name := hasTyTStx) Γ:51 " ⊢ₛ " m:51 " : " T:51 => HasTyT Γ m T
/-- `⊢ₛ v : τ`, the typing of closed values. -/
scoped notation:50 (name := hasTyVClosedStx) "⊢ₛ " v:51 " : " τ:51 => HasTyV [] v τ
/-- `⊢ₛ m : T`, the typing of closed terms. -/
scoped notation:50 (name := hasTyTClosedStx) "⊢ₛ " m:51 " : " T:51 => HasTyT [] m T

/-- A variable bound in a static context has a static type. -/
theorem ctxStatic_get {Γ : Ctx} {x : ℕ} {τ : Ty}
    (hΓ : CtxStatic Γ) (hx : Γ[x]? = some τ) : IsStaticTy τ :=
  hΓ τ (List.mem_of_getElem? hx)

/-- A variable bound in a well-formed context has a well-formed type. -/
theorem ctxWf_get {Γ : Ctx} {x : ℕ} {τ : Ty}
    (hΓ : CtxWf Γ) (hx : Γ[x]? = some τ) : WfTy τ :=
  hΓ τ (List.mem_of_getElem? hx)

/- A static term typed under a static context has a static type. -/
mutual
/-- Under a static context, the type of a static value is static. -/
theorem isStatic_val : ∀ {Γ v τ}, HasTyV Γ v τ → CtxStatic Γ → IsStaticVal v → IsStaticTy τ
  | _, _, _, .var hx, hΓ, _ => ctxStatic_get hΓ hx
  | _, _, _, .real, _, _ => .real
  | _, _, _, .bool, _, _ => .bool
  | _, _, _, .lam hm _, hΓ, hs => by
      cases hs with
      | lam hsτ hsm =>
        exact .arrow hsτ (isStatic_tm hm (ctxStatic_cons hsτ hΓ) hsm)
/-- Under a static context, the type of a static term is static. -/
theorem isStatic_tm : ∀ {Γ m T}, HasTyT Γ m T → CtxStatic Γ → IsStaticTm m → IsStaticDTy T
  | _, _, _, .val hv, hΓ, hs => by
      cases hs with
      | val hsv =>
        exact IsStaticDTy.point (isStatic_val hv hΓ hsv)
  | _, _, _, .app hv _ _, hΓ, hs => by
      cases hs with
      | app hsv _ =>
        cases isStatic_val hv hΓ hsv with
        | arrow _ hd => exact hd
  | _, _, _, .letin (es := es) (T := T) hm hF, hΓ, hs => by
      cases hs with
      | letin hsm hsn =>
        have hes : IsStaticEntries es := by
          exact (isStatic_tm hm hΓ hsm).entries
        exact isStatic_letRes hes (fun i => isStatic_tm (hF i)
          (ctxStatic_cons (entry_static_ty_mem hes _ (List.get_mem es i)) hΓ) hsn)
  | _, _, _, .choice hm hn, hΓ, hs => by
      cases hs with
      | choice hp0 hp1 hsm hsn =>
        exact isStatic_addD (isStatic_scaleD hp0 hp1 (isStatic_tm hm hΓ hsm))
          (isStatic_scaleD (by linarith) (by linarith) (isStatic_tm hn hΓ hsn))
  | _, _, _, .ascT _ _ _, hΓ, hs => by
      cases hs with
      | ascT _ hsT => exact hsT
  | _, _, _, .ascV _ _ _, hΓ, hs => by
      cases hs with
      | ascV _ hsτ => exact IsStaticDTy.point hsτ
  | _, _, _, .add _ _ _ _, _, _ =>
      IsStaticDTy.point .real
  | _, _, _, .ite _ _ hm hn _, hΓ, hs => by
      cases hs with
      | ite _ hsm _ => exact isStatic_tm hm hΓ hsm
end

/- Lemma 1 (type well-formedness), also Lemma 14 of the appendix. -/
mutual
/-- Lemma 1 (type well-formedness), item 1, also Lemma 14 (well-formed types),
item 1: under a well-formed context, the type of a value is well-formed. -/
theorem wf_val : ∀ {Γ} {v : Val} {τ}, Γ ⊢ₛ v : τ → CtxWf Γ → WfTy τ
  | _, _, _, .var hx, hΓ => ctxWf_get hΓ hx
  | _, _, _, .real, _ => .real
  | _, _, _, .bool, _ => .bool
  | _, _, _, .lam hm hτ, hΓ => .arrow hτ (wf_tm hm (ctxWf_cons hτ hΓ))
/-- Lemma 1 (type well-formedness), item 2, also Lemma 14 (well-formed types),
item 2: under a well-formed context, the type of a term is well-formed. -/
theorem wf_tm : ∀ {Γ} {m : Tm} {T}, Γ ⊢ₛ m : T → CtxWf Γ → WfDTy T
  | _, _, _, .val hv, hΓ => WfDTy.point (wf_val hv hΓ)
  | _, _, _, .app hv _ _, hΓ => wfTy_cod (wf_val hv hΓ)
  | _, _, _, .letin (es := es) (T := T) hm hF, hΓ => by
      obtain ⟨hEs, hpm⟩ := wfDTy_dist_inv (wf_tm hm hΓ)
      have hTi : ∀ i, WfDTy (T i) := fun i =>
        wf_tm (hF i) (ctxWf_cons (hEs _ (List.get_mem es i)) hΓ)
      refine wfDTy_of _
        (wfEntriesD_letRes _ _ (fun i => wfDTy_wfEntriesD (hTi i))) ?_
      rw [dmass_letRes _ _ (fun i => wfDTy_mass (hTi i))]
      exact hpm
  | _, _, _, .choice hm hn, hΓ => by
      have h1 := wf_tm hm hΓ
      have h2 := wf_tm hn hΓ
      refine wfDTy_of _
        (wfEntriesD_add (wfEntriesD_scale _ (wfDTy_wfEntriesD h1))
          (wfEntriesD_scale _ (wfDTy_wfEntriesD h2))) ?_
      rw [dmass_add, dmass_scale, dmass_scale, wfDTy_mass h1, wfDTy_mass h2]
      ring
  | _, _, _, .ascT _ _ hT, _ => hT
  | _, _, _, .ascV _ _ hτ, _ => WfDTy.point hτ
  | _, _, _, .add _ _ _ _, _ => WfDTy.point WfTy.real
  | _, _, _, .ite _ _ hm _ _, hΓ => wf_tm hm hΓ
end

/-- Lemma 15 (equality and the type operators), item 1: if `τ =ₛ τ'`, then
`{τ¹} =ₛ {τ'¹}`. -/
theorem eqD_singleton {τ τ' : Ty} (h : τ =ₛ τ') :
    .dist [(τ, .q 1)] =ₛ .dist [(τ', .q 1)] :=
  EqD.intro (Lift.point rfl rfl h)
    ⟨fun i => ⟨⟨0, by simp⟩, by fin_cases i; exact h⟩,
     fun j => ⟨⟨0, by simp⟩, by fin_cases j; exact h⟩⟩

/-- Lemma 15 (equality and the type operators), item 2, scaling: if `T =ₛ T'` and
`c ≥ 0`, then `c · T =ₛ c · T'`.  The lifting is the scaled one (`Lift.smul`). -/
theorem eqD_scale {c : ℝ} (hc : 0 ≤ c) : ∀ {T T' : DTy},
    T =ₛ T' → scaleD c T =ₛ scaleD c T'
  | .dist es, .dist es', h => by
      show EqD (.dist (es.map fun e => (e.1, GProb.q (c * pval e.2))))
        (.dist (es'.map fun e => (e.1, GProb.q (c * pval e.2))))
      rw [map_eq_ofFn_get, map_eq_ofFn_get]
      exact eqD_ofFn_iff.2 ⟨h.coup.smul hc, h.cov.1, h.cov.2⟩

/-- Lemma 15 (equality and the type operators), item 2, sum: if `A =ₛ A'` and
`B =ₛ B'`, then `A + B =ₛ A' + B'`.  The two liftings sit side by side
(`Lift.append`). -/
theorem eqD_add : ∀ {A A' B B' : DTy}, A =ₛ A' → B =ₛ B' →
    addD A B =ₛ addD A' B'
  | .dist a, .dist a', .dist b, .dist b', hA, hB => by
      show EqD (.dist (a ++ b)) (.dist (a' ++ b'))
      rw [← List.ofFn_get a, ← List.ofFn_get b, ← List.ofFn_get a', ← List.ofFn_get b',
        ← List.ofFn_fin_append, ← List.ofFn_fin_append]
      refine eqD_ofFn_iff.2 ⟨?_, fun i => ?_, fun j => ?_⟩
      · refine (hA.coup.append hB.coup (fun _ _ h => ?_) (fun _ _ h => ?_)).congr
          (fun i => ?_) (fun j => ?_)
        · simpa using h
        · simpa using h
        · induction i using Fin.addCases <;> simp
        · induction j using Fin.addCases <;> simp
      · induction i using Fin.addCases with
        | left i => exact (hA.cov.1 i).imp' (Fin.castAdd _) fun j hj => by simpa using hj
        | right i => exact (hB.cov.1 i).imp' (Fin.natAdd _) fun j hj => by simpa using hj
      · induction j using Fin.addCases with
        | left j => exact (hA.cov.2 j).imp' (Fin.castAdd _) fun i hi => by simpa using hi
        | right j => exact (hB.cov.2 j).imp' (Fin.natAdd _) fun i hi => by simpa using hi

/-- Equality of two weighted sums `Σⱼ pⱼ · Tⱼ` and `Σⱼ' p'ⱼ' · T'ⱼ'`: if the
weights are related by the lifting of `=ₛ` on the summands, and every summand
on either side has an `=ₛ` summand on the other, then the sums are equal.  The
lifting is the product (`Lift.sigmaFin`) of the lifting between the weights
with the liftings between the related summands. -/
theorem eqD_sumScaled {n n' : ℕ} {f : Fin n → ℝ × DTy} {f' : Fin n' → ℝ × DTy}
    (hlift : Lift (fun j j' => EqD (f j).2 (f' j').2) (fun j => (f j).1) (fun j' => (f' j').1))
    (hcovL : ∀ j, ∃ j', EqD (f j).2 (f' j').2) (hcovR : ∀ j', ∃ j, EqD (f j).2 (f' j').2) :
    EqD (sumScaledList (List.ofFn f)) (sumScaledList (List.ofFn f')) := by
  obtain ⟨u, hu, hs⟩ := hlift
  rw [← dist_dentries (sumScaledList (List.ofFn f)),
    ← dist_dentries (sumScaledList (List.ofFn f')), dentries_sumScaled_ofFn,
    dentries_sumScaled_ofFn]
  refine eqD_ofFn_iff.2 ⟨?_, fun κ => ?_, fun κ' => ?_⟩
  · refine (Lift.sigmaFin hu hs (fun j j' h => h.entries.1) fun j j' l l' _ h => ?_).congr
      (fun _ => rfl) fun κ' => ?_
    · rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact h
    · rw [← Finset.sum_mul, hu.col]
      rfl
  · obtain ⟨j', hj'⟩ := hcovL (finSigmaFinEquiv.symm κ).1
    obtain ⟨l', hl'⟩ := hj'.entries.2.1 (finSigmaFinEquiv.symm κ).2
    refine ⟨finSigmaFinEquiv ⟨j', l'⟩, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact hl'
  · obtain ⟨j, hj⟩ := hcovR (finSigmaFinEquiv.symm κ').1
    obtain ⟨l, hl⟩ := hj.entries.2.2 (finSigmaFinEquiv.symm κ').2
    refine ⟨finSigmaFinEquiv ⟨j, l⟩, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact hl

/-- Lemma 15 (equality and the type operators), item 3: if
the probabilities of `{τᵢ^{pᵢ}}` and `{τ'ⱼ^{p'ⱼ}}` are related by the lifting
of `=ₛ` on the body types, and every body type on either side has an `=ₛ` body
type on the other, then `Σᵢ pᵢ · Tᵢ =ₛ Σⱼ p'ⱼ · T'ⱼ`. -/
theorem eqD_letRes {es es' : List (Ty × GProb)} {Ts : Fin es.length → DTy}
    {Ts' : Fin es'.length → DTy}
    (hlift : Lift (fun j j' => Ts j =ₛ Ts' j')
      (fun j => pval (es.get j).2) (fun j' => pval (es'.get j').2))
    (hbcovL : ∀ j, ∃ j', Ts j =ₛ Ts' j')
    (hbcovR : ∀ j', ∃ j, Ts j =ₛ Ts' j') :
    letRes es Ts =ₛ letRes es' Ts' :=
  eqD_sumScaled hlift hbcovL hbcovR

/- Typing is deterministic. -/
mutual
/-- Typing of values is deterministic: if `Γ ⊢ₛ v : τ₁` and `Γ ⊢ₛ v : τ₂`, then
`τ₁ = τ₂`. -/
theorem det_val : ∀ {Γ v τ1 τ2}, HasTyV Γ v τ1 → HasTyV Γ v τ2 → τ1 = τ2
  | _, _, _, _, .var hx, h2 => by
      cases h2 with
      | var hx' => exact Option.some.inj (hx.symm.trans hx')
  | _, _, _, _, .real, h2 => by cases h2 with | real => rfl
  | _, _, _, _, .bool, h2 => by cases h2 with | bool => rfl
  | _, _, _, _, .lam hm _, h2 => by
      cases h2 with
      | lam hm' _ => rw [det_tm hm hm']
/-- Typing of terms is deterministic: if `Γ ⊢ₛ m : T₁` and `Γ ⊢ₛ m : T₂`, then
`T₁ = T₂`. -/
theorem det_tm : ∀ {Γ m T1 T2}, HasTyT Γ m T1 → HasTyT Γ m T2 → T1 = T2
  | _, _, _, _, .val hv, h2 => by
      cases h2 with
      | val hv' => rw [det_val hv hv']
  | _, _, _, _, .app hv _ _, h2 => by
      cases h2 with
      | app hv' _ _ =>
        have h := det_val hv hv'
        injection h with _ hd
  | _, _, _, _, @HasTyT.letin _ _ _ es T hm hF, h2 => by
      cases h2 with
      | @letin _ _ _ es2 T2 hm' hF' =>
        have h := det_tm hm hm'
        injection h with hes
        subst hes
        have hfun : (fun j : Fin es.length => (pval (es.get j).2, T j))
            = (fun j : Fin es.length => (pval (es.get j).2, T2 j)) := by
          funext j
          rw [det_tm (hF j) (hF' j)]
        unfold letRes
        rw [hfun]
  | _, _, _, _, .choice hm hn, h2 => by
      cases h2 with
      | choice hm' hn' => rw [det_tm hm hm', det_tm hn hn']
  | _, _, _, _, .ascT _ _ _, h2 => by
      cases h2 with
      | ascT _ _ _ => rfl
  | _, _, _, _, .ascV _ _ _, h2 => by
      cases h2 with
      | ascV _ _ _ => rfl
  | _, _, _, _, .add _ _ _ _, h2 => by
      cases h2 with
      | add _ _ _ _ => rfl
  | _, _, _, _, .ite _ _ hm hn _, h2 => by
      cases h2 with
      | ite _ _ hm' _ _ => exact det_tm hm hm'
end

/-- Pointwise equality `EqTy` of two contexts. -/
def EqCtx (Γ Γ' : Ctx) : Prop := List.Forall₂ EqTy Γ Γ'

/-- A static context is pointwise equal to itself. -/
theorem eqCtx_refl : ∀ {Γ : Ctx}, CtxStatic Γ → EqCtx Γ Γ
  | [], _ => .nil
  | τ :: Γ, h => .cons (EqTy.refl (h τ List.mem_cons_self))
      (eqCtx_refl (fun σ hσ => h σ (List.mem_cons_of_mem _ hσ)))

/-- A variable bound in `Γ` is bound in a pointwise equal `Γ'` at an equal type. -/
theorem eqCtx_getElem : ∀ {Γ Γ' : Ctx}, EqCtx Γ Γ' → ∀ {x : ℕ} {τ : Ty},
    Γ[x]? = some τ → ∃ τ', Γ'[x]? = some τ' ∧ EqTy τ τ'
  | _, _, .nil, x, τ, hx => by simp at hx
  | _, _, .cons hab htail, x, τ, hx => by
      cases x with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨_, by simp, hab⟩
      | succ n =>
        simp only [List.getElem?_cons_succ] at hx
        obtain ⟨τ', h1, h2⟩ := eqCtx_getElem htail hx
        exact ⟨τ', by simpa using h1, h2⟩

mutual
/-- Lemma 16 (determinism modulo equality), values: a static value typed under
two well-formed, pointwise equal contexts gets equal types. -/
theorem det_eq_val : ∀ {Γ Γ'} {v : Val} {τ τ'}, Γ ⊢ₛ v : τ → Γ' ⊢ₛ v : τ' →
    EqCtx Γ Γ' → CtxStatic Γ → CtxStatic Γ' → CtxWf Γ → CtxWf Γ' → IsStaticVal v →
    τ =ₛ τ'
  | _, _, _, _, _, .var hx, h2, hctx, _, _, _, _, _ => by
      cases h2 with
      | var hx' =>
        obtain ⟨τ'', hx'', hceq⟩ := eqCtx_getElem hctx hx
        exact (Option.some.inj (hx''.symm.trans hx')) ▸ hceq
  | _, _, _, _, _, .real, h2, _, _, _, _, _, _ => by
      cases h2 with | real => exact .real
  | _, _, _, _, _, .bool, h2, _, _, _, _, _, _ => by
      cases h2 with | bool => exact .bool
  | _, _, _, _, _, .lam hm hwτ, h2, hctx, hΓ, hΓ', hΓw, hΓw', hsv => by
      cases h2 with
      | lam hm' _ =>
        cases hsv with
        | lam hsτ hsm =>
          exact .arrow (EqTy.refl hsτ)
            (det_eq_tm hm hm' (.cons (EqTy.refl hsτ) hctx)
              (ctxStatic_cons hsτ hΓ) (ctxStatic_cons hsτ hΓ')
              (ctxWf_cons hwτ hΓw) (ctxWf_cons hwτ hΓw') hsm)
/-- Lemma 16 (determinism modulo equality), terms: a static term typed under
two well-formed, pointwise equal contexts gets equal types. -/
theorem det_eq_tm : ∀ {Γ Γ'} {m : Tm} {T T'}, Γ ⊢ₛ m : T → Γ' ⊢ₛ m : T' →
    EqCtx Γ Γ' → CtxStatic Γ → CtxStatic Γ' → CtxWf Γ → CtxWf Γ' → IsStaticTm m →
    T =ₛ T'
  | _, _, _, _, _, .val hv, h2, hctx, hΓ, hΓ', hΓw, hΓw', hs => by
      cases h2 with
      | val hv' =>
        cases hs with
        | val hsv => exact eqD_singleton (det_eq_val hv hv' hctx hΓ hΓ' hΓw hΓw' hsv)
  | _, _, _, _, _, .app hv _ _, h2, hctx, hΓ, hΓ', hΓw, hΓw', hs => by
      cases h2 with
      | app hv' _ _ =>
        cases hs with
        | app hsv _ =>
          have h := det_eq_val hv hv' hctx hΓ hΓ' hΓw hΓw' hsv
          cases h with
          | arrow _ hd => exact hd
  | _, _, _, _, _, @HasTyT.letin _ _ nb es T hm hF, h2, hctx, hΓ, hΓ', hΓw, hΓw', hs => by
      cases h2 with
      | @letin _ _ _ es2 T2 hm2 hF2 =>
        cases hs with
        | letin hsm hsn =>
          have hes : IsStaticEntries es := by
            exact (isStatic_tm hm hΓ hsm).entries
          have hes2 : IsStaticEntries es2 := by
            exact (isStatic_tm hm2 hΓ' hsm).entries
          have hesW := wfDTy_dist_inv (wf_tm hm hΓw)
          have hes2W := wfDTy_dist_inv (wf_tm hm2 hΓw')
          have hsc := det_eq_tm hm hm2 hctx hΓ hΓ' hΓw hΓw' hsm
          have hbody : ∀ j j', EqTy (es.get j).1 (es2.get j').1 →
              EqD (T j) (T2 j') := fun j j' hceq =>
            det_eq_tm (hF j) (hF2 j')
              (.cons hceq hctx)
              (ctxStatic_cons (isStaticEntries_get_ty hes j) hΓ)
              (ctxStatic_cons (isStaticEntries_get_ty hes2 j') hΓ')
              (ctxWf_cons (hesW.1 _ (List.get_mem es j)) hΓw)
              (ctxWf_cons (hes2W.1 _ (List.get_mem es2 j')) hΓw') hsn
          exact eqD_letRes (hsc.coup.mono hbody)
            (fun j => (hsc.cov.1 j).imp fun j' h => hbody j j' h)
            (fun j' => (hsc.cov.2 j').imp fun j h => hbody j j' h)
  | _, _, _, _, _, .choice hm hn, h2, hctx, hΓ, hΓ', hΓw, hΓw', hs => by
      cases h2 with
      | choice hm' hn' =>
        cases hs with
        | choice hp0 hp1 hsm hsn =>
          exact eqD_add (eqD_scale hp0 (det_eq_tm hm hm' hctx hΓ hΓ' hΓw hΓw' hsm))
            (eqD_scale (by linarith) (det_eq_tm hn hn' hctx hΓ hΓ' hΓw hΓw' hsn))
  | _, _, _, _, _, .ascT _ _ _, h2, hctx, hΓ, hΓ', hΓw, hΓw', hs => by
      cases h2 with
      | ascT _ _ _ =>
        cases hs with
        | ascT _ hsT => exact EqD.refl hsT
  | _, _, _, _, _, .ascV _ _ _, h2, hctx, hΓ, hΓ', hΓw, hΓw', hs => by
      cases h2 with
      | ascV _ _ _ =>
        cases hs with
        | ascV _ hsτ => exact eqD_singleton (EqTy.refl hsτ)
  | _, _, _, _, _, .add _ _ _ _, h2, hctx, hΓ, hΓ', hΓw, hΓw', hs => by
      cases h2 with
      | add _ _ _ _ => exact eqD_singleton EqTy.real
  | _, _, _, _, _, .ite _ _ hm hn _, h2, hctx, hΓ, hΓ', hΓw, hΓw', hs => by
      cases h2 with
      | ite _ _ hm' hn' _ =>
        cases hs with
        | ite _ hsm _ => exact det_eq_tm hm hm' hctx hΓ hΓ' hΓw hΓw' hsm
end


mutual
/-- Lemma 13 (well-formedness (equality)), item 1: equality preserves
well-formedness of simple types. -/
theorem wf_eq_ty : ∀ {τ1 τ2 : Ty}, τ1 =ₛ τ2 → WfTy τ1 → WfTy τ2
  | _, _, .real, _ => .real
  | _, _, .bool, _ => .bool
  | _, _, .arrow hs hd, hw => by
      cases hw with
      | arrow hws hwd => exact .arrow (wf_eq_ty hs hws) (wf_eq_d hd hwd)
/-- Lemma 13 (well-formedness (equality)), item 2, in a stronger form:
equality preserves well-formedness of distribution types.  Every entry of the
right-hand side is equal to some entry of the left-hand side (coverage), and the
coupling preserves the total probability. -/
theorem wf_eq_d : ∀ {T1 T2 : DTy}, T1 =ₛ T2 → WfDTy T1 → WfDTy T2
  | _, _, .dist (es1 := es1) (es2 := es2) _ fL fR _ hl hfL hfR, hwf => by
      cases hwf with
      | dist hes hsum =>
        refine .dist ?_ ?_
        · intro e he
          obtain ⟨j, hj⟩ := List.mem_iff_get.1 he
          have hwj := wf_eq_ty (hfR j) (hes _ (List.get_mem es1 (fR j)))
          rw [← hj]; exact hwj
        · show pmass es2 = 1
          obtain ⟨w, hw, -⟩ := hl
          rw [pmass_eq_sum, ← hw.sum_eq, ← pmass_eq_sum]
          exact hsum
end

/-- Lemma 13 (well-formedness (equality)), item 2, as stated in the article:
the probabilities of the right-hand side sum to `1` and every entry of positive
probability is well-formed.  A corollary of `wf_eq_d`. -/
theorem wf_eqD_entries {T1 : DTy} {es2 : List (Ty × GProb)}
    (h : EqD T1 (.dist es2)) (hw : WfDTy T1) :
    pmass es2 = 1 ∧ ∀ e ∈ es2, 0 < pval e.2 → WfTy e.1 := by
  cases wf_eq_d h hw with
  | dist hes hsum => exact ⟨hsum, fun e he _ => hes e he⟩

end GradualProb.SPLC
