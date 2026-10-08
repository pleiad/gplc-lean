import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-!
# Gradual types

The syntax of types shared by the three languages (Figure 4): gradual
probabilities, gradual simple types and gradual distribution types, with the
unknown simple type and the unknown probability `?`. Static types (SPLC,
Section 3) are the gradual types with no `?` (`IsStaticTy`, `IsStaticDTy`).
The module also defines the concretization `γ_p` of gradual probabilities and a
splitting concretization of gradual annotation types (`ConcrTy`, `ConcrD`).

## Reading guide

The type system of GPLC works with formula types (`FTy`, `FDist` in
`GPLC/FormulaTypes`), not with these annotation types, and the concretization
of Section 4 that defines consistency and precision is the one on formula types
(`FConcrTy`, `FConcrD` in `GPLC/Concretization`). `ConcrTy`/`ConcrD` here are
its counterpart on annotations; `gammaT_split_example` checks the splitting
example of Section 4.
-/

namespace GradualProb

open scoped BigOperators
open Classical


/-- Gradual probabilities: a known real `r`, or the unknown probability `?`.
Probabilities are reals: the grammar's restriction to `[0,1]` is not part of the
type but a predicate imposed where needed (by `GammaP`, by the staticness
predicate `IsStaticEntries`, and by the hypotheses of the statements). -/
inductive GProb where
  | q   : ℝ → GProb        -- a known probability `r`
  | unk : GProb            -- the unknown probability `?`

/-- Concretization `γ_p` of a gradual probability, as a predicate:
`γ_p(r) = {r}` (for `r ∈ [0,1]`) and `γ_p(?) = [0,1]`. -/
def GammaP : GProb → ℝ → Prop
  | .q r,  x => x = r ∧ 0 ≤ r ∧ r ≤ 1
  | .unk,  x => 0 ≤ x ∧ x ≤ 1

/-- Every concretization of a gradual probability lies in `[0,1]`. -/
theorem gammaP_mem_unit : ∀ {g : GProb} {x : ℝ}, GammaP g x → 0 ≤ x ∧ x ≤ 1
  | .q r, x, ⟨hx, h0, h1⟩ => hx ▸ ⟨h0, h1⟩
  | .unk, x, h => h

/-- Numeric value of a known probability; `0` for the unknown one. -/
def pval : GProb → ℝ
  | .q r => r
  | .unk => 0

/- Gradual simple types `Ty` and gradual distribution types `DTy`, mutually
defined (Figure 4). The same datatype holds the static types of SPLC, carved out
by `IsStaticTy`/`IsStaticDTy` below. A distribution type `{{τ_i^{p_i}}}_{i∈I}`,
a multiset in the article, is a list of entries: the index set `I` becomes the
positions `Fin n` of the list. Statements that must not depend on the order of
entries are stated up to an equality relation or a coupling, never by list
equality. -/
mutual
/-- Gradual simple types. -/
inductive Ty where
  | real  : Ty
  | bool  : Ty
  | unk   : Ty                       -- the unknown simple type `?`
  | arrow : Ty → DTy → Ty
/-- Gradual distribution types. -/
inductive DTy where
  | dist : List (Ty × GProb) → DTy   -- `{{ τ_i ^ p_i }}_{i}` as a list of entries
end

/- Static types: no `?` anywhere and only known probabilities, each in `[0,1]`
as the grammar of static types requires. A distribution type is static when
the simple type of every entry is static and every probability is a known one
in `[0,1]`; `IsStaticEntries` bundles the two conditions entry by entry. -/
mutual
/-- Static simple types. -/
inductive IsStaticTy : Ty → Prop where
  | real  : IsStaticTy .real
  | bool  : IsStaticTy .bool
  | arrow : ∀ {s d}, IsStaticTy s → IsStaticDTy d → IsStaticTy (.arrow s d)
/-- Static distribution types. -/
inductive IsStaticDTy : DTy → Prop where
  | dist  : ∀ {es : List (Ty × GProb)}, (∀ e ∈ es, IsStaticTy e.1) →
              (∀ e ∈ es, ∃ r, e.2 = GProb.q r ∧ 0 ≤ r ∧ r ≤ 1) →
              IsStaticDTy (.dist es)
end

/-- Entry lists of static distribution types: every simple type is static and
every probability is a known one in `[0,1]`. -/
abbrev IsStaticEntries (es : List (Ty × GProb)) : Prop :=
  ∀ e ∈ es, IsStaticTy e.1 ∧ ∃ r, e.2 = GProb.q r ∧ 0 ≤ r ∧ r ≤ 1

/-- A distribution type with static entries is static. -/
theorem IsStaticDTy.ofEntries {es : List (Ty × GProb)} (h : IsStaticEntries es) :
    IsStaticDTy (.dist es) :=
  .dist (fun e he => (h e he).1) (fun e he => (h e he).2)

/-- The Dirac type on a static simple type is static. -/
theorem IsStaticDTy.point {τ : Ty} (h : IsStaticTy τ) : IsStaticDTy (.dist [(τ, .q 1)]) :=
  .ofEntries fun _ he => by
    obtain rfl := List.mem_singleton.1 he
    exact ⟨h, 1, rfl, zero_le_one, le_refl 1⟩

/-- The entries of a static distribution type are static. -/
theorem IsStaticDTy.entries {es : List (Ty × GProb)} (h : IsStaticDTy (.dist es)) :
    IsStaticEntries es := by
  cases h with | dist h1 h2 => exact fun e he => ⟨h1 e he, h2 e he⟩

/- Splitting concretization of gradual annotation types, as inductive relations:
`ConcrTy σ τ` means `τ ∈ γ_τ(σ)` and `ConcrD G S` means `S ∈ γ_T(G)`, with
`τ` and `S` static. A static distribution type concretizes `G` when a map `f`
assigns each static entry to the gradual entry it splits from, every static
simple type concretizes the simple type of its gradual entry, the
probabilities of the block over each gradual entry `i` sum to a value in `γ_p`
of its probability, and every block is non-empty (`f` is surjective), so that
an entry of probability zero still has a witness. This is the annotation-level
counterpart of `FConcrTy`/`FConcrD`, the concretization of formula types of
Section 4. -/
mutual
/-- `ConcrTy σ τ`: the static simple type `τ` is in `γ(σ)`. -/
inductive ConcrTy : Ty → Ty → Prop where
  | real : ConcrTy .real .real
  | bool : ConcrTy .bool .bool
  | unk  : ∀ {t}, IsStaticTy t → ConcrTy .unk t
  | arrow : ∀ {s d t e}, ConcrTy s t → ConcrD d e → ConcrTy (.arrow s d) (.arrow t e)
/-- `ConcrD G S`: the static distribution type `S` is in `γ(G)`. -/
inductive ConcrD : DTy → DTy → Prop where
  | dist : ∀ {G : List (Ty × GProb)} {S : List (Ty × ℝ)} {f : Fin S.length → Fin G.length},
      (∀ k, ConcrTy (G.get (f k)).1 (S.get k).1) →
      (∀ i, GammaP (G.get i).2 (∑ k ∈ Finset.univ.filter (fun k => f k = i), (S.get k).2)) →
      (∀ k, 0 ≤ (S.get k).2) →
      -- non-empty blocks: every gradual entry has at least one static
      -- representative, possibly of probability 0
      (∀ i, ∃ k, f k = i) →
      ConcrD (.dist G) (.dist (S.map (fun e => (e.1, GProb.q e.2))))
end


/- The lifting `⌈·⌉` of annotations to formula types is `liftFTy`/`liftFDist`
in `GPLC/Typing`. -/


/-! ## Splitting examples

A single gradual entry can stand for several distinct static outcomes: both
static entries below are assigned to the single gradual entry, and their
probabilities sum to `1`. -/


/-- `{{Real^½, Bool^½}} ∈ γ_T({{?^ρ}})` whenever `1 ∈ γ_P(ρ)`: the probability
of the single entry splits as `½ + ½` across two distinct types. -/
theorem gammaT_split {p : GProb} (hp : GammaP p 1) :
    ConcrD (.dist [(.unk, p)]) (.dist [(.real, .q (1/2)), (.bool, .q (1/2))]) := by
  have h : ConcrD (.dist [(.unk, p)])
      (.dist (([(.real, (1:ℝ)/2), (.bool, (1:ℝ)/2)]).map (fun e => (e.1, GProb.q e.2)))) := by
    refine ConcrD.dist (S := [(.real, (1:ℝ)/2), (.bool, (1:ℝ)/2)]) (f := fun _ => 0)
      ?_ ?_ ?_ (fun i => ⟨0, by fin_cases i; rfl⟩)
    · intro k; fin_cases k
      · exact ConcrTy.unk IsStaticTy.real
      · exact ConcrTy.unk IsStaticTy.bool
    · intro i; fin_cases i
      simp only [Finset.sum_filter, Fin.sum_univ_two]
      convert hp using 1
      norm_num
    · intro k; fin_cases k <;> norm_num
  simpa using h

/-- `{{Real^½, Bool^½}} ∈ γ_T({{?^?}})`, the splitting example of Section 4. -/
theorem gammaT_split_example :
    ConcrD (.dist [(.unk, .unk)]) (.dist [(.real, .q (1/2)), (.bool, .q (1/2))]) :=
  gammaT_split (by norm_num [GammaP])

/-- `{{Real^½, Bool^½}} ∈ γ_T({{?^1}})`. -/
theorem gammaT_split_one_example :
    ConcrD (.dist [(.unk, .q 1)]) (.dist [(.real, .q (1/2)), (.bool, .q (1/2))]) :=
  gammaT_split (by norm_num [GammaP])
/-- The simple type of each entry of a static entry list, at an index. -/
theorem isStaticEntries_get_ty {es : List (Ty × GProb)} (h : IsStaticEntries es)
    (i : Fin es.length) : IsStaticTy (es.get i).1 :=
  (h _ (List.get_mem es i)).1

end GradualProb
