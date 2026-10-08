import GradualProb.GPLC.Types

/-!
# Well-formedness of annotations

Well-formedness of source gradual types, the language of annotations
(Definition 14): simple types are well-formed when their components are, and a
distribution type is well-formed when its entries are and its probabilities are
plausible, that is, some choice of concretizations `pᵢ ∈ γ_p(ρᵢ)` sums to `1`
(`Plausible`). Well-formedness of formula types (Definition 5) is `GoodTy`/`GoodD`
in `GPLC/FormulaTypes`; Lemma 21 (lifting well-formedness), which connects the
two, is `goodTy_liftF`/`goodD_liftFD` in `GPLC/Typing`.
-/

namespace GradualProb.GPLC

open scoped BigOperators

/-- Plausibility of the probabilities of a distribution annotation: some choice
of concretizations `pᵢ ∈ γ_p(ρᵢ)` has total `1`. `List.Forall₂` matches the
witness list to the entries pointwise. -/
def Plausible (es : List (Ty × GProb)) : Prop :=
  ∃ ps : List ℝ, List.Forall₂ GammaP (es.map Prod.snd) ps ∧ ps.sum = 1

/- Definition 14 (well-formedness of source annotations). `WfEntries` names the
condition on the entries of a distribution type. -/
mutual
/-- Definition 14 (well-formedness of source annotations), simple types:
well-formed source gradual simple types. -/
inductive WfTy : Ty → Prop where
  | real : WfTy .real
  | bool : WfTy .bool
  | unk  : WfTy .unk
  | arrow : ∀ {s d}, WfTy s → WfDTy d → WfTy (.arrow s d)
/-- Definition 14 (well-formedness of source annotations), distribution types:
well-formed source gradual distribution types, whose entries are well-formed
and whose probabilities are `Plausible`. -/
inductive WfDTy : DTy → Prop where
  | dist : ∀ {es : List (Ty × GProb)}, (∀ e ∈ es, WfTy e.1) → Plausible es →
             WfDTy (.dist es)
end

/-- Entry lists whose simple types are well-formed. -/
abbrev WfEntries (es : List (Ty × GProb)) : Prop := ∀ e ∈ es, WfTy e.1


end GradualProb.GPLC
