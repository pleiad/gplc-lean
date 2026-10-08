# Representation decisions

The development formalizes the definitions of the article, but represents some
of them differently. The main differences are listed below; each one is also
explained in a comment next to the definition it affects. Names are given
without the `GradualProb.` prefix.

**Formulas as sets of solutions.** A formula distribution type (`FDist`) is
represented by a finite family of entries together with a predicate on their
probabilities, `C : (Fin n → ℝ) → Prop`, namely the set of solutions of its
formula. Consequently, the grammar of formulas, tagged variables and
freshness have no counterpart, and conjunction, the marginal equations of the
meet and the guarded implication of the `let` rule are operations on sets of
solutions. In the formula of the witness construction `W_f` (the meet and the
reordering initial evidence, `TPLC.witness`), the probability variables of the
operands, which the article leaves free, are existentially quantified.
Likewise, the fresh variables that rules (G⊕) and (D⊕) of TPLC introduce for
the probability of a choice are an existential quantification over that
probability, separate for each application of the rule.

**Witnesses as functions.** In the definitions of equality, consistency and
precision (`SPLC.EqD`, `GPLC.ConsD`, `GPLC.PrecD`), each existential
quantifier nested under a universal one is replaced by an explicit witness
function, its Skolem form. The relation that the distribution rule of each
of these definitions lifts (Definitions 2 and 3: `Lift`, `SymLift`,
`SymLiftAll`) is also an explicit witness, a relation on the entries of the
two types that is contained in the relation being defined, because an
inductive definition cannot refer to itself inside the lifting. Since the
lifting is monotone in the relation, the rule relates the same types;
`SPLC.EqD.intro`/`SPLC.EqD.coup`, `GPLC.ConsD.intro`/`GPLC.ConsD.coup` and
`GPLC.PrecD.intro`/`GPLC.PrecD.coup` state it on the relation itself.
The distribution rule of tag-aware precision (`TPLC.TagPrecD`, Figure 18)
has the same form.

**Variables and environments.** Variables are de Bruijn indices, and typing
environments are lists indexed by position.

**SPLC as a fragment of GPLC.** The types of SPLC are represented as the
gradual types (`Ty`, `DTy`) that contain no unknown type and no unknown
probability (`IsStaticTy`, `IsStaticDTy`). The terms of SPLC (`SPLC.Tm`,
`SPLC.Val`) carry annotations of that universe, restricted to static ones by
`SPLC.IsStaticTm` and `SPLC.IsStaticVal`, and embed into the terms of GPLC by
`GPLC.embedT` and `GPLC.embedV`.

**Equality of static types.** The rules and statements that use the equality
`=ₛ` of Section 3 use the coupling equality (`SPLC.EqTy`, `SPLC.EqD`) in its
place. The distribution rule of `=ₛ` refers to `=ₛ` inside the probability of
a class, so it is not an inductive definition; by Lemma 2
(`SPLC.eq_iff_coupling`), its rules define exactly the coupling equality
(`SPLC.eq_satisfies_rules`, `SPLC.eqRules_unique`).

**Typed precision of TPLC.** The judgment `Γ ⊑ Γ' ⊢ m ⊑ m'` of the article is
`TPLC.PrecT Γ Γ' m m'`, defined for arbitrary environments `Γ` and `Γ'`;
`Γ ⊑ Γ'` is a hypothesis of the results that require it. The premises of the
ascription rules and of the `let` rule that refer to the type of a subterm
are required for every type of that subterm; since typing in TPLC is deterministic, they coincide
with the premises of the article on well-typed terms.

**Derivation index.** The big-step reduction relations (`SPLC.Red`,
`TPLC.Red`) are indexed by the height of their derivation, a natural number
used for induction; the results quantify over this index without
constraining it.

**Type of a configuration.** The type of a configuration (`TPLC.DConf`) is
not a premise of its typing judgment; it is computed from its formula and
from the types of its values (`TPLC.DConf.confF`).

**Families of `let` bodies.** The bodies of a `let` of TPLC are a function
`Fin n → Tm` from the entries of the type of the bound term, and the length
`n` is part of the term (`TPLC.Tm.letin`). The rules that type, reduce
or elaborate a `let` (`TPLC.HasTyT`, `TPLC.Red`, `TPLC.ElabT`) take
`n` as a variable and write the type of the bound term with its components,
`⟨n, ty, C⟩`, as the article's rules name its entries; the condition that
the family has one body per entry is thereby the index of the term rather
than a premise.

**Tags of the routing evidences.** The tags of a tagged evidence
(`TPLC.TagD`) are natural numbers, as in the article, and validity
(Definition 9, `TPLC.HValid`) checks that they name entries of the judged
types. The routing evidences that rules (Dlet) and (D::μ) compute are
instances of the witness construction `W_f` (`TPLC/Witness`), whose cells
are pairs of operand entries; the rules (`TPLC.Red`) name the value and the
target entry of a cell through the projections of that pair
(`TPLC.reorderDL`, `TPLC.reorderDR`, `TPLC.meetDL`) rather than through the
tags. Only the right tag of a cell of `(μ′ ∥ μ) ∘ ξ` comes from the evidence
`ξ` written in the term; that it names an entry of the target type follows
from the premise of rule (D::μ) that `ξ` is valid (`TPLC.TagD.HValidFor`).
