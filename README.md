# The metatheory of *A Gradual Probabilistic Lambda Calculus*, in Lean 4

This is the machine-checked development behind the article "A Gradual
Probabilistic Lambda Calculus" (Matías Toro, Federico Olmedo and Wenjia Ye),
available at <https://arxiv.org/abs/2604.05246>, which extends the OOPSLA 2023
paper of the same title (<https://doi.org/10.1145/3586036>). Every
numbered lemma and theorem of the article, in the body and in the appendices
(Lemmas 1–67, Theorems 1–8), is proved here against the definitions of the
article. The tables below map each numbered definition, lemma and theorem of
the article body to the declarations that formalize it; in the article, a
footnote on each numbered element, in the body and in the appendices, names
its declarations.

* Toolchain `leanprover/lean4:v4.30.0`, Mathlib at tag `v4.30.0`.
* The main theorems depend only on `propext`,
  `Classical.choice` and `Quot.sound`.

## Build

The build needs `elan`, the Lean toolchain manager, which installs the Lean
version fixed in `lean-toolchain` and `lake`, the build tool. On macOS and
Linux:

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

(other platforms: <https://github.com/leanprover/elan>). Then, from this
directory:

```sh
lake exe cache get   # downloads Mathlib and its prebuilt files
lake build           # success is the proof check
```

`lake exe cache get` downloads Mathlib and its compiled files from the
Mathlib community server, about 7.6 GB of disk in all (about 10 minutes on a
fast connection); `lake build` then checks this
development, which takes about 3 minutes and 2.5 GB of memory on a six-core
desktop machine. If the prebuilt files of this Mathlib version are no longer on
the server, `lake build` still succeeds, compiling Mathlib from source, which
takes several hours.

Do not run `lake update`: it would move Mathlib to its latest version, while
`lake-manifest.json` fixes the exact commit of every dependency that this
development was checked against.

## Structure

The development has one directory per language, `SPLC/`, `GPLC/` and `TPLC/`,
each following its section of the article: definitions first (types, terms,
typing, semantics), then the metatheory, where most main theorems have a
module of their own. The shared module `Coupling` holds the couplings and
the lifting of relations on which type equality, consistency and precision
are built. The languages are linked in three places:

* SPLC is a fragment of GPLC: its types are the static types of `GPLC/Types`.
* The evidence of TPLC is built on the formula types of GPLC
  (`GPLC/FormulaTypes`), and `TPLC/Elaboration` translates GPLC into TPLC.
* `TPLC/DynamicConservativeExtension` relates TPLC back to SPLC.

Each module opens with a header that names the article elements it
formalizes.

## Correspondence with the article

Declarations are named without the `GradualProb.` prefix.

### Section 3: SPLC

| Article | Declarations | Module |
|---|---|---|
| Lemma 1, type well-formedness | `SPLC.wf_val`, `SPLC.wf_tm` | `SPLC/Typing` |
| Theorem 1, type safety for SPLC | `SPLC.type_safety` (from `SPLC.termination`, `SPLC.preservation`); reading in terms of probabilities, `SPLC.semantic_soundness` | `SPLC/TypeSafety` |

### Section 4: GPLC

| Article | Declarations | Module |
|---|---|---|
| Definition 1, type consistency, by AGT | `GPLC.AgtConsTy`, `GPLC.AgtConsD` | `GPLC/Concretization` |
| Definition 2, relation lifting | `IsCoupling` (condition 1), `Supp` (condition 2), `Lift` | `Coupling` |
| Lemma 2, alternative characterization of equality | `SPLC.eq_iff_coupling` (item 1 `SPLC.eqTy_iff_coupling`, item 2 `SPLC.eqD_iff_coupling`) | `SPLC/Equality` |
| Definition 3, coupling over symbolic distributions | `SymLift`; `SymLiftAll` for the form of Figure 8, universally quantified on the left | `Coupling` |
| Definition 4, type consistency, inductively | `GPLC.ConsTy`, `GPLC.ConsD` | `GPLC/FormulaTypes` |
| Lemma 3, equivalence of consistencies | `GPLC.agt_consistencyTy_iff`, `GPLC.agt_consistency_iff` | `GPLC/Concretization` |
| Definition 5, type and environment well-formedness | `GPLC.GoodTy`, `GPLC.GoodD`; environments `GPLC.CtxGood` | `GPLC/FormulaTypes`, `GPLC/Typing` |
| Lemma 4, type well-formedness | `GPLC.good_val`, `GPLC.good_tm` | `GPLC/Typing` |
| Definition 6, type precision | `GPLC.AgtPrecTy`, `GPLC.AgtPrecD`; the precision of Figure 8, sound for it by Lemma 5, is `GPLC.PrecTy`, `GPLC.PrecD` | `GPLC/Concretization`, `GPLC/FormulaTypes` |
| Lemma 5, soundness of type precision | `GPLC.precTy_to_agtPrecTy`, `GPLC.precD_to_agtPrecD` | `GPLC/Precision` |
| Theorem 2, static gradual guarantee for GPLC | `GPLC.static_gradual_guarantee` (open terms: `GPLC.static_gradual_guarantee_tm`, `GPLC.static_gradual_guarantee_val`) | `GPLC/Typing` |
| Definition 7, realization | `GPLC.RealizesTy`, `GPLC.RealizesD` | `GPLC/ConservativeExtension` |
| Theorem 3, conservative extension of the static semantics | `GPLC.static_conservative_extension` (`GPLC.static_conservative_extension_forward`, `GPLC.static_conservative_extension_backward`; values `GPLC.conservative_forward_val`, `GPLC.conservative_backward_val`) | `GPLC/ConservativeExtension` |

### Section 5: TPLC

| Article | Declarations | Module |
|---|---|---|
| Lemma 6, type well-formedness | `TPLC.wf_val`, `TPLC.wf_tm` | `TPLC/Definitions` |
| Definition 8, evidence | `TPLC.EEvTy`, `TPLC.EEvD` | `TPLC/Evidence` |
| Definition 9, valid evidence | `TPLC.HVTagTy`, `TPLC.TagD.HValidFor` | `TPLC/Evidence` |
| Lemma 7, valid evidence is evidence | `TPLC.valid_evidence_ty`, `TPLC.valid_evidence_d` | `TPLC/Evidence` |
| Lemma 8, reductivity of the meet operator | `TPLC.eprec_meetTy`, `TPLC.eprec_meetD` (both operands, picked by `π`); `TPLC.eprec_meetTy_glb`, `TPLC.eprec_meetD_glb`, `TPLC.consTy_of_common_lb`, `TPLC.consD_of_common_lb` | `TPLC/Meet` |
| Lemma 9, evidence from consistent transitivity | `TPLC.transTy_invariant`, `TPLC.transD_invariant` | `TPLC/Meet` |
| Definition 10, reordering | `TPLC.EReordTy`, `TPLC.EReordD` | `TPLC/Definitions` |
| Definition 11, reordering initial evidence | `TPLC.reorderTy`, `TPLC.reorderD`; the construction `W_f` shared with the meet, `TPLC.witness` | `TPLC/Definitions`, `TPLC/Witness` |
| Lemma 10, initial evidence for reordering | `TPLC.reord_reorderTy_isSome`, `TPLC.eprec_reorderTy` (both operands, picked by `π`); `TPLC.reorderD_sat_iff_ereordD`, `TPLC.eprec_reorderD`, `TPLC.goodD_reorderD` | `TPLC/Reorder` |
| Lemma 11, elaboration preserves types | `TPLC.elaboration_preserves_types` (`TPLC.elaboration_preserves_types_val`; `TPLC.elab_exists_tm`, `TPLC.elab_preserves_tm`) | `TPLC/Elaboration` |
| Theorem 4, type safety for GPLC | `GPLC.type_safety` (from `TPLC.elaboration_preserves_types_closed` and `TPLC.type_safety_converges_or_diverges`; case 1 is `TPLC.type_safety` with `TPLC.entriesIn_red`) | `TPLC/TypeSafety` |
| Lemma 12, monotonicity of evidence combination | `TPLC.meetTy_mono`, `TPLC.meetD_mono` | `TPLC/EvidencePrecision` |
| Theorem 5, dynamic gradual guarantee for TPLC | `TPLC.dynamic_gradual_guarantee` | `TPLC/GradualGuarantee` |
| Theorem 6, dynamic gradual guarantee for GPLC | `GPLC.dynamic_gradual_guarantee` (via `TPLC.elab_canon_tm`) | `TPLC/SourceGradualGuarantee` |
| Theorem 7, dynamic conservative extension of TPLC with respect to SPLC | `TPLC.dynamic_conservative_extension` (`TPLC.dynamic_conservative_extension_obs`) | `TPLC/DynamicConservativeExtension` |

## Representation Decisions

The development formalizes the definitions of the article, but represents some
of them differently (formulas as sets of solutions, de Bruijn indices, SPLC
as a fragment of GPLC, and others). The main encodings are listed in
[`REPDECISIONS.md`](REPDECISIONS.md). Each one is also explained in a comment
next to the definition it affects.

## Naming

Each language has its namespace: `GradualProb.SPLC` (the static language,
Section 3), `GradualProb.GPLC` (the gradual source language, Section 4) and
`GradualProb.TPLC` (the target language, Section 5). The types shared by the
three (`Ty`, `DTy`, gradual probabilities, the concretization) and the
coupling toolkit live in `GradualProb`. The same notion has the same short
name in every language: `SPLC.HasTyT`, `GPLC.HasTyT` and `TPLC.HasTyT` are
the typing judgments of terms. Formula types are `FTy`/`FDist`; relations on
runtime evidence carry the prefix `E` (`EConsD`, `EPrecD`, `EReordD`,
`EEvD`). Throughout this README, names are given without the `GradualProb.`
prefix.

Names follow the conventions of Mathlib. Types, relations and predicates are
in `UpperCamelCase` (`PrecD`, `HValid`, `Tm.FvBelow`), functions and other
data in `lowerCamelCase` (`meetD`, `reorderD`, `pushfwd`), and theorems in
`snake_case`, where a definition that the statement mentions appears in
`lowerCamelCase` (`eprecD_of_precD`, `hvalidFor_tagReorderD`). The structural
properties of a relation live in its namespace (`EqD.refl`, `EqD.symm`,
`PrecD.trans`). The versions of a notion for simple and for distribution types
end in `Ty` and `D` (`meetTy`/`meetD`, `reorderTy`/`reorderD`,
`ConcrTy`/`ConcrD`), and the meet and the reordering, instances of one
construction, name their lemmas in parallel (`eprec_meetD_glb` and
`eprec_reorderD_glb`, `meetD_sat_iff_econsD` and `reorderD_sat_iff_ereordD`).
Two exceptions keep the article's notation: the fields `C` (the formula of a
distribution type) and `V` (the value of a typed distribution) keep their
capital inside theorem names (`meetD_C_iff`), and the constants of Example 6
are named after its types (`sA`, `P1`, `E1`). The natural number that indexes
a big-step reduction is its derivation index (`red_index_mono`).

## Notation

The relations and judgments that the article writes with a symbol have the
same symbol in Lean, as a `scoped` notation of the namespace of their
language: it is active inside that namespace and wherever the namespace is
opened (`open GradualProb.GPLC`). Each notation is declared next to its
definition, with a docstring that names the figure or definition of the
article. The statements of the cited results use them, and the goals print
with them.

| Article | Lean notation | Declarations |
|---|---|---|
| `Γ ⊢ₛ v : τ`, `Γ ⊢ₛ m : T` | `Γ ⊢ₛ v : τ`, `Γ ⊢ₛ m : T`, closed `⊢ₛ m : T` | `SPLC.HasTyV`, `SPLC.HasTyT` |
| `τ =ₛ τ'` | `τ =ₛ τ'` | `SPLC.EqTy`, `SPLC.EqD` |
| `m ⇓ₛ 𝒱` | `m ⇓ₛ[k] V` | `SPLC.Red` |
| `Γ ⊢ v : σ`, `Γ ⊢ m : μ` | `Γ ⊢ v : σ`, `Γ ⊢ m : D`, closed `⊢ m : D` | `GPLC.HasTyV`, `GPLC.HasTyT`; `TPLC.HasTyRaw`, `TPLC.HasTyV`, `TPLC.HasTyT` |
| `σ ∼ δ` (Definitions 1 and 4) | `σ ∼ δ`; by AGT `σ ∼ᴬᴳᵀ δ` | `GPLC.ConsTy`, `GPLC.ConsD`; `GPLC.AgtConsTy`, `GPLC.AgtConsD` |
| `σ ⊑ δ`, `σ ⊑_AGT δ` | `σ ⊑ δ`, `σ ⊑ᴬᴳᵀ δ` | `GPLC.PrecTy`, `GPLC.PrecD`; `GPLC.AgtPrecTy`, `GPLC.AgtPrecD` |
| `ρ ⊑ ρ'`, `Γ ⊑ Γ'`, `m ⊑ n` (GPLC) | `ρ ⊑ ρ'`, `Γ ⊑ Γ'`, `m ⊑ n` | `GPLC.PrecP`, `GPLC.PrecCtx`, `GPLC.PrecV`, `GPLC.PrecT` |
| `σ ∼̇ δ`, `σ ⊑̇ δ` (Figure 12) | `σ ∼̇ δ`, `σ ⊑̇ δ` | `GPLC.EConsTy`, `GPLC.EConsD`, `GPLC.EPrecTy`, `GPLC.EPrecD` |
| `⌈σ⌉` | `⌈σ⌉` | `GPLC.liftFTy`, `GPLC.liftFDist` |
| `σ ⇝ τ` (Definition 7), `σ ⇝ʷ τ` (Definition 15) | `σ ⇝ τ`, `σ ⇝ʷ τ` | `GPLC.RealizesTy`, `GPLC.RealizesD`; `TPLC.WeakRealizesTy`, `TPLC.WeakRealizesD` |
| `ε ⊢ σ ∼̇ δ` (Definition 8) | `ε ⊢ σ ∼̇ δ` | `TPLC.EEvTy`, `TPLC.EEvD` |
| `ε ⊩ σ ∼̇ δ`, `ε ⊩_ℓ σ` (Definition 9) | `ε ⊩ σ ∼̇ δ`, `ε ⊩[.l] σ` | `TPLC.HVTagTy`, `TPLC.TagD.HValidFor`; `TPLC.HVTag`, `TPLC.HValid` |
| `σ ⊓ δ` | `σ ⊓ δ`; tagged `σ ⊓ᵗ δ` | `TPLC.meetTy`, `TPLC.meetD`; `TPLC.tagMeetTy`, `TPLC.tagMeetD` |
| `ε₁ ∘ ε₂` | `ε₁ ∘ ε₂` | `TPLC.emeetTy`, `TPLC.emeetD` |
| `μ =ʳ ν` (`=` with `r` above, Definition 10) | `μ =ʳ ν` | `TPLC.EReordTy`, `TPLC.EReordD` |
| `μ ∥ ν` (`=` turned upright, Definition 11) | `μ ∥ ν`; tagged `μ ∥ᵗ ν` | `TPLC.reorderTy`, `TPLC.reorderD`; `TPLC.tagReorderTy`, `TPLC.tagReorderD` |
| `m ⇓ₖ Φ ▷ 𝒱` | `m ⇓[k] V` | `TPLC.Red` |
| `Γ ⊑ Γ' ⊢ m ⊑ m'`, closed `m ⊑ m'` (Figure 17) | `Γ ⊑ Γ' ⊢ m ⊑ m'`, `m ⊑ m'` | `TPLC.PrecRaw`, `TPLC.PrecV`, `TPLC.PrecT` |
| `Φ ▷ 𝒱 ⊑ Φ' ▷ 𝒱'` | `V ⊑ V'` | `TPLC.DConfPrec` |
| `σ ⊑ δ ⊢_π ε ⊑̇ ε'` (Figure 18) | `σ ⊑ δ ⊢[π] ε ⊑̇ ε'` | `TPLC.TagPrecTy`, `TPLC.TagPrecD` |
| `Γ ⊢ m : μ ⇝ m'` (Figure 16) | `Γ ⊢ m : D ⇝ tm`, closed `⊢ m : D ⇝ tm` | `TPLC.ElabV`, `TPLC.ElabT` |
| `Γ ⊢_⇝ m : μ` (Definition 16) | `Γ ⊢⇝ m : D`, closed `⊢⇝ m : D` | `TPLC.SRRaw`, `TPLC.SRV`, `TPLC.SRT` |

A symbol is shared by several declarations when the types of the arguments
tell them apart (`⊑` on types, contexts, probabilities, terms and
configurations; `⊢` for GPLC and TPLC). Where they do not, Lean adds a mark
that the article does not need: `ᴬᴳᵀ` for the declarative relations of
Definitions 1 and 6, and `ᵗ` for the meet and the reordering initial evidence
as tagged evidences, which take the same arguments as their untagged
versions. The dotted `⊑̇` and `∼̇` are `⊑` and `∼` followed by the combining dot
above (U+0307). Three glyphs differ from the article: `∥` (U+2225) for the
upright `=`, which Mathlib's norm `‖·‖` leaves free; `=ʳ` for the `=` with an
`r` above; `⊢[π]` and `⊩[.l]` for the subscripts. `⊓`, `∘` and `⌈·⌉` are
shared with Mathlib's infimum, function composition and ceiling, and the
type of the operands picks the reading. An overloaded statement must give
the type of a variable that only the notation determines (`∀ {Γ} {m : Tm}
{D}, Γ ⊢ m : D → …`). Well-formedness, written `⊢ σ` in the article, has no
notation: `⊢` before a type would read as the goal marker in the infoview.

## License

Apache License 2.0; see `LICENSE`.
