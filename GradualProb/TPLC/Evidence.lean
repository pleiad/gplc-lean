import GradualProb.GPLC.FormulaTypes

/-!
# Evidence, tagged evidence and its validity

This module formalizes the evidences of TPLC (Section 5.2 of the article):
evidence for a consistency judgment (Definition 8), the tagged evidences that
TPLC terms carry, valid evidence (Definition 9) and Lemma 7 (valid evidence is
evidence). It also defines the tag-aware precision between evidences
(Figure 18), which the term precision of TPLC (Figure 17) uses in its
ascription rules.

## Main results

* `valid_evidence_ty`, `valid_evidence_d`: Lemma 7 (valid evidence is
  evidence). The steps are `hvtag_toVTy` with `vtag_evTy`, and
  `TagD.HValidFor.toV` with `validFor_evD`; the core is `eprecD_of_tagPrec`.
* `TagPrecTy.flip`, `TagPrecD.flip`: flipping the tags exchanges the two
  judgments `⊢[.l]` and `⊢[.r]` of tag-aware precision (what rule (Dapp) needs).
* `TagPrecTy.refl`, `TagPrecD.refl`: reflexivity of tag-aware precision on
  valid evidences.

## Reading guide

The module goes in this order: evidence on formula types (`EEvTy`, `EEvD`);
the tag-guided precision `TagPrec` behind validity; the syntax of tagged
evidence (`TagTy`, `TagD`), the pointer `π ∈ {l, r}` (`Side`) that selects
one of its two tags (`TagD.tag`), its erasure `toF`, the flip of the tags and
the diagonal embedding `FTy.toTag`; the tag-aware precision of Figure 18
(`TagPrecTy π`, `TagPrecD π`); the shallow validity (`TagD.Valid π`,
`VTag π`), an intermediate step of Lemma 7; and the hereditary validity of
Definition 9 (`HVTag π`, `HValid π`, `HVTagTy`, `TagD.HValidFor`). The
judgments of Figure 18 and the two validities of Definition 9 are stated once
for the pointer `π`, as in the article. -/


namespace GradualProb.TPLC

open GradualProb.GPLC

/-! ## Evidence for consistency judgments

An evidence `ε` justifies a consistency judgment `σ ∼̇ σ'` when it is at least
as precise as both `σ` and `σ'`. Definition 8 uses the runtime precision of
Figure 12 (`EPrecTy`/`EPrecD`, no coverage clauses); it is `EEvTy`/`EEvD` below. -/


/-- Definition 8 (evidence), item 1: `ε ⊢ σ ∼̇ σ'` iff `ε` is below both `σ`
and `σ'` in the runtime precision `⊑̇`. -/
def EEvTy (ε σ σ' : FTy) : Prop := ε ⊑̇ σ ∧ ε ⊑̇ σ'

/-- Definition 8 (evidence), item 2: `ε ⊢ D ∼̇ D'` iff `ε` is below both `D`
and `D'` in the runtime precision `⊑̇`. -/
def EEvD (ε D D' : FDist) : Prop := ε ⊑̇ D ∧ ε ⊑̇ D'

/-- `ε ⊢ σ ∼̇ σ'`, the evidence `ε` justifies the runtime consistency of `σ`
and `σ'` (Definition 8). -/
scoped notation:50 (name := eEvTyStx) ε:51 " ⊢ " σ:51 " ∼̇ " σ':51 => EEvTy ε σ σ'
/-- `ε ⊢ D ∼̇ D'`, the evidence `ε` justifies the runtime consistency of `D`
and `D'` (Definition 8). -/
scoped notation:50 (name := eEvDStx) ε:51 " ⊢ " D:51 " ∼̇ " D':51 => EEvD ε D D'

/-- An evidence for `σ ∼̇ σ'` is below `σ`. -/
theorem EEvTy.left {ε σ σ' : FTy} (h : EEvTy ε σ σ') : EPrecTy ε σ := h.1
/-- An evidence for `σ ∼̇ σ'` is below `σ'`. -/
theorem EEvTy.right {ε σ σ' : FTy} (h : EEvTy ε σ σ') : EPrecTy ε σ' := h.2
/-- An evidence for `D ∼̇ D'` is below `D`. -/
theorem EEvD.left {ε D D' : FDist} (h : EEvD ε D D') : EPrecD ε D := h.1
/-- An evidence for `D ∼̇ D'` is below `D'`. -/
theorem EEvD.right {ε D D' : FDist} (h : EEvD ε D D') : EPrecD ε D' := h.2

/-! ## Tag-guided precision -/

/-- Tag-guided precision of `ε` into `D` along the map `l` from the cells of
`ε` to the entries of `D`: each cell is below the entry it is sent to
(`EPrecTy`), and the push-forward along `l` (`pushfwd`) of every solution of
`ε` is a solution of `D`. This is the distribution clause of validity (Definition 9)
without the hereditary validity of the cells. -/
structure TagPrec (ε : FDist) (D : FDist) (l : Fin ε.n → Fin D.n) : Prop where
  cell : ∀ k, EPrecTy (ε.ty k) (D.ty (l k))
  push : ∀ w, ε.C w → D.C (pushfwd l w)

/-- Tag-guided precision implies the runtime precision `EPrecD` when the
solutions of `ε` are nonnegative: every solution is related to its
push-forward along `l` (`Lift.pushfwd`). The core of Lemma 7. -/
theorem eprecD_of_tagPrec {ε D : FDist} {l : Fin ε.n → Fin D.n}
    (h : TagPrec ε D l) (hnn : ∀ w, ε.C w → ∀ k, 0 ≤ w k) : EPrecD ε D :=
  .intro fun w hw => ⟨_, h.push w hw, .pushfwd l (hnn w hw) h.cell⟩

/-- Tag-guided precision composes (push-forward of push-forward, `EPrecTy`
transitivity on the cells). -/
theorem TagPrec.comp {ε1 ε2 D : FDist} {f : Fin ε1.n → Fin ε2.n}
    {g : Fin ε2.n → Fin D.n} (h1 : TagPrec ε1 ε2 f) (h2 : TagPrec ε2 D g) :
    TagPrec ε1 D (fun k => g (f k)) := by
  refine ⟨fun k => EPrecTy.trans (h1.cell k) (h2.cell (f k)), fun w hw => ?_⟩
  rw [← pushfwd_comp]
  exact h2.push _ (h1.push w hw)

/-- Transports tag-guided precision along an equality of the evidence type. -/
theorem tagPrec_of_eq {ε ε' D : FDist} (h : ε' = ε)
    {l : Fin ε.n → Fin D.n} (ht : TagPrec ε D l) :
    TagPrec ε' D (fun c => l (Fin.cast (congrArg FDist.n h) c)) := by
  subst h
  exact ht

/-! ## The tagged-evidence syntax -/

mutual
/-- Tagged simple evidence: a formula simple type whose distribution nodes
carry tags (mirror of `FTy`). -/
inductive TagTy : Type where
  | real : TagTy
  | bool : TagTy
  | unk  : TagTy
  | arrow : TagTy → TagD → TagTy
/-- Tagged distribution evidence: `n` entries, the closing formula (as its set
of solutions, as in `FDist`), and two tag maps `l` and `r`.

In the article a tag is a component `ω = ⟨α, l, r⟩` of each probability
variable, pointing at the entries of the left and right judged types that the
cell connects. Here the tags are two maps from the cells to entry indices,
with values in `ℕ`; that they are in range for a given judged type is part of
validity (`HValid`). The evidences that the reduction rules compute
(`tagReorderD`, `emeetD`) are instances of the witness construction of
`TPLC/Witness`, whose cells are pairs of operand entries; the rules name the
outcome and the target entry of a cell through the projections of the cell
(`reorderDL`, `reorderDR`, `meetDL`), which are indices by construction, except
the target entry of rule (D::μ), which is the right tag of the cell, in range
by the validity premise of the rule.

As `FDist`, it is a `structure` whose operators are written with projections
(see the note at `FDist`); it does not extend `FDist`, since its entries are
tagged evidences and not formula types. -/
structure TagD : Type where
  /-- Number of cells. -/
  n : ℕ
  /-- Entries (cell evidences). -/
  ty : Fin n → TagTy
  /-- Closing formula, as a solution set. -/
  C : (Fin n → ℝ) → Prop
  /-- Left tags: the entry of the left judged type each cell points at. -/
  l : Fin n → ℕ
  /-- Right tags: the entry of the right judged type each cell points at. -/
  r : Fin n → ℕ
end

/-! ## The two tags

Tag-aware precision (Figure 18) and validity (Definition 9) are stated once for
a pointer `π ∈ {l, r}` that stands for either tag. -/

/-- The pointer `π ∈ {l, r}`: one of the two tags of a tagged variable, and
with it one of the two judged sides. -/
inductive Side : Type where
  | l : Side
  | r : Side
  deriving DecidableEq

/-- The other pointer. -/
def Side.swap : Side → Side
  | .l => .r
  | .r => .l

/-- The `π` component of a pair: the first for `l`, the second for `r`. -/
def Side.pick {α : Sort _} : Side → α → α → α
  | .l, a, _ => a
  | .r, _, b => b

/-- The `π` component of a pair of equal components. -/
@[simp] theorem Side.pick_self {α : Sort _} (π : Side) (a : α) : π.pick a a = a := by
  cases π <;> rfl

/-- Picking commutes with a binary constructor. -/
theorem Side.pick_app {α β γ : Sort _} (π : Side) (f : α → β → γ) (a a' : α) (b b' : β) :
    π.pick (f a b) (f a' b') = f (π.pick a a') (π.pick b b') := by
  cases π <;> rfl

/-- A property of both components holds of the `π` component. -/
theorem Side.pick_prop {α : Sort _} (P : α → Prop) (π : Side) {a b : α} (ha : P a) (hb : P b) :
    P (π.pick a b) := by
  cases π
  · exact ha
  · exact hb

/-- The tag map `π` of a tagged distribution evidence. -/
def TagD.tag (e : TagD) : Side → Fin e.n → ℕ
  | .l => e.l
  | .r => e.r

/-- The tag map `l` is the left tags. -/
@[simp] theorem TagD.tag_l (e : TagD) : e.tag .l = e.l := rfl

/-- The tag map `r` is the right tags. -/
@[simp] theorem TagD.tag_r (e : TagD) : e.tag .r = e.r := rfl

/-- Whether a tagged simple evidence is an arrow. -/
def TagTy.IsArrow : TagTy → Prop
  | .arrow _ _ => True
  | _ => False

/-! ## Erasure into formula types -/

mutual
/-- Erasure of a tagged simple evidence: forget the tags. -/
@[reducible] def TagTy.toF : TagTy → FTy
  | .real => .real
  | .bool => .bool
  | .unk => .unk
  | .arrow s d => .arrow s.toF ⟨d.n, d.toFty, d.C⟩
/-- The entries of the erasure of a tagged distribution evidence (the entry
function of `TagD.toF`). -/
@[reducible] def TagD.toFty : (e : TagD) → Fin e.n → FTy
  | .mk _ ty _ _ _ => fun i => (ty i).toF
end

/-- Erasure of a tagged distribution evidence: forget the tags. The number of
cells and the formula are those of the evidence, definitionally. -/
@[reducible] def TagD.toF (e : TagD) : FDist := ⟨e.n, e.toFty, e.C⟩

/-- The erasure of a tagged distribution evidence has as many entries as the
evidence. -/
@[simp] theorem TagD.toF_n (e : TagD) : e.toF.n = e.n := rfl

/-- The erasure of an entry is the entry of the erasure. -/
@[simp] theorem tagD_toF_ty (e : TagD) (i : Fin e.n) :
    e.toF.ty i = (e.ty i).toF := by
  cases e; rfl

/-- Erasure commutes with a `getD .unk` default. -/
theorem toF_getD_unk (o : Option TagTy) :
    ((o.getD .unk) : TagTy).toF = (o.map TagTy.toF).getD FTy.unk := by
  cases o <;> rfl

/-! ## Flipping the tag maps

An evidence for `σ₁ ∼̇ σ₂` read as an evidence for `σ₂ ∼̇ σ₁`. Rule (Dapp)
coerces the argument with the domain of the function's evidence, which
exchanges the two judged sides; `tagDom` below returns the flipped domain. -/

mutual
/-- Swap the two tag maps of a simple evidence, hereditarily. -/
def TagTy.flip : TagTy → TagTy
  | .real => .real
  | .bool => .bool
  | .unk => .unk
  | .arrow s d => .arrow s.flip ⟨d.n, d.flipty, d.C, d.r, d.l⟩
/-- The entries of a flipped distribution evidence (the entry function of
`TagD.flip`). -/
def TagD.flipty : (e : TagD) → Fin e.n → TagTy
  | .mk _ ty _ _ _ => fun i => (ty i).flip
end

/-- Swap the two tag maps of a distribution evidence, hereditarily. -/
def TagD.flip (e : TagD) : TagD := ⟨e.n, e.flipty, e.C, e.r, e.l⟩

mutual
/-- Flipping the tags does not change the erasure (simple evidence). -/
@[simp] theorem TagTy.flip_toF : ∀ (e : TagTy), e.flip.toF = e.toF
  | .real => rfl
  | .bool => rfl
  | .unk => rfl
  | .arrow s d => by
      show FTy.arrow s.flip.toF d.flip.toF = FTy.arrow s.toF d.toF
      rw [TagTy.flip_toF s, TagD.flip_toF d]
/-- Flipping the tags does not change the erasure (distribution evidence). -/
theorem TagD.flip_toF : ∀ (e : TagD), e.flip.toF = e.toF
  | .mk n ty C l r => by
      show FDist.mk n (fun i => ((ty i).flip).toF) C
        = FDist.mk n (fun i => (ty i).toF) C
      congr 1
      funext i
      exact TagTy.flip_toF (ty i)
end

/-- Flipping exchanges the two tag maps. -/
@[simp] theorem TagD.flip_tag (e : TagD) (π : Side) : e.flip.tag π = e.tag π.swap := by
  cases π <;> rfl

/-- Flipping keeps the shape of a simple evidence. -/
@[simp] theorem TagTy.flip_isArrow (e : TagTy) : e.flip.IsArrow = e.IsArrow := by
  cases e <;> rfl

/-! ## The diagonal embedding (identity tags) -/

end GradualProb.TPLC

namespace GradualProb.GPLC

open GradualProb.TPLC

/-- Whether a formula simple type is an arrow. -/
def FTy.IsArrow : FTy → Prop
  | .arrow _ _ => True
  | _ => False

mutual
/-- A formula simple type as a tagged evidence with identity tags: the
reflexive evidence for `σ ∼̇ σ`.

In the article the types inferred by the typing judgments are formula types
whose variables carry the diagonal tags (each cell points at itself). Here
`FTy`/`FDist` carry no tags; the diagonal tags are recomputed when a type is
used as an evidence, by `FTy.toTag`/`FDist.toTag`. -/
def FTy.toTag : FTy → TagTy
  | .real => .real
  | .bool => .bool
  | .unk => .unk
  | .arrow s D => .arrow s.toTag ⟨D.n, D.toTagty, D.C, Fin.val, Fin.val⟩
/-- The entries of the diagonal embedding of a formula distribution type (the
entry function of `FDist.toTag`). -/
def FDist.toTagty : (D : FDist) → Fin D.n → TagTy
  | .mk _ ty _ => fun i => (ty i).toTag
end

/-- A formula distribution type as a tagged evidence with identity tags (see
`FTy.toTag`). -/
def FDist.toTag (D : FDist) : TagD := ⟨D.n, D.toTagty, D.C, Fin.val, Fin.val⟩

mutual
/-- The erasure of the diagonal embedding of `σ` is `σ`. -/
theorem FTy.toTag_toF : ∀ (σ : FTy), σ.toTag.toF = σ
  | .real => rfl
  | .bool => rfl
  | .unk => rfl
  | .arrow s D => by
      show FTy.arrow s.toTag.toF D.toTag.toF = FTy.arrow s D
      rw [FTy.toTag_toF s, FDist.toTag_toF D]
/-- The erasure of the diagonal embedding of `D` is `D`. -/
theorem FDist.toTag_toF : ∀ (D : FDist), D.toTag.toF = D
  | .mk n ty C => by
      show FDist.mk n (fun i => ((ty i).toTag).toF) C = FDist.mk n ty C
      congr 1
      funext i
      exact FTy.toTag_toF (ty i)
end

end GradualProb.GPLC

namespace GradualProb.TPLC

open GradualProb.GPLC



/-- The tags of the diagonal embedding are the identity, on both sides. -/
@[simp] theorem FDist.toTag_tag (D : FDist) (π : Side) : D.toTag.tag π = Fin.val := by
  cases π <;> rfl

/-! ## Tag-aware precision between evidences (Figure 18)

The judgment `σ ⊑ σ' ⊢[π] e ⊑̇ e'` compares two evidences cell by cell along
one of the two tags `π ∈ {l, r}`, and compares the entries of the judged
types that the tags name: `TagPrecTy π` for simple evidences and `TagPrecD π`
for distribution evidences, mutually inductive. Only the judged types on the
side `π` appear as arguments, since the judgment only reads the tags `π`.

Rule (πevd) relates the solutions of the two formulas by the lifting of a
relation on the cells. Since an inductive cannot mention itself under the
definition `SymLiftAll`, the lifted relation is an explicit witness `R`
contained in the cell relation, as in `PrecD`; `TagPrecD.intro` and
`TagPrecD.coup` state the rule on the cell relation itself. -/

mutual
/-- Tag-aware precision `σ ⊑ σ' ⊢[π] e ⊑̇ e'` of simple evidences (Figure 18). -/
inductive TagPrecTy (π : Side) : FTy → FTy → TagTy → TagTy → Prop where
  /-- Rule (πB): one of the judged types or of the evidences is not an arrow,
  and the erasures are related by runtime precision. -/
  | flat : ∀ {σ σ' : FTy} {e e' : TagTy},
      ¬ (σ.IsArrow ∧ σ'.IsArrow ∧ e.IsArrow ∧ e'.IsArrow) →
      EPrecTy e.toF e'.toF → TagPrecTy π σ σ' e e'
  /-- Rule (π→): the domains and the codomains are related. -/
  | arrow : ∀ {σ σ' : FTy} {D D' : FDist} {s s' : TagTy} {d d' : TagD},
      TagPrecTy π σ σ' s s' → TagPrecD π d d' D D' →
      TagPrecTy π (.arrow σ D) (.arrow σ' D') (.arrow s d) (.arrow s' d')
/-- Rule (πevd) of Figure 18, `D ⊑ D' ⊢[π] e ⊑̇ e'`: the tags `π` of both
evidences are in range, and every solution of `e` is coupled with a solution
of `e'` so that, at each cell pair of positive weight, the cell evidences are
related by `TagPrecTy π` against the entries their tags name, and those
entries are related by type precision `PrecTy`. -/
inductive TagPrecD (π : Side) : TagD → TagD → FDist → FDist → Prop where
  | mk : ∀ {e e' : TagD} {D D' : FDist} (R : Fin e.n → Fin e'.n → Prop)
      (ht : ∀ c : Fin e.n, e.tag π c < D.n) (ht' : ∀ c : Fin e'.n, e'.tag π c < D'.n),
      (∀ c c', R c c' → TagPrecTy π (D.ty ⟨e.tag π c, ht c⟩) (D'.ty ⟨e'.tag π c', ht' c'⟩)
        (e.ty c) (e'.ty c')) →
      (∀ c c', R c c' → PrecTy (D.ty ⟨e.tag π c, ht c⟩) (D'.ty ⟨e'.tag π c', ht' c'⟩)) →
      SymLiftAll R e.toF.C e'.toF.C →
      TagPrecD π e e' D D'
end

/-- `σ ⊑ σ' ⊢[π] e ⊑̇ e'`, the tag-aware precision of simple evidences along
`π` (Figure 18), the article's `σ ⊑ σ' ⊢_π e ⊑̇ e'`. -/
scoped notation:50 (name := tagPrecTyStx) σ:51 " ⊑ " σ':51 " ⊢[" π "] " e:51 " ⊑̇ " e':51 =>
  TagPrecTy π σ σ' e e'
/-- `D ⊑ D' ⊢[π] e ⊑̇ e'`, the tag-aware precision of distribution evidences
along `π` (Figure 18). In `TagPrecD π e e' D D'` the evidences come before the
judged types; the notation restores the article's order. -/
scoped notation:50 (name := tagPrecDStx) D:51 " ⊑ " D':51 " ⊢[" π "] " e:51 " ⊑̇ " e':51 =>
  TagPrecD π e e' D D'

/-! ### The distribution rule on the cell relation -/

/-- The tags `π` of `e` are in range for `D`. -/
theorem TagPrecD.tag_lt {π : Side} {e e' : TagD} {D D' : FDist} :
    TagPrecD π e e' D D' → ∀ c : Fin e.n, e.tag π c < D.n
  | .mk _ ht _ _ _ _ => ht

/-- The tags `π` of `e'` are in range for `D'`. -/
theorem TagPrecD.tag_lt' {π : Side} {e e' : TagD} {D D' : FDist} :
    TagPrecD π e e' D D' → ∀ c : Fin e'.n, e'.tag π c < D'.n
  | .mk _ _ ht' _ _ _ => ht'

/-- The coupling clause of `TagPrecD`: every solution of `e` is coupled with a
solution of `e'` so that cells of positive weight are related. -/
theorem TagPrecD.coup {π : Side} {e e' : TagD} {D D' : FDist} (h : TagPrecD π e e' D D') :
    SymLiftAll (fun (c : Fin e.toF.n) (c' : Fin e'.toF.n) =>
          TagPrecTy π (D.ty ⟨e.tag π c, h.tag_lt c⟩) (D'.ty ⟨e'.tag π c', h.tag_lt' c'⟩)
            (e.ty c) (e'.ty c') ∧
          PrecTy (D.ty ⟨e.tag π c, h.tag_lt c⟩) (D'.ty ⟨e'.tag π c', h.tag_lt' c'⟩))
      e.toF.C e'.toF.C :=
  match h with
  | .mk _ _ _ hty hprec hc => hc.mono fun c c' hR => ⟨hty c c' hR, hprec c c' hR⟩

/-- Introduction rule for `TagPrecD`, from the lifting of the cell relation. -/
theorem TagPrecD.intro {π : Side} {e e' : TagD} {D D' : FDist}
    (ht : ∀ c : Fin e.n, e.tag π c < D.n) (ht' : ∀ c : Fin e'.n, e'.tag π c < D'.n)
    (hc : SymLiftAll (fun (c : Fin e.toF.n) (c' : Fin e'.toF.n) =>
          TagPrecTy π (D.ty ⟨e.tag π c, ht c⟩) (D'.ty ⟨e'.tag π c', ht' c'⟩) (e.ty c) (e'.ty c') ∧
          PrecTy (D.ty ⟨e.tag π c, ht c⟩) (D'.ty ⟨e'.tag π c', ht' c'⟩))
      e.toF.C e'.toF.C) :
    TagPrecD π e e' D D' :=
  .mk _ ht ht' (fun _ _ h => h.1) (fun _ _ h => h.2) hc

/-! ### Inversion at arrows -/

/-- Inversion of `TagPrecTy` at arrows: the domains and the codomains are
related (rule (πB) does not apply to four arrows). -/
theorem TagPrecTy.arrow_inv {π : Side} {s s' : TagTy} {d d' : TagD} {σ D σ' D'}
    (h : TagPrecTy π (.arrow σ D) (.arrow σ' D') (.arrow s d) (.arrow s' d')) :
    TagPrecTy π σ σ' s s' ∧ TagPrecD π d d' D D' := by
  cases h with
  | flat hn _ => exact absurd ⟨trivial, trivial, trivial, trivial⟩ hn
  | arrow hs hd => exact ⟨hs, hd⟩

/-- Every evidence is tag-aware more precise than `?`: rule (πB), since `?` is
not an arrow. -/
theorem TagPrecTy.unk_right {π : Side} {σ σ' : FTy} {e : TagTy} :
    TagPrecTy π σ σ' e .unk :=
  .flat (fun h => h.2.2.2) EPrecTy.unk

/-- The evidence `Real` is related to itself against any judged types: rule
(πB), since `Real` is not an arrow. -/
theorem TagPrecTy.real_real {π : Side} {σ σ' : FTy} : TagPrecTy π σ σ' .real .real :=
  .flat (fun h => h.2.2.1) EPrecTy.real

/-- Only an arrow is below an arrow in runtime precision. -/
theorem TagTy.isArrow_of_eprec {x y : TagTy} (h : EPrecTy x.toF y.toF) (hy : y.IsArrow) :
    x.IsArrow := by
  cases y with
  | arrow =>
      cases x with
      | arrow => trivial
      | real | bool | unk => exact nomatch h
  | real | bool | unk => exact hy.elim

/-! ### Projection to the erasures: tag-aware precision implies the runtime
precision of the erased evidences. -/

mutual
/-- Tag-aware precision implies the runtime precision `⊑̇` of the erased simple
evidences. -/
theorem TagPrecTy.toEPrecTy {π : Side} : ∀ {σ σ' : FTy} {e e' : TagTy},
    TagPrecTy π σ σ' e e' → EPrecTy e.toF e'.toF
  | _, _, _, _, .flat _ h => h
  | _, _, _, _, .arrow hs hd => .arrow (TagPrecTy.toEPrecTy hs) (TagPrecD.toEPrecD hd)
/-- Tag-aware precision implies the runtime precision `⊑̇` of the erased
distribution evidences. -/
theorem TagPrecD.toEPrecD {π : Side} : ∀ {e e' : TagD} {D D' : FDist},
    TagPrecD π e e' D D' → EPrecD e.toF e'.toF
  | _, _, _, _, .mk R _ _ hty _ hc =>
      .mk R (fun c c' hR => by
        rw [tagD_toF_ty, tagD_toF_ty]
        exact TagPrecTy.toEPrecTy (hty c c' hR)) hc
end

/-! ### Flipping exchanges the two tags

Rule (Dapp) coerces the argument with the domain of the function's evidence,
with its two tags exchanged: if `ε ⊢ (σ₁ → γ₁) ∼̇ (σ₂ → γ₂)`, the domain
evidence justifies `σ₂ ∼̇ σ₁`, whose right side is the left side of `ε`'s
judgment. Flipping the tags exchanges the two judgments `⊢[.l]` and `⊢[.r]`. -/

mutual
/-- Flipping the tags of both evidences exchanges `⊢[π]` and `⊢[π.swap]`
(simple level), where `π.swap` is the other pointer. -/
theorem TagPrecTy.flip {π : Side} : ∀ {σ σ' : FTy} {e e' : TagTy},
    TagPrecTy π σ σ' e e' → TagPrecTy π.swap σ σ' e.flip e'.flip
  | _, _, e, e', .flat hn h =>
      .flat (by rwa [TagTy.flip_isArrow, TagTy.flip_isArrow])
        (by rwa [TagTy.flip_toF, TagTy.flip_toF])
  | _, _, _, _, .arrow hs hd => .arrow (TagPrecTy.flip hs) (TagPrecD.flip hd)
/-- Flipping the tags of both evidences exchanges `⊢[π]` and `⊢[π.swap]`
(distribution level). -/
theorem TagPrecD.flip {π : Side} : ∀ {e e' : TagD} {D D' : FDist},
    TagPrecD π e e' D D' → TagPrecD π.swap e.flip e'.flip D D'
  | .mk _ _ _ _ _, .mk _ _ _ _ _, _, _, .mk R ht ht' hty hprec hc => by
      cases π <;>
      exact .mk R ht ht' (fun c c' hR => TagPrecTy.flip (hty c c' hR)) hprec hc
end

/-! ## Shallow validity

Validity without the hereditary clause on the cells: the distribution clause
of Definition 9 checks the tags and the tag-guided precision but not the
validity of each cell. It is an intermediate step of Lemma 7; the typing rules
use the hereditary validity defined further below. -/

/-- Shallow validity along `π`: the tags `π` are in range and tag-guide the
erasure's precision into `D`. -/
def TagD.Valid (π : Side) (e : TagD) (D : FDist) : Prop :=
  ∃ h : ∀ c : Fin e.n, e.tag π c < D.n, TagPrec e.toF D (fun c => ⟨e.tag π c, h c⟩)

/-- Shallow validity of a tagged evidence for the judgment `D1 ∼̇ D2`. -/
def TagD.ValidFor (e : TagD) (D1 D2 : FDist) : Prop :=
  e.Valid .l D1 ∧ e.Valid .r D2

/-- The diagonal embedding is valid against its own type along either tag:
identity tags push solutions forward to themselves (`pushfwd_id`) and entries
are reflexively precise. -/
theorem TagD.valid_toTag (π : Side) : ∀ {D : FDist}, GoodD D → D.toTag.Valid π D
  | .mk n ty C, hg => by
      refine ⟨fun c => by rw [FDist.toTag_tag]; exact c.isLt, ?_, ?_⟩
      · intro k
        cases π <;>
        · show EPrecTy ((ty (⟨(k : ℕ), k.isLt⟩ : Fin n)).toTag).toF
            (ty (⟨(k : ℕ), k.isLt⟩ : Fin n))
          rw [FTy.toTag_toF]
          exact EPrecTy.refl (hg.tys _)
      · intro w hw
        cases π <;>
        · show C (pushfwd (fun c => c) w)
          rwa [pushfwd_id]

/-! ### Shallow validity of simple evidence

`VTag π e σ` follows the rules of validity (Definition 9) on simple types, with
the shallow `TagD.Valid` at arrow codomains. -/

/-- Shallow validity of a simple evidence along `π`. -/
inductive VTag (π : Side) : TagTy → FTy → Prop where
  | real : VTag π .real .real
  | bool : VTag π .bool .bool
  | unk  : ∀ {e}, VTag π e .unk
  | arrow : ∀ {s : TagTy} {d : TagD} {σs : FTy} {σD : FDist},
      VTag π s σs → d.Valid π σD → VTag π (.arrow s d) (.arrow σs σD)

/-- Shallow validity of a simple evidence for the judgment `σ ∼̇ σ'`. -/
def VTagTy (e : TagTy) (σ σ' : FTy) : Prop := VTag .l e σ ∧ VTag .r e σ'

/-- A shallowly valid evidence for `σ ∼̇ σ'` is shallowly left valid for `σ`. -/
theorem VTagTy.left {e σ σ'} (h : VTagTy e σ σ') : VTag .l e σ := h.1
/-- A shallowly valid evidence for `σ ∼̇ σ'` is shallowly right valid for `σ'`. -/
theorem VTagTy.right {e σ σ'} (h : VTagTy e σ σ') : VTag .r e σ' := h.2


/-! ### Shallow validity is evidence -/

/-- Shallow validity of a well-formed evidence implies runtime precision of
its erasure (well-formedness gives the nonnegativity that `eprecD_of_tagPrec`
needs). -/
theorem vtag_eprec {π : Side} : ∀ {e : TagTy} {σ : FTy}, VTag π e σ → GoodTy e.toF →
    EPrecTy e.toF σ
  | _, _, .real, _ => EPrecTy.real
  | _, _, .bool, _ => EPrecTy.bool
  | _, _, .unk, _ => EPrecTy.unk
  | _, _, .arrow hs hd, hg => by
      cases hg with
      | arrow hgs hgd =>
        obtain ⟨hr, hp⟩ := hd
        exact EPrecTy.arrow (vtag_eprec hs hgs) (eprecD_of_tagPrec hp hgd.good.nonneg)

/-- Shallow validity of a simple evidence implies Definition 8 for its
erasure (a step of Lemma 7). -/
theorem vtag_evTy {e : TagTy} {σ σ' : FTy} (h : VTagTy e σ σ')
    (hg : GoodTy e.toF) : EEvTy e.toF σ σ' :=
  ⟨vtag_eprec h.1 hg, vtag_eprec h.2 hg⟩

/-- Shallow validity of a distribution evidence implies Definition 8 for its
erasure (a step of Lemma 7). -/
theorem validFor_evD {e : TagD} {D1 D2 : FDist} (h : e.ValidFor D1 D2)
    (hg : GoodD e.toF) : EEvD e.toF D1 D2 := by
  obtain ⟨⟨hl, hpl⟩, ⟨hr, hpr⟩⟩ := h
  exact ⟨eprecD_of_tagPrec hpl hg.good.nonneg, eprecD_of_tagPrec hpr hg.good.nonneg⟩

/-! ## Valid evidence (Definition 9)

The routed reduction rules (Dlet) and (D::μ) coerce, at each cell `c` of the
routing evidence, the outcome that the left tag of `c` names to the target
entry that its right tag names, using the cell's entry `e.ty c` as the coercion
evidence (`Red` names them through the projections of the cell, which agree
with its tags, and the target entry of (D::μ) through the right tag; see
`TagD`). Typing that coercion
needs the entry to be valid for the judgment its tags name, so validity is
hereditary: the distribution clause asks every cell to be valid against the
entry its tag names. -/


mutual
/-- Definition 9, validity `e ⊩[π] σ` of a simple evidence along `π`. -/
inductive HVTag (π : Side) : TagTy → FTy → Prop where
  | real : HVTag π .real .real
  | bool : HVTag π .bool .bool
  | unk  : ∀ {e}, HVTag π e .unk
  | arrow : ∀ {s : TagTy} {d : TagD} {σs : FTy} {σD : FDist},
      HVTag π s σs → HValid π d σD → HVTag π (.arrow s d) (.arrow σs σD)
/-- Definition 9, validity of a distribution evidence along `π` (the
distribution rule): the tags `π` are in range, the erasure is tag-guided
precise into `D` (`TagPrec`), and every cell is valid against the entry its
tag `π` names. -/
inductive HValid (π : Side) : TagD → FDist → Prop where
  | mk : ∀ {e : TagD} {D : FDist} (ht : ∀ c : Fin e.n, e.tag π c < D.n),
      TagPrec e.toF D (fun c => ⟨e.tag π c, ht c⟩) →
      (∀ c : Fin e.n, HVTag π (e.ty c) (D.ty ⟨e.tag π c, ht c⟩)) →
      HValid π e D
end

/-- `e ⊩[π] σ`, the simple evidence `e` is valid for `σ` along `π`
(Definition 9), the article's `ε ⊩_ℓ σ` and `ε ⊩_r σ`. -/
scoped notation:50 (name := hVTagStx) e:51 " ⊩[" π "] " σ:51 => HVTag π e σ
/-- `e ⊩[π] D`, the distribution evidence `e` is valid for `D` along `π`
(Definition 9). -/
scoped notation:50 (name := hValidStx) e:51 " ⊩[" π "] " D:51 => HValid π e D

/-- An evidence valid against an arrow is an arrow. -/
theorem HVTag.isArrow {π : Side} {e : TagTy} {σ : FTy} (h : HVTag π e σ) (hσ : σ.IsArrow) :
    e.IsArrow := by
  cases h with
  | arrow => trivial
  | real | bool | unk => exact hσ.elim

/-- Definition 9 (valid evidence), distribution types: `e ⊩ D1 ∼̇ D2` iff `e`
is left valid for `D1` and right valid for `D2`. -/
def TagD.HValidFor (e : TagD) (D1 D2 : FDist) : Prop :=
  e ⊩[.l] D1 ∧ e ⊩[.r] D2

/-- `e ⊩ D1 ∼̇ D2`, the distribution evidence `e` is valid for the judgment
`D1 ∼̇ D2` (Definition 9). -/
scoped notation:50 (name := hValidForStx) e:51 " ⊩ " D1:51 " ∼̇ " D2:51 => TagD.HValidFor e D1 D2

/-- The tags `π` of an evidence valid along `π` are in range. -/
theorem HValid.tag_lt {π : Side} : ∀ {e : TagD} {D : FDist}, HValid π e D →
    ∀ c : Fin e.n, e.tag π c < D.n
  | _, _, .mk ht _ _ => ht

/-! Valid evidence is shallowly valid. -/

mutual
/-- A simple evidence valid along `π` is shallowly valid along `π`. -/
theorem hvtag_toV {π : Side} : ∀ {e : TagTy} {σ : FTy}, HVTag π e σ → VTag π e σ
  | _, _, .real => .real
  | _, _, .bool => .bool
  | _, _, .unk => .unk
  | _, _, .arrow hs hd => .arrow (hvtag_toV hs) (hvalid_toV hd)
/-- A distribution evidence valid along `π` is shallowly valid along `π`. -/
theorem hvalid_toV {π : Side} : ∀ {e : TagD} {D : FDist}, HValid π e D → e.Valid π D
  | _, _, .mk hr hp _ => ⟨hr, hp⟩
end

/-- A valid distribution evidence is shallowly valid (a step of Lemma 7). -/
theorem TagD.HValidFor.toV {e : TagD} {D1 D2 : FDist} (h : e.HValidFor D1 D2) :
    e.ValidFor D1 D2 :=
  ⟨hvalid_toV h.1, hvalid_toV h.2⟩


/-- The cells of a well-formed distribution evidence are well-formed. -/
theorem TagD.goodTy_entry {e : TagD} (hg : GoodD e.toF) (c : Fin e.n) :
    GoodTy (e.ty c).toF := by
  obtain ⟨n, ty, C, l, r⟩ := e
  exact hg.tys c

/-! ## Valid simple evidence and Lemma 7 -/

/-- Definition 9 (valid evidence), simple types: `e ⊩ σ ∼̇ σ'` iff `e` is left
valid for `σ` and right valid for `σ'`. This is the premise of the ascription
rules of TPLC typing. -/
def HVTagTy (e : TagTy) (σ σ' : FTy) : Prop := e ⊩[.l] σ ∧ e ⊩[.r] σ'

/-- `e ⊩ σ ∼̇ σ'`, the simple evidence `e` is valid for the judgment `σ ∼̇ σ'`
(Definition 9). -/
scoped notation:50 (name := hVTagTyStx) e:51 " ⊩ " σ:51 " ∼̇ " σ':51 => HVTagTy e σ σ'

/-- A valid evidence for `σ ∼̇ σ'` is left valid for `σ`. -/
theorem HVTagTy.left {e σ σ'} (h : HVTagTy e σ σ') : HVTag .l e σ := h.1
/-- A valid evidence for `σ ∼̇ σ'` is right valid for `σ'`. -/
theorem HVTagTy.right {e σ σ'} (h : HVTagTy e σ σ') : HVTag .r e σ' := h.2

/-- A valid simple evidence is shallowly valid (a step of Lemma 7). -/
theorem hvtag_toVTy {e : TagTy} {σ σ' : FTy} (h : HVTagTy e σ σ') :
    VTagTy e σ σ' :=
  ⟨hvtag_toV h.1, hvtag_toV h.2⟩

/-- Lemma 7 (valid evidence is evidence), simple types: a well-formed evidence
valid for `σ ∼̇ σ'` is an evidence for `σ ∼̇ σ'` (Definition 8). -/
theorem valid_evidence_ty {e : TagTy} {σ σ' : FTy} (h : e ⊩ σ ∼̇ σ')
    (hg : GoodTy e.toF) : e.toF ⊢ σ ∼̇ σ' :=
  vtag_evTy (hvtag_toVTy h) hg

/-- Lemma 7 (valid evidence is evidence), distribution types: a well-formed
evidence valid for `D1 ∼̇ D2` is an evidence for `D1 ∼̇ D2` (Definition 8). -/
theorem valid_evidence_d {e : TagD} {D1 D2 : FDist} (h : e ⊩ D1 ∼̇ D2)
    (hg : GoodD e.toF) : e.toF ⊢ D1 ∼̇ D2 :=
  validFor_evD h.toV hg

/-! Flipping the tags exchanges the two validities (what rule (Dapp) needs for
the flipped domain). -/

mutual
/-- If `e` is valid for `σ` along `π`, then `e.flip` is valid for `σ` along
the other pointer. -/
theorem hvtag_flip {π : Side} : ∀ {e : TagTy} {σ : FTy}, HVTag π e σ → HVTag π.swap e.flip σ
  | _, _, .real => .real
  | _, _, .bool => .bool
  | _, _, .unk => .unk
  | _, _, .arrow hs hd => .arrow (hvtag_flip hs) (hvalid_flip hd)
/-- If `d` is valid for `D` along `π`, then `d.flip` is valid for `D` along the
other pointer. -/
theorem hvalid_flip {π : Side} : ∀ {d : TagD} {D : FDist}, HValid π d D → HValid π.swap d.flip D
  | .mk n ty C l r, D, h => by
      cases h with
      | mk hr hp hh =>
        cases π <;>
        exact .mk hr (tagPrec_of_eq (TagD.flip_toF _) hp) fun c => hvtag_flip (hh c)
end

/-! The diagonal embedding of a well-formed type is valid against that type
(the reflexive evidence of literals and λ in the elaboration). -/

mutual
/-- The diagonal embedding of a well-formed `σ` is valid for `σ` along either
tag. -/
theorem hvtag_toTag (π : Side) : ∀ {σ : FTy}, GoodTy σ → HVTag π σ.toTag σ
  | _, .real => .real
  | _, .bool => .bool
  | _, .unk => .unk
  | _, .arrow hs hD => .arrow (hvtag_toTag π hs) (hvalid_toTagD π hD)
/-- The diagonal embedding of a well-formed `D` is valid for `D` along either
tag. -/
theorem hvalid_toTagD (π : Side) : ∀ {D : FDist}, GoodD D → HValid π D.toTag D
  | .mk n ty C, hg => by
      obtain ⟨hr, hp⟩ := TagD.valid_toTag π (D := .mk n ty C) hg
      refine .mk hr hp fun c => ?_
      cases π <;> exact hvtag_toTag _ (hg.tys c)
end

/-- `σ.toTag` is a valid evidence for `σ ∼̇ σ`. -/
theorem hvtag_refl {σ : FTy} (hg : GoodTy σ) : HVTagTy σ.toTag σ σ :=
  ⟨hvtag_toTag .l hg, hvtag_toTag .r hg⟩

/-- Each cell of a valid distribution evidence is a valid simple evidence for
the judgment its two tags name. -/
theorem TagD.HValidFor.entryH {e : TagD} {D1 D2 : FDist} (h : e.HValidFor D1 D2)
    {c : Fin e.n} (h1 : e.l c < D1.n) (h2 : e.r c < D2.n) :
    HVTagTy (e.ty c) (D1.ty ⟨e.l c, h1⟩) (D2.ty ⟨e.r c, h2⟩) := by
  obtain ⟨hL, hR⟩ := h
  cases hL with
  | mk hrL _ hhL =>
    cases hR with
    | mk hrR _ hhR =>
      exact ⟨hhL c, hhR c⟩

/-! ## Domain and codomain of an arrow evidence

An arrow evidence for `(σ' → D) ∼̇ (σa → Dres)` has its domain valid for
`σ' ∼̇ σa`, but rule (Dapp) uses it to coerce the argument, a judgment
`σa ∼̇ σ'`, so `tagDom` swaps the tags. -/

/-- The article's `cdom(ε)` as used by rule (Dapp): the domain of an arrow
evidence with its tags flipped; `none` on other evidences. -/
def tagDom : TagTy → Option TagTy
  | .arrow s _ => some s.flip
  | _ => none

/-- The article's `ccod(ε)`: the codomain of an arrow evidence; `none` on other
evidences. -/
def tagCod : TagTy → Option TagD
  | .arrow _ d => some d
  | _ => none

/-! ## Reflexivity of tag-aware precision

A well-formed evidence that is valid along `π` for a well-formed type is
related to itself, with the diagonal coupling. Validity is what makes each
cell related to itself against the entry its tag names. -/

mutual
/-- Reflexivity of `TagPrecTy π` on evidences valid along `π`. -/
theorem TagPrecTy.refl {π : Side} : ∀ {σ : FTy} {e : TagTy},
    HVTag π e σ → GoodTy e.toF → GoodTy σ → TagPrecTy π σ σ e e
  | _, _, .real, hge, _ => .flat (fun h => h.1) (EPrecTy.refl hge)
  | _, _, .bool, hge, _ => .flat (fun h => h.1) (EPrecTy.refl hge)
  | _, _, .unk, hge, _ => .flat (fun h => h.1) (EPrecTy.refl hge)
  | .arrow σs σD, .arrow s d, .arrow hs hd, hge, hg => by
      cases hge with
      | arrow hges hged =>
        cases hg with
        | arrow hgs hgd =>
          exact .arrow (TagPrecTy.refl hs hges hgs) (TagPrecD.refl hd hged hgd)
  termination_by structural _ _ hval _ _ => hval
/-- Reflexivity of `TagPrecD π` on evidences valid along `π`, with the
diagonal coupling (`Lift.refl`). -/
theorem TagPrecD.refl {π : Side} : ∀ {e : TagD} {D : FDist},
    HValid π e D → GoodD e.toF → GoodD D → TagPrecD π e e D D
  | e, .mk n ty C, .mk hr _ hh, hge, hg => by
      refine TagPrecD.intro hr hr fun w hw =>
        ⟨w, hw, .refl (hge.good.nonneg w hw) fun c => ?_⟩
      exact ⟨TagPrecTy.refl (hh _) (TagD.goodTy_entry hge _) (hg.tys _),
        PrecTy.refl (hg.tys _)⟩
  termination_by structural _ _ hval _ _ => hval
end


end GradualProb.TPLC
