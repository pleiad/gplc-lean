import GradualProb.GPLC.FormulaTypes
import GradualProb.SPLC.Equality

/-!
# Concretization and the declarative relations

The concretization `γ` of formula types (Section 4.1) and the relations that
AGT derives from it: type consistency by AGT (Definition 1, `AgtConsTy`,
`AgtConsD`) and declarative type precision (Definition 6, `AgtPrecTy`,
`AgtPrecD`). Equality of static types in these definitions is the coupling
equality `SPLC.EqTy`/`SPLC.EqD`.

## Main results

* `agt_consistencyTy_iff`, `agt_consistency_iff`: Lemma 3 (equivalence of
  consistencies), over well-formed formula types.
* `goodTy_fconcr`, `goodD_fconcr`: a well-formed formula type has a
  concretization.

## Reading guide

The direction from Definition 1 to Definition 4 (`agtConsTy_to_consTy`,
`agtConsD_to_consD`) needs no well-formedness: the split of a concretization
is a lifting between the probabilities of its entries and a solution of the
formula (`lift_split`), and the two splits compose with the lifting of
equality between the concretizations (`Lift.trans`). The converse
(`consTy_to_agtConsTy`, `consD_to_agtConsD`) builds one block per pair of
entries `(i, j)` with probability `w i j`, taking coupled-equal concretizations
where `0 < w i j` and the concretizations given by the coverage clauses
elsewhere; these exist by well-formedness, and the grid of blocks has the two
solutions as marginals (`IsCoupling.restrict`). Lemma 5 (soundness of type
precision) is in `GPLC/Precision`.
-/


namespace GradualProb.GPLC

open GradualProb.SPLC

open scoped BigOperators
open Classical

/-! ## `γ` on formula types -/

/- The concretization of formula types (Section 4.1), as inductive relations:
`FConcrTy σ τ` means `τ ∈ γ(σ)` and `FConcrD D S` means `S ∈ γ(D)`, with `τ`
and `S` static. A static distribution type concretizes `D` when there are a
solution `p` of the closing formula of `D` and a map `f` assigning each static
entry to the formula entry it refines, such that every static simple type
concretizes the type of its formula entry, the probabilities of the block over
entry `i` sum to `p i`, and every block is non-empty (`f` is surjective). -/
mutual
/-- `FConcrTy σ τ`: the static simple type `τ` is in `γ(σ)`. -/
inductive FConcrTy : FTy → Ty → Prop where
  | real : FConcrTy .real .real
  | bool : FConcrTy .bool .bool
  | unk  : ∀ {t}, IsStaticTy t → FConcrTy .unk t
  | arrow : ∀ {s D t e}, FConcrTy s t → FConcrD D e → FConcrTy (.arrow s D) (.arrow t e)
/-- `FConcrD D S`: the static distribution type `S` is in `γ(D)`. -/
inductive FConcrD : FDist → DTy → Prop where
  | dist : ∀ {D : FDist} {S : List (Ty × ℝ)} {p : Fin D.n → ℝ} {f : Fin S.length → Fin D.n},
      D.C p →
      (∀ k, FConcrTy (D.ty (f k)) (S.get k).1) →
      (∀ i, (∑ k ∈ Finset.univ.filter (fun k => f k = i), (S.get k).2) = p i) →
      (∀ k, 0 ≤ (S.get k).2) →
      -- the concretization is a static type: its probabilities lie in `[0,1]`
      (∀ k, (S.get k).2 ≤ 1) →
      -- non-empty blocks: every formula entry has a static representative
      (∀ i, ∃ k, f k = i) →
      FConcrD D (.dist (S.map (fun e => (e.1, GProb.q e.2))))
end

/-! ## Concretizations are static -/

mutual
/-- Every concretization `τ ∈ γ(σ)` of a formula simple type is static. -/
theorem fconcrTy_static : ∀ {s : FTy} {t : Ty}, FConcrTy s t → IsStaticTy t
  | _, _, .real => .real
  | _, _, .bool => .bool
  | _, _, .unk h => h
  | _, _, .arrow hs hd => .arrow (fconcrTy_static hs) (fconcrD_static hd)
/-- Every concretization `S ∈ γ(D)` of a formula distribution type is static. -/
theorem fconcrD_static : ∀ {D : FDist} {S : DTy}, FConcrD D S → IsStaticDTy S
  | _, _, .dist (S := S) _ hty _ hnn hle _ => by
      refine .ofEntries ?_
      intro e he
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 he
      obtain ⟨k, rfl⟩ := List.mem_iff_get.1 hs
      exact ⟨fconcrTy_static (hty k), (S.get k).2, rfl, hnn k, hle k⟩
end

/-! ## Membership in `γ` for a static type given as `List.ofFn` -/

/-- Every probability of a solution of a good constraint is at most `1`. -/
theorem GoodC.le_one {n : ℕ} {C : (Fin n → ℝ) → Prop} (hC : GoodC n C)
    {p : Fin n → ℝ} (hp : C p) (i : Fin n) : p i ≤ 1 := by
  rw [← hC.mass p hp]
  exact Finset.single_le_sum (fun j _ => hC.nonneg p hp j) (Finset.mem_univ i)

/-- Introduction form of `FConcrD` for a static type whose entries are given
as a function on `Fin N` with probabilities at most `1`, with a solution `p` of
`D.C` and a split `f`. -/
theorem fconcrD_ofFn_le {D : FDist} {N : ℕ} (a : Fin N → Ty) (wt : Fin N → ℝ)
    (p : Fin D.n → ℝ) (f : Fin N → Fin D.n)
    (hC : D.C p)
    (hty : ∀ k, FConcrTy (D.ty (f k)) (a k))
    (hmass : ∀ i, (∑ k ∈ Finset.univ.filter (fun k => f k = i), wt k) = p i)
    (hnn : ∀ k, 0 ≤ wt k)
    (hwt1 : ∀ k, wt k ≤ 1)
    (hsurj : ∀ i, ∃ k, f k = i) :
    FConcrD D (.dist (List.ofFn fun k => (a k, GProb.q (wt k)))) := by
  have hmap : (List.ofFn fun k => (a k, wt k)).map (fun e => (e.1, GProb.q e.2))
      = List.ofFn fun k => (a k, GProb.q (wt k)) := by
    rw [List.map_ofFn]; rfl
  rw [← hmap]
  have hS : (List.ofFn fun k => (a k, wt k)).length = N := List.length_ofFn
  have hget : ∀ k : Fin (List.ofFn fun k => (a k, wt k)).length,
      (List.ofFn fun k => (a k, wt k)).get k = (a (Fin.cast hS k), wt (Fin.cast hS k)) := by
    intro k; rw [List.get_eq_getElem, List.getElem_ofFn]; rfl
  refine FConcrD.dist (p := p) (f := fun k => f (Fin.cast hS k)) hC ?_ ?_ ?_ ?_ ?_
  · intro k; rw [hget k]; exact hty _
  · intro i
    have key : (∑ k ∈ Finset.univ.filter
          (fun k : Fin (List.ofFn fun k => (a k, wt k)).length => f (Fin.cast hS k) = i),
          ((List.ofFn fun k => (a k, wt k)).get k).2)
        = ∑ k ∈ Finset.univ.filter (fun k => f k = i), wt k := by
      refine Finset.sum_equiv (finCongr hS) (fun k => ?_) (fun k _ => ?_)
      · simp [finCongr_apply]
      · rw [hget k]; simp [finCongr_apply]
    rw [key]; exact hmass i
  · intro k; rw [hget k]; exact hnn _
  · intro k; rw [hget k]; exact hwt1 _
  · intro i
    obtain ⟨k0, hk0⟩ := hsurj i
    exact ⟨Fin.cast hS.symm k0, hk0⟩

/-- `fconcrD_ofFn_le` when the solution `p` has probabilities at most `1`:
the probability of an entry is at most that of its block, which is `p i`. -/
theorem fconcrD_ofFn {D : FDist} {N : ℕ} (a : Fin N → Ty) (wt : Fin N → ℝ)
    (p : Fin D.n → ℝ) (f : Fin N → Fin D.n)
    (hC : D.C p)
    (hty : ∀ k, FConcrTy (D.ty (f k)) (a k))
    (hmass : ∀ i, (∑ k ∈ Finset.univ.filter (fun k => f k = i), wt k) = p i)
    (hnn : ∀ k, 0 ≤ wt k)
    (hp1 : ∀ i, p i ≤ 1)
    (hsurj : ∀ i, ∃ k, f k = i) :
    FConcrD D (.dist (List.ofFn fun k => (a k, GProb.q (wt k)))) := by
  refine fconcrD_ofFn_le a wt p f hC hty hmass hnn (fun k => ?_) hsurj
  have hle : wt k ≤ ∑ k' ∈ Finset.univ.filter (fun k' => f k' = f k), wt k' :=
    Finset.single_le_sum (f := wt) (fun k' _ => hnn k') (by simp)
  exact hle.trans ((hmass _).le.trans (hp1 _))

/-! ## Well-formed types have a concretization -/

mutual
/-- A well-formed formula simple type has a concretization. -/
theorem goodTy_fconcr : ∀ {s : FTy}, GoodTy s → ∃ t, FConcrTy s t
  | _, .real => ⟨.real, .real⟩
  | _, .bool => ⟨.bool, .bool⟩
  | _, .unk  => ⟨.real, .unk .real⟩
  | _, .arrow hs hD => by
      obtain ⟨u, hu⟩ := goodTy_fconcr hs
      obtain ⟨S, hS⟩ := goodD_fconcr hD
      exact ⟨.arrow u S, .arrow hu hS⟩
/-- A well-formed formula distribution type has a concretization (the identity
split at a solution of its formula, concretizing each entry type). -/
theorem goodD_fconcr : ∀ {D : FDist}, GoodD D → ∃ S, FConcrD D S
  | D, .mk hC hty => by
      obtain ⟨p, hp⟩ := hC.sat
      choose a ha using fun i => goodTy_fconcr (hty i)
      refine ⟨_, fconcrD_ofFn a p p (fun k => k) hp ha ?_ (fun k => hC.nonneg p hp k)
        (hC.le_one hp) (fun i => ⟨i, rfl⟩)⟩
      intro i
      rw [show (Finset.univ.filter (fun k : Fin D.n => k = i)) = {i} by
        ext k; simp [eq_comm], Finset.sum_singleton]
end

/-! ## The declarative relations -/

/-- Definition 1 (type consistency, by AGT), on formula simple types: some
concretizations of the two types are equal. -/
def AgtConsTy (s1 s2 : FTy) : Prop :=
  ∃ t1 t2, FConcrTy s1 t1 ∧ FConcrTy s2 t2 ∧ t1 =ₛ t2

/-- Definition 1 (type consistency, by AGT), on formula distribution types:
some concretizations of the two types are equal. -/
def AgtConsD (D1 D2 : FDist) : Prop :=
  ∃ S1 S2, FConcrD D1 S1 ∧ FConcrD D2 S2 ∧ S1 =ₛ S2

/-- `σ ∼ᴬᴳᵀ τ`, consistency by AGT on formula simple types (Definition 1). The
article writes it `∼`, like the inductive consistency `ConsTy` of Definition 4
with which Lemma 3 identifies it; Lean needs a second symbol because both
relate formula simple types. -/
scoped infix:50 (name := agtConsTyStx) " ∼ᴬᴳᵀ " => AgtConsTy
/-- `D ∼ᴬᴳᵀ D'`, consistency by AGT on formula distribution types
(Definition 1). -/
scoped infix:50 (name := agtConsDStx) " ∼ᴬᴳᵀ " => AgtConsD

/-- Definition 6 (type precision), on formula simple types: every
concretization of the left type is equal to some concretization of the right
one. -/
def AgtPrecTy (s1 s2 : FTy) : Prop :=
  ∀ t1, FConcrTy s1 t1 → ∃ t2, FConcrTy s2 t2 ∧ t1 =ₛ t2

/-- Definition 6 (type precision), on formula distribution types: every
concretization of the left type is equal to some concretization of the right
one. -/
def AgtPrecD (D1 D2 : FDist) : Prop :=
  ∀ S1, FConcrD D1 S1 → ∃ S2, FConcrD D2 S2 ∧ S1 =ₛ S2

/-- `σ ⊑ᴬᴳᵀ τ`, type precision by AGT on formula simple types (Definition 6),
the article's `⊑_AGT`. -/
scoped infix:50 (name := agtPrecTyStx) " ⊑ᴬᴳᵀ " => AgtPrecTy
/-- `D ⊑ᴬᴳᵀ D'`, type precision by AGT on formula distribution types
(Definition 6). -/
scoped infix:50 (name := agtPrecDStx) " ⊑ᴬᴳᵀ " => AgtPrecD

/-! ## Equality of concretizations and the split of a concretization

A concretization is a list of entries with concrete probabilities. Equality
of two such lists is stated on functions over `Fin` (`SPLC.map_eq_ofFn_get`,
`SPLC.eqD_ofFn_iff`), and the
split of a concretization is a lifting between the probabilities of its
entries and the solution of the formula (`lift_split`). -/

/-- The split of a concretization couples the probabilities `wt` of the static
entries with the solution `p`: all the probability of the entry `k` goes to the
formula entry `f k` (`Lift.pushfwd`). -/
theorem lift_split {N n : ℕ} {f : Fin N → Fin n} {wt : Fin N → ℝ} {p : Fin n → ℝ}
    (hnn : ∀ k, 0 ≤ wt k)
    (hmass : ∀ i, (∑ k ∈ Finset.univ.filter (fun k => f k = i), wt k) = p i) :
    Lift (fun k i => f k = i) wt p := by
  obtain rfl : pushfwd f wt = p := funext fun i => (pushfwd_eq_sum_filter f wt i).trans (hmass i)
  exact .pushfwd f hnn fun _ => rfl

/-! ## Lemma 3, from Definition 1 to Definition 4 (no well-formedness needed) -/

mutual
/-- One direction of Lemma 3 (Definition 1 to Definition 4), simple types: if
some concretizations `τ₁ ∈ γ(σ₁)` and `τ₂ ∈ γ(σ₂)` are equal, then `σ₁ ∼ σ₂`. -/
theorem agtConsTy_to_consTy : ∀ {s1 : FTy} {u1 : Ty} {s2 : FTy} {u2 : Ty},
    FConcrTy s1 u1 → FConcrTy s2 u2 → EqTy u1 u2 → ConsTy s1 s2
  | _, _, _, _, .unk _, _, _ => .unkL
  | _, _, _, _, _, .unk _, _ => .unkR
  | _, _, _, _, .real, .real, .real => .real
  | _, _, _, _, .bool, .bool, .bool => .bool
  | _, _, _, _, .arrow hc1 hd1, .arrow hc2 hd2, .arrow hceq hdeq =>
      .arrow (agtConsTy_to_consTy hc1 hc2 hceq) (agtConsD_to_consD hd1 hd2 hdeq)
/-- One direction of Lemma 3 (Definition 1 to Definition 4), distribution
types: if some concretizations `S₁ ∈ γ(D₁)` and `S₂ ∈ γ(D₂)` are equal,
then `D₁ ∼ D₂`. -/
theorem agtConsD_to_consD : ∀ {D1 D2 : FDist} {S1 S2 : DTy},
    FConcrD D1 S1 → FConcrD D2 S2 → EqD S1 S2 → ConsD D1 D2
  | D1, D2, _, _, .dist (S := L1) (p := p1) (f := f1) hC1 hty1 hmass1 hnn1 _ hsurj1,
      .dist (S := L2) (p := p2) (f := f2) hC2 hty2 hmass2 hnn2 _ hsurj2, heq => by
    rw [map_eq_ofFn_get _ L1, map_eq_ofFn_get _ L2] at heq
    obtain ⟨hl, hcovL, hcovR⟩ := eqD_ofFn_iff.1 heq
    refine ConsD.intro ⟨p1, p2, hC1, hC2, ?_⟩ ⟨fun i => ?_, fun j => ?_⟩
    · -- the split of `S₁` backwards, the lifting of equality and the split of `S₂`
      refine ((lift_split hnn1 hmass1).symm.trans hl
        (T := fun i l => ConsTy (D1.ty i) (D2.ty (f2 l))) fun i k l hki he => ?_).trans
        (lift_split hnn2 hmass2) fun i l j h hlj => by subst hlj; exact h
      subst hki
      exact agtConsTy_to_consTy (hty1 k) (hty2 l) he
    · -- left coverage: go down to a static entry of the block (blocks are
      -- non-empty), cross by the coverage clause of `EqD`, go up by the split
      obtain ⟨k, rfl⟩ := hsurj1 i
      obtain ⟨l, hl⟩ := hcovL k
      exact ⟨f2 l, agtConsTy_to_consTy (hty1 k) (hty2 l) hl⟩
    · -- right coverage: symmetric
      obtain ⟨l, rfl⟩ := hsurj2 j
      obtain ⟨k, hk⟩ := hcovR l
      exact ⟨f1 k, agtConsTy_to_consTy (hty1 k) (hty2 l) hk⟩
end

/-! ## Lemma 3, from Definition 4 to Definition 1 (uses well-formedness) -/

mutual
/-- One direction of Lemma 3 (Definition 4 to Definition 1), simple types: for
well-formed `σ₁` and `σ₂`, `σ₁ ∼ σ₂` implies that some concretizations of the
two are equal. -/
theorem consTy_to_agtConsTy {s1 s2 : FTy} (h1 : GoodTy s1) (h2 : GoodTy s2) :
    ConsTy s1 s2 → AgtConsTy s1 s2
  | .real => ⟨.real, .real, .real, .real, .real⟩
  | .bool => ⟨.bool, .bool, .bool, .bool, .bool⟩
  | .unkL => by
      obtain ⟨u, hu⟩ := goodTy_fconcr h2
      exact ⟨u, u, .unk (fconcrTy_static hu), hu, EqTy.refl (fconcrTy_static hu)⟩
  | .unkR => by
      obtain ⟨u, hu⟩ := goodTy_fconcr h1
      exact ⟨u, u, hu, .unk (fconcrTy_static hu), EqTy.refl (fconcrTy_static hu)⟩
  | .arrow hcs hcd => by
      cases h1 with
      | arrow hvs1 hvd1 =>
        cases h2 with
        | arrow hvs2 hvd2 =>
          obtain ⟨a1, a2, ha1, ha2, hae⟩ := consTy_to_agtConsTy hvs1 hvs2 hcs
          obtain ⟨d1, d2, hd1, hd2, hde⟩ := consD_to_agtConsD hvd1 hvd2 hcd
          exact ⟨.arrow a1 d1, .arrow a2 d2, .arrow ha1 hd1, .arrow ha2 hd2, .arrow hae hde⟩
/-- One direction of Lemma 3 (Definition 4 to Definition 1), distribution
types: for well-formed `D₁` and `D₂`, `D₁ ∼ D₂` implies that some
concretizations of the two are equal. -/
theorem consD_to_agtConsD {D1 D2 : FDist} (h1 : GoodD D1) (h2 : GoodD D2) :
    ConsD D1 D2 → AgtConsD D1 D2
  | .mk R fL fR hR hl hicovL hicovR => by
    obtain ⟨p, q, hp, hq, w, hw, hs⟩ := hl
    have hG1 : ∀ i, GoodTy (D1.ty i) := h1.tys
    have hG2 : ∀ j, GoodTy (D2.ty j) := h2.tys
    -- equal concretizations for the coverage pairs of Definition 4
    have hRLex : ∀ i, ∃ ab : Ty × Ty, FConcrTy (D1.ty i) ab.1 ∧
        FConcrTy (D2.ty (fL i)) ab.2 ∧ EqTy ab.1 ab.2 := by
      intro i
      obtain ⟨a, b, ha, hb, he⟩ := consTy_to_agtConsTy (hG1 i) (hG2 (fL i)) (hicovL i)
      exact ⟨(a, b), ha, hb, he⟩
    choose RL hRLa hRLb hRLe using hRLex
    have hRRex : ∀ j, ∃ ab : Ty × Ty, FConcrTy (D1.ty (fR j)) ab.1 ∧
        FConcrTy (D2.ty j) ab.2 ∧ EqTy ab.1 ab.2 := by
      intro j
      obtain ⟨a, b, ha, hb, he⟩ := consTy_to_agtConsTy (hG1 (fR j)) (hG2 j) (hicovR j)
      exact ⟨(a, b), ha, hb, he⟩
    choose RR hRRa hRRb hRRe using hRRex
    -- per pair: equal concretizations if the cell has positive probability, the
    -- coverage representatives otherwise
    have hAB : ∀ i j, ∃ ab : Ty × Ty,
        FConcrTy (D1.ty i) ab.1 ∧ FConcrTy (D2.ty j) ab.2 ∧
          (0 < w i j → EqTy ab.1 ab.2) ∧
          (¬ 0 < w i j → ab = ((RL i).1, (RR j).2)) := by
      intro i j
      by_cases hpos : 0 < w i j
      · obtain ⟨a, b, ha, hb, he⟩ := consTy_to_agtConsTy (hG1 i) (hG2 j) (hR i j (hs i j hpos))
        exact ⟨(a, b), ha, hb, fun _ => he, fun hc => absurd hpos hc⟩
      · exact ⟨((RL i).1, (RR j).2), hRLa i, hRRb j,
          fun hc => absurd hc hpos, fun _ => rfl⟩
    choose AB hA hB hE hZ using hAB
    set E := (finProdFinEquiv : Fin D1.n × Fin D2.n ≃ Fin (D1.n * D2.n)) with hEdef
    set aK : Fin (D1.n * D2.n + (D1.n + D2.n)) → Ty :=
      Fin.addCases (fun kp => (AB (E.symm kp).1 (E.symm kp).2).1)
        (Fin.addCases (fun i => (RL i).1) (fun j => (RR j).1)) with haK
    set bK : Fin (D1.n * D2.n + (D1.n + D2.n)) → Ty :=
      Fin.addCases (fun kp => (AB (E.symm kp).1 (E.symm kp).2).2)
        (Fin.addCases (fun i => (RL i).2) (fun j => (RR j).2)) with hbK
    set wtK : Fin (D1.n * D2.n + (D1.n + D2.n)) → ℝ :=
      Fin.addCases (fun kp => w (E.symm kp).1 (E.symm kp).2) (fun _ => 0) with hwtK
    set g1 : Fin (D1.n * D2.n + (D1.n + D2.n)) → Fin D1.n :=
      Fin.addCases (fun kp => (E.symm kp).1) (Fin.addCases id fR) with hg1
    set g2 : Fin (D1.n * D2.n + (D1.n + D2.n)) → Fin D2.n :=
      Fin.addCases (fun kp => (E.symm kp).2) (Fin.addCases fL id) with hg2
    have hwtnn : ∀ k, 0 ≤ wtK k := by
      intro k
      refine Fin.addCases (fun kp => ?_) (fun kab => ?_) k
      · simp only [hwtK, Fin.addCases_left]
        exact hw.nonneg _ _
      · simp only [hwtK, Fin.addCases_right]
        exact le_refl 0
    -- the cells of the grid have the two solutions as marginals
    have hgrid := hw.restrict E.symm.injective fun i j _ => ⟨E (i, j), E.symm_apply_apply _⟩
    refine ⟨.dist (List.ofFn fun k => (aK k, GProb.q (wtK k))),
            .dist (List.ofFn fun k => (bK k, GProb.q (wtK k))), ?_, ?_, ?_⟩
    · refine fconcrD_ofFn aK wtK p g1 hp ?_ ?_ hwtnn (h1.good.le_one hp) ?_
      · intro k
        refine Fin.addCases (fun kp => ?_) (fun kab => ?_) k
        · simp only [haK, hg1, Fin.addCases_left]
          exact hA _ _
        · refine Fin.addCases (fun i => ?_) (fun j => ?_) kab
          · simp only [haK, hg1, Fin.addCases_right, Fin.addCases_left]
            exact hRLa i
          · simp only [haK, hg1, Fin.addCases_right]
            exact hRRa j
      · intro i
        rw [← pushfwd_eq_sum_filter]
        exact (pushfwd_append _ _ _ _ i).trans (by rw [hgrid.1]; simp [pushfwd])
      · intro i
        refine ⟨Fin.natAdd _ (Fin.castAdd _ i), ?_⟩
        simp only [hg1, Fin.addCases_right, Fin.addCases_left]
        rfl
    · refine fconcrD_ofFn bK wtK q g2 hq ?_ ?_ hwtnn (h2.good.le_one hq) ?_
      · intro k
        refine Fin.addCases (fun kp => ?_) (fun kab => ?_) k
        · simp only [hbK, hg2, Fin.addCases_left]
          exact hB _ _
        · refine Fin.addCases (fun i => ?_) (fun j => ?_) kab
          · simp only [hbK, hg2, Fin.addCases_right, Fin.addCases_left]
            exact hRLb i
          · simp only [hbK, hg2, Fin.addCases_right]
            exact hRRb j
      · intro j
        rw [← pushfwd_eq_sum_filter]
        exact (pushfwd_append _ _ _ _ j).trans (by rw [hgrid.2]; simp [pushfwd])
      · intro j
        refine ⟨Fin.natAdd _ (Fin.natAdd _ j), ?_⟩
        simp only [hg2, Fin.addCases_right]
        rfl
    · -- the two members of every coverage entry are equal
      have hself : ∀ kab, EqTy (aK (Fin.natAdd _ kab)) (bK (Fin.natAdd _ kab)) := by
        intro kab
        refine Fin.addCases (fun i => ?_) (fun j => ?_) kab
        · simp only [haK, hbK, Fin.addCases_right, Fin.addCases_left]
          exact hRLe i
        · simp only [haK, hbK, Fin.addCases_right]
          exact hRRe j
      refine eqD_ofFn_diag aK bK wtK hwtnn ?_ ?_ ?_
      · intro k
        refine Fin.addCases (fun kp => ?_) (fun kab => ?_) k
        · intro hpos
          simp only [hwtK, Fin.addCases_left] at hpos
          simp only [haK, hbK, Fin.addCases_left]
          exact hE _ _ hpos
        · intro hpos
          simp only [hwtK, Fin.addCases_right] at hpos
          exact absurd hpos (lt_irrefl 0)
      · intro k
        refine Fin.addCases (fun kp => ?_) (fun kab => ?_) k
        · by_cases h : 0 < w (E.symm kp).1 (E.symm kp).2
          · refine ⟨Fin.castAdd _ kp, ?_⟩
            simp only [haK, hbK, Fin.addCases_left]
            exact hE _ _ h
          · refine ⟨Fin.natAdd _ (Fin.castAdd _ (E.symm kp).1), ?_⟩
            simp only [haK, hbK, Fin.addCases_left, Fin.addCases_right]
            rw [congrArg Prod.fst (hZ _ _ h)]
            exact hRLe (E.symm kp).1
        · exact ⟨Fin.natAdd _ kab, hself kab⟩
      · intro l
        refine Fin.addCases (fun kp => ?_) (fun kab => ?_) l
        · by_cases h : 0 < w (E.symm kp).1 (E.symm kp).2
          · refine ⟨Fin.castAdd _ kp, ?_⟩
            simp only [haK, hbK, Fin.addCases_left]
            exact hE _ _ h
          · refine ⟨Fin.natAdd _ (Fin.natAdd _ (E.symm kp).2), ?_⟩
            simp only [haK, hbK, Fin.addCases_left, Fin.addCases_right]
            rw [congrArg Prod.snd (hZ _ _ h)]
            exact hRRe (E.symm kp).2
        · exact ⟨Fin.natAdd _ kab, hself kab⟩
end

/-! ## Lemma 3 at the formula level -/

/-- Lemma 3 (equivalence of consistencies), item 1, simple types: over well-formed
formula simple types, Definition 1 and Definition 4 coincide. -/
theorem agt_consistencyTy_iff {s1 s2 : FTy} (h1 : GoodTy s1) (h2 : GoodTy s2) :
    s1 ∼ᴬᴳᵀ s2 ↔ s1 ∼ s2 :=
  ⟨fun ⟨_, _, hc1, hc2, he⟩ => agtConsTy_to_consTy hc1 hc2 he, consTy_to_agtConsTy h1 h2⟩

/-- Lemma 3 (equivalence of consistencies), item 2, distribution types: over well-formed
formula distribution types, consistency by AGT (Definition 1) coincides with the
inductive consistency `ConsD` (Definition 4). -/
theorem agt_consistency_iff {D1 D2 : FDist} (h1 : GoodD D1) (h2 : GoodD D2) :
    D1 ∼ᴬᴳᵀ D2 ↔ D1 ∼ D2 :=
  ⟨fun ⟨_, _, hc1, hc2, he⟩ => agtConsD_to_consD hc1 hc2 he, consD_to_agtConsD h1 h2⟩

end GradualProb.GPLC
