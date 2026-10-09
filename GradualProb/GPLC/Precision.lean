import GradualProb.GPLC.Concretization

/-!
# Soundness of type precision

The inductive type precision of Figure 8 (`PrecTy`/`PrecD`, the relation the
type system and the theorems use) is sound with respect to the declarative
type precision of Definition 6 (`AgtPrecTy`/`AgtPrecD`). The converse is not
claimed.

## Main results

* `precTy_to_agtPrecTy`, `precD_to_agtPrecD`: Lemma 5 (soundness of type
  precision).

## Reading guide

Given a concretization of the left type, the proof composes its split
(`lift_split`) with the coupling of `PrecD` (`Lift.trans`) and builds a
concretization of the right type with one static entry for each pair of
indices `(k, j)` of the composed coupling, assigned to the block of `j`. The
type placed at the entry `(k, j)` is always an equal copy of some entry of the
given concretization: of entry `k` itself when its formula entry is precise
for `j` (which a positive coupling weight guarantees), and of an entry obtained
from the right coverage witness `fR j` otherwise. The two coverage clauses of `EqD`
are then read off these entries.
-/

namespace GradualProb.GPLC

open GradualProb.SPLC

open scoped BigOperators
open Classical

mutual
/-- Lemma 5 (soundness of type precision), item 1, simple types: `σ₁ ⊑ σ₂`
(inductive) implies `σ₁ ⊑ᴬᴳᵀ σ₂` (declarative). -/
theorem precTy_to_agtPrecTy {s1 s2 : FTy} :
    s1 ⊑ s2 → s1 ⊑ᴬᴳᵀ s2
  | .real => fun t1 h => by cases h; exact ⟨.real, .real, .real⟩
  | .bool => fun t1 h => by cases h; exact ⟨.bool, .bool, .bool⟩
  | .unk => fun t1 h =>
      ⟨t1, .unk (fconcrTy_static h), EqTy.refl (fconcrTy_static h)⟩
  | .arrow hs hd => fun t1 h => by
      cases h with
      | arrow ht he =>
        obtain ⟨t', ht', hte⟩ := precTy_to_agtPrecTy hs _ ht
        obtain ⟨e', he', hee⟩ := precD_to_agtPrecD hd _ he
        exact ⟨.arrow t' e', .arrow ht' he', .arrow hte hee⟩

/-- Lemma 5 (soundness of type precision), item 2, distribution types:
`D₁ ⊑ D₂` (inductive) implies `D₁ ⊑ᴬᴳᵀ D₂` (declarative). -/
theorem precD_to_agtPrecD {D1 D2 : FDist} :
    D1 ⊑ D2 → D1 ⊑ᴬᴳᵀ D2
  | .mk R fL fR hRty hcoup hfL hfR => by
    intro S1 hconcr
    cases hconcr with
    | @dist _ L1 p1 f1 hC1 hty1 hmass1 hnn1 hle1 hsurj1 =>
    obtain ⟨q, hqC, hw⟩ := hcoup p1 hC1
    -- the split of the concretization (`lift_split`) composed with the coupling
    -- of `PrecD`: a coupling `g` of the entry probabilities of `S1` and `q`
    obtain ⟨g, hg, hgs⟩ := (lift_split hnn1 hmass1).trans hw
      (T := fun k j => R (f1 k) j) fun k i j hki hij => by subst hki; exact hij
    -- Every entry `(k, j)` carries an equal copy of some entry of `S1`, recorded
    -- in `K`; it is a copy of entry `k` itself on the entry that left coverage
    -- reads (`j = fL (f1 k)`) and on every entry of positive weight.  All three
    -- branches feed the recursive call a precision proof taken from a field of
    -- the `PrecD` constructor, which is what the termination checker needs.
    have hb : ∀ k j, ∃ (b : Ty) (k' : Fin L1.length),
        FConcrTy (D2.ty j) b ∧ EqTy (L1.get k').1 b ∧
        (j = fL (f1 k) → k' = k) ∧ (0 < g k j → k' = k) := by
      intro k j
      by_cases hjl : j = fL (f1 k)
      · subst hjl
        obtain ⟨b, hbc, hbe⟩ :=
          precTy_to_agtPrecTy (hfL (f1 k)) (L1.get k).1 (hty1 k)
        exact ⟨b, k, hbc, hbe, fun _ => rfl, fun _ => rfl⟩
      · by_cases hpos : 0 < g k j
        · obtain ⟨b, hbc, hbe⟩ :=
            precTy_to_agtPrecTy (hRty (f1 k) j (hgs k j hpos)) (L1.get k).1 (hty1 k)
          exact ⟨b, k, hbc, hbe, fun _ => rfl, fun _ => rfl⟩
        · obtain ⟨k0, hk0⟩ := hsurj1 (fR j)
          obtain ⟨b, hbc, hbe⟩ :=
            precTy_to_agtPrecTy (hfR j) (L1.get k0).1 (hk0 ▸ hty1 k0)
          exact ⟨b, k0, hbc, hbe, fun h => absurd h hjl, fun h => absurd h hpos⟩
    choose B K hBc hBe hBl hBk using hb
    set E := (finProdFinEquiv : Fin L1.length × Fin D2.n ≃ Fin (L1.length * D2.n)) with hEdef
    -- the pairs of the grid, with weights `g`, have the entry probabilities of
    -- `S1` and the solution `q` as marginals
    obtain ⟨hrow, hcol⟩ := hg.restrict E.symm.injective
      fun k j _ => ⟨E (k, j), E.symm_apply_apply _⟩
    refine ⟨.dist (List.ofFn fun κ =>
        (B (E.symm κ).1 (E.symm κ).2, GProb.q (g (E.symm κ).1 (E.symm κ).2))), ?_, ?_⟩
    · -- the built list is a concretization of `D2`; an entry weighs at most its
      -- row, the probability of an entry of `S1`, hence at most 1
      refine fconcrD_ofFn_le (fun κ => B (E.symm κ).1 (E.symm κ).2)
        (fun κ => g (E.symm κ).1 (E.symm κ).2) q (fun κ => (E.symm κ).2) hqC
        (fun κ => hBc _ _) (fun j => ?_) (fun κ => hg.nonneg _ _)
        (fun κ => (hg.le_left _ _).trans (hle1 _)) (fun j => ?_)
      · rw [← pushfwd_eq_sum_filter, hcol]
      · -- non-empty blocks: `fR j` has an entry in `S1`, pair it with `j`
        obtain ⟨k0, _⟩ := hsurj1 (fR j)
        exact ⟨E (k0, j), by simp [hEdef]⟩
    · -- couple the given concretization of `D1` with the built one
      rw [map_eq_ofFn_get]
      refine eqD_ofFn_iff.2 ⟨?_, fun k => ⟨E (k, fL (f1 k)), ?_⟩,
        fun κ => ⟨K (E.symm κ).1 (E.symm κ).2, hBe _ _⟩⟩
      · -- every entry `(k, j)` goes to the entry `k` of `S1`; an entry of positive
        -- weight carries a copy of that entry
        have hl := Lift.pushfwd_of_pos (fun κ => (E.symm κ).1)
          (w := fun κ => g (E.symm κ).1 (E.symm κ).2)
          (R := fun κ k => EqTy (L1.get k).1 (B (E.symm κ).1 (E.symm κ).2))
          (fun κ => hg.nonneg _ _) fun κ hpos => by
            have hce := hBe (E.symm κ).1 (E.symm κ).2
            rwa [hBk _ _ hpos] at hce
        rw [hrow] at hl
        exact hl.symm
      · -- left coverage: the entry `(k, fL (f1 k))` carries a copy of entry `k`
        have hce := hBe k (fL (f1 k))
        rw [hBl k _ rfl] at hce
        simpa using hce
end

end GradualProb.GPLC
