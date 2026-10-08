import GradualProb.GPLC.WellFormedness

/-!
# The terms of GPLC

The term syntax of GPLC (values `Val` and terms `Tm`, Figure 4), the precision
`PrecP` on gradual probabilities used by term precision at a probabilistic
choice (Figure 9), and the well-formedness `WfAnnV`/`WfAnnT` of the type
annotations of a term (Definition 14 applied to every annotation).
-/

namespace GradualProb.GPLC

open scoped BigOperators
open Classical

/- Values `Val` and terms `Tm` of GPLC (Figure 4), in A-normal form: application,
the conditional and addition take values. Variables are de Bruijn indices: `var k`
refers to the `k`-th enclosing binder, and `lam` and the body of `letin` bind
index `0`. The same syntax holds the terms of SPLC, as the terms whose
annotations are static (`SPLC.IsStaticTm`). -/
mutual
/-- Values of GPLC. -/
inductive Val where
  | var  : ℕ → Val
  | real : ℝ → Val
  | bool : Bool → Val
  | lam  : Ty → Tm → Val
/-- Terms of GPLC. -/
inductive Tm where
  | val    : Val → Tm
  | app    : Val → Val → Tm
  | letin  : Tm → Tm → Tm
  | choice : GProb → Tm → Tm → Tm
  | ascT   : Tm → DTy → Tm
  | ascV   : Val → Ty → Tm
  | ite    : Val → Tm → Tm → Tm
  | add    : Val → Val → Tm
end


/-- Precision on gradual probabilities: `ρ ⊑ ρ` and `ρ ⊑ ?`. -/
inductive PrecP : GProb → GProb → Prop where
  | refl : ∀ {p}, PrecP p p
  | unk  : ∀ {p}, PrecP p .unk

/-- `ρ ⊑ ρ'`, precision on gradual probabilities (Figure 9). -/
scoped infix:50 (name := precPStx) " ⊑ " => PrecP

/- Well-formedness of the annotations of a term: every type annotation is a
well-formed source gradual type (Definition 14). -/
mutual
/-- The annotations of a value are well-formed. -/
inductive WfAnnV : Val → Prop where
  | var  : ∀ {x}, WfAnnV (.var x)
  | real : ∀ {r}, WfAnnV (.real r)
  | bool : ∀ {b}, WfAnnV (.bool b)
  | lam  : ∀ {τ m}, WfTy τ → WfAnnT m → WfAnnV (.lam τ m)
/-- Definition 14 (well-formedness of source annotations), on terms: every
type annotation of the term is well-formed. -/
inductive WfAnnT : Tm → Prop where
  | val    : ∀ {v}, WfAnnV v → WfAnnT (.val v)
  | app    : ∀ {v w}, WfAnnV v → WfAnnV w → WfAnnT (.app v w)
  | letin  : ∀ {m n}, WfAnnT m → WfAnnT n → WfAnnT (.letin m n)
  | choice : ∀ {p m n}, WfAnnT m → WfAnnT n → WfAnnT (.choice p m n)
  | ascT   : ∀ {m T}, WfAnnT m → WfDTy T → WfAnnT (.ascT m T)
  | ascV   : ∀ {v τ}, WfAnnV v → WfTy τ → WfAnnT (.ascV v τ)
  | ite    : ∀ {v m n}, WfAnnV v → WfAnnT m → WfAnnT n → WfAnnT (.ite v m n)
  | add    : ∀ {v w}, WfAnnV v → WfAnnV w → WfAnnT (.add v w)
end


/-- Precision of gradual probabilities is sound for `γ_p`:
`ρ ⊑ ρ′ ⟹ γ_p(ρ) ⊆ γ_p(ρ′)`. -/
theorem gammaP_precP {p p' : GProb} {x : ℝ} (h : PrecP p p') (hx : GammaP p x) :
    GammaP p' x := by
  cases h with
  | refl => exact hx
  | unk => exact gammaP_mem_unit hx

end GradualProb.GPLC
