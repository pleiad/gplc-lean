import GradualProb.GPLC.Typing
import GradualProb.TPLC.Witness

/-!
# TPLC: syntax, typing, operators on evidence, reduction and term precision

This module defines TPLC, the target language of Section 5: its syntax
(Figure 10), its type system (Figure 11) with Lemma 6, the meet operator
(consistent transitivity, Section 5.2) on formula types and on tagged
evidence, reordering (Definition 10) and the reordering initial evidence
(Definition 11), the distribution semantics (Figures 13 and 14), and the term
precision of TPLC (Figure 17). The metatheory of the operators and of the
semantics is in later modules (`TPLC/Meet`, `TPLC/Reorder`, `TPLC/TypeSafety`,
`TPLC/GradualGuarantee`).

## Main results

* `wf_val`, `wf_tm`: Lemma 6 (type well-formedness, TPLC); with `wf_raw`,
  Lemma 32 (well-formed types, TPLC).
* `det_raw`, `det_val`, `det_tm`: Lemma 36 (determinism of typing, TPLC).

## Reading guide

Syntax and typing come first, then the meet operator, Lemma 6, determinism,
renaming and substitution, reordering and the auxiliary refinement relation of
type safety, distribution configurations, the reordering initial evidence, the
reduction relation `Red`, and term precision.
-/

namespace GradualProb.TPLC

open GradualProb.GPLC

open scoped BigOperators

/-! ## Syntax (Figure 10)

Evidences are the tagged evidences of `TPLC/Evidence` (`TagTy`, `TagD`).
Variables are de Bruijn indices (see `GPLC.Tm`). The probability of a choice
is a `GProb` (a concrete probability or `?`), as in GPLC.

The body of a `let` is a family `Fin n → Tm` of `n` terms, one per entry of
the type of the bound term; the length `n` is part of the term, and the
rules that type, reduce or relate a `let` take it as a variable and write the
type of the bound term with its components, `⟨n, ty, C⟩`, as the article's
rules name the entries. (A rule stated over a type `D` with the family indexed
by `Fin D.n` could not be inverted on a `let` whose length is a numeral or
another type's `D'.n`.) -/

mutual
/-- Raw values `u`: a real, a boolean, or an annotated lambda. -/
inductive Raw : Type where
  | real : ℝ → Raw
  | bool : Bool → Raw
  | lam  : FTy → Tm → Raw
/-- Values `v`: a variable, an ascribed raw value `⟨ε u⟩ :: σ`, or a typed
error `error_σ`. -/
inductive Val : Type where
  | var : ℕ → Val
  | asc : TagTy → Raw → FTy → Val    -- `⟨ε u⟩ :: σ` : tagged evidence `ε`, type `σ`
  | err : FTy → Val                   -- `error_σ`
/-- Terms `m`. -/
inductive Tm : Type where
  | val    : Val → Tm
  | app    : Val → Val → Tm
  | letin  : Tm → (n : ℕ) → (Fin n → Tm) → Tm
      -- `let x = m in {nⱼ}ⱼ`: a family of `n` bodies, one per entry of the
      -- type of `m` (the typing rule fixes `n`)
  | choice : GProb → Tm → Tm → Tm   -- `m ⊕ᵖ n`
  | ascT   : TagD → Tm → FDist → Tm  -- `⟨ε m⟩ :: μ` : tagged evidence `ε`, type `μ`
  | ascV   : TagTy → Val → FTy → Tm  -- `⟨ε v⟩ :: σ'` (a term, of type `{σ'^1}`)
  | ite    : Val → Tm → Tm → Tm
  | add    : Val → Val → Tm
  | errD   : FDist → Tm               -- `error_μ`
end

/-! ## The type system (Figure 11)

`HasTyRaw Γ u σ`, `HasTyV Γ v σ` (values, simple types) and `HasTyT Γ m D`
(terms, distribution types). Only the ascription rules (`ascRaw`, `ascV`,
`ascT`) relate two types, through a valid evidence (Definition 9); all other
rules require the top-level constructors to agree. The configuration rule (GV)
is `DConfHasTy` in `TPLC/TypeSafety`. -/


mutual
/-- Typing of raw values: rules (Gr), (Gb) and (Gλ). -/
inductive HasTyRaw : List FTy → Raw → FTy → Prop where
  | real : ∀ {Γ r}, HasTyRaw Γ (.real r) .real
  | bool : ∀ {Γ b}, HasTyRaw Γ (.bool b) .bool
  | lam  : ∀ {Γ σ m D}, HasTyT (σ :: Γ) m D → GoodTy σ →
             HasTyRaw Γ (.lam σ m) (.arrow σ D)
/-- Typing of values: rules (Gx), (Gu::σ) and (Gerr_σ). -/
inductive HasTyV : List FTy → Val → FTy → Prop where
  | var    : ∀ {Γ x σ}, Γ[x]? = some σ → HasTyV Γ (.var x) σ
  -- (Gu::σ): `ε` is valid for `σu ∼̇ σ` and well-formed, `σ` is well-formed
  | ascRaw : ∀ {Γ} {ε : TagTy} {u σu σ}, HasTyRaw Γ u σu → HVTagTy ε σu σ →
               GoodTy ε.toF → GoodTy σ →
               HasTyV Γ (.asc ε u σ) σ
  | err    : ∀ {Γ σ}, GoodTy σ → HasTyV Γ (.err σ) σ
/-- Typing of terms: the rules of Figure 11 with a distribution type. -/
inductive HasTyT : List FTy → Tm → FDist → Prop where
  -- (Gv)
  | val    : ∀ {Γ v σ}, HasTyV Γ v σ → HasTyT Γ (.val v) (pointF σ)
  -- (Gapp): top-level constructors match
  | app    : ∀ {Γ v w σ D}, HasTyV Γ v (.arrow σ D) → HasTyV Γ w σ →
               HasTyT Γ (.app v w) D
  -- (Glet): the bound term has a type `⟨n, ty, C⟩` with as many entries as
  -- the family has bodies, each body is typed under its entry, and the result
  -- is the weighted union `letSem` over all entries. The type is written with
  -- its components, as in the article's rule, so that the number of bodies
  -- `n` is a variable of the rule (see the section "Syntax").
  | letin  : ∀ {Γ m n} {ty : Fin n → FTy} {C : (Fin n → ℝ) → Prop}
               {ns : Fin n → Tm} {F : Fin n → FDist},
               HasTyT Γ m ⟨n, ty, C⟩ →
               (∀ i, HasTyT (ty i :: Γ) (ns i) (F i)) →
               HasTyT Γ (.letin m n ns) (letSem ⟨n, ty, C⟩ F)
  -- (G⊕) with a concrete probability
  | choice : ∀ {Γ m n D1 D2} {a : ℝ}, 0 ≤ a → a ≤ 1 →
               HasTyT Γ m D1 → HasTyT Γ n D2 →
               HasTyT Γ (.choice (.q a) m n) (chooseSem a D1 D2)
  -- (G⊕) with the unknown probability
  | choiceU : ∀ {Γ m n D1 D2}, HasTyT Γ m D1 → HasTyT Γ n D2 →
               HasTyT Γ (.choice .unk m n) (chooseSemU D1 D2)
  -- (G::μ): `ε` is valid for `D ∼̇ Db`. The type `D` of `m` is not stored in
  -- the term; it is unique (`det_tm`).
  | ascT   : ∀ {Γ} {ε : TagD} {m D Db}, HasTyT Γ m D → ε.HValidFor D Db →
               GoodD ε.toF → GoodD Db →
               HasTyT Γ (.ascT ε m Db) Db
  -- (G::σ): `ε` is valid for `σ ∼̇ σ'`; the result is the Dirac `{σ'^1}`
  | ascV   : ∀ {Γ} {ε : TagTy} {v σ σ'}, HasTyV Γ v σ → HVTagTy ε σ σ' →
               GoodTy ε.toF → GoodTy σ' →
               HasTyT Γ (.ascV ε v σ') (pointF σ')
  -- (Gif): the convex hull `D1 ⊕_? D2` of the branch types, as `choiceU`
  | ite    : ∀ {Γ v m n D1 D2}, HasTyV Γ v .bool →
               HasTyT Γ m D1 → HasTyT Γ n D2 →
               HasTyT Γ (.ite v m n) (chooseSemU D1 D2)
  -- (G+)
  | add    : ∀ {Γ v w}, HasTyV Γ v .real → HasTyV Γ w .real →
               HasTyT Γ (.add v w) (pointF .real)
  -- (Gerr_γ)
  | errD   : ∀ {Γ D}, GoodD D → HasTyT Γ (.errD D) D
end

/-- `Γ ⊢ u : σ`, the typing of raw values of TPLC (Figure 11). GPLC and TPLC
share the symbol; the language of the term picks the reading. -/
scoped notation:50 (name := hasTyRawStx) Γ:51 " ⊢ " u:51 " : " σ:51 => HasTyRaw Γ u σ
/-- `Γ ⊢ v : σ`, the typing of values of TPLC (Figure 11). -/
scoped notation:50 (name := hasTyVStx) Γ:51 " ⊢ " v:51 " : " σ:51 => HasTyV Γ v σ
/-- `Γ ⊢ m : D`, the typing of terms of TPLC (Figure 11). -/
scoped notation:50 (name := hasTyTStx) Γ:51 " ⊢ " m:51 " : " D:51 => HasTyT Γ m D
/-- `⊢ u : σ`, the typing of closed raw values of TPLC. -/
scoped notation:50 (name := hasTyRawClosedStx) "⊢ " u:51 " : " σ:51 => HasTyRaw [] u σ
/-- `⊢ v : σ`, the typing of closed values of TPLC. -/
scoped notation:50 (name := hasTyVClosedStx) "⊢ " v:51 " : " σ:51 => HasTyV [] v σ
/-- `⊢ m : D`, the typing of closed terms of TPLC. -/
scoped notation:50 (name := hasTyTClosedStx) "⊢ " m:51 " : " D:51 => HasTyT [] m D

/-! ## The meet operator (consistent transitivity)

Consistent transitivity coincides with the meet, `ε₁ ∘ ε₂ = ε₁ ⊓ ε₂`
(Section 5.2). On simple types the meet is defined by the clauses of the
article and is partial (`Option`). On distribution types it is the witness
construction `W_⊓(D₁, D₂)` of `TPLC/Witness`: one entry for each pair `(i, j)`
of entries whose simple meet is defined, that is, of runtime-consistent entries
(`EConsTy`, Figure 12, no coverage clauses), with that meet as its type, and as
formula the coupling condition between the two operands.

The article's meet on distribution types is partial: it is defined when its
formula is satisfiable. Here `meetD` is a total function returning a formula
type; definedness is stated separately, as satisfiability of its formula
(`meetD_sat_iff_econsD` in `TPLC/Meet`). At simple types definedness is a
`some` whose result is well-formed. The metatheory of the meet is in
`TPLC/Meet`. -/

open Classical

mutual
/-- The meet `σ ⊓ τ` of simple types (Section 5.2), `none` where the article's
clauses do not apply. At arrows it does not check that the codomain meet is
defined (satisfiable); see the section header. The codomain is `meetD D1 D2`,
written out because `meetD` is defined after this block. -/
noncomputable def meetTy : FTy → FTy → Option FTy
  | .real, .real => some .real
  | .bool, .bool => some .bool
  | .unk, t => some t
  | t, .unk => some t
  | .arrow s1 D1, .arrow s2 D2 =>
      match meetTy s1 s2 with
      | some s => some (.arrow s (witness EConsTy D1 D2 (meetDty D1 D2)))
      | none => none
  | _, _ => none
/-- The simple types of the entries of `D1 ⊓ D2`: the simple meet of the pair of
operand entries that each entry enumerates (the entry function of `meetD`; it is
the one component that recurses on the entries, so it is the one defined by
pattern matching). -/
noncomputable def meetDty : (D1 D2 : FDist) → Fin (liveK EConsTy D1 D2).card → FTy
  | .mk n1 ty1 C1, .mk n2 ty2 C2 => fun c =>
      (meetTy (ty1 (witnessL EConsTy ⟨n1, ty1, C1⟩ ⟨n2, ty2, C2⟩ c))
        (ty2 (witnessR EConsTy ⟨n1, ty1, C1⟩ ⟨n2, ty2, C2⟩ c))).getD .unk
end

/-- The meet `D1 ⊓ D2 = W_⊓(D1, D2)` of distribution types: the witness
construction on the runtime-consistent pairs, with the simple meet of each
pair as entry (`meetDty`). -/
noncomputable def meetD (D1 D2 : FDist) : FDist :=
  witness EConsTy D1 D2 (meetDty D1 D2)

/-- `σ ⊓ τ`, the meet of formula simple types (Section 5.2). It is partial:
`σ ⊓ τ = some ρ` reads as the article's `σ ⊓ τ = ρ`. The symbol is shared with
Mathlib's lattice infimum; the type of the operands picks the reading. -/
scoped infixl:69 (name := meetTyStx) " ⊓ " => meetTy
/-- `D1 ⊓ D2`, the meet of formula distribution types (Section 5.2), defined
in the article when its formula is satisfiable. -/
scoped infixl:69 (name := meetDStx) " ⊓ " => meetD

/-- The entry count of the meet is the number of runtime-consistent pairs. -/
@[simp] theorem meetD_n (D1 D2 : FDist) :
    (meetD D1 D2).n = (liveK EConsTy D1 D2).card := rfl

/-! ## The entries of the meet -/

/-- The pair of operand entries that an entry of `D1 ⊓ D2` enumerates. -/
noncomputable def meetCell (D1 D2 : FDist) (c : Fin (meetD D1 D2).n) : Fin D1.n × Fin D2.n :=
  witnessCell EConsTy D1 D2 c

/-- Left provenance tag of an entry of the meet: the index of the left operand's entry
it comes from. -/
noncomputable def meetDL (D1 D2 : FDist) (c : Fin (meetD D1 D2).n) : Fin D1.n :=
  (meetCell D1 D2 c).1

/-- Right provenance tag of an entry of the meet: the index of the right operand's
entry it comes from. -/
noncomputable def meetDR (D1 D2 : FDist) (c : Fin (meetD D1 D2).n) : Fin D2.n :=
  (meetCell D1 D2 c).2

/-- The meet, unfolded: the article's triple, with the coupling condition
between the operands as formula. -/
theorem meetD_eq (D1 D2 : FDist) :
    meetD D1 D2 = ⟨(liveK EConsTy D1 D2).card, meetDty D1 D2, fun w =>
      ∃ pp qq, D1.C pp ∧ D2.C qq ∧
        (∀ i, pushfwd (meetDL D1 D2) w i = pp i) ∧
        (∀ j, pushfwd (meetDR D1 D2) w j = qq j) ∧ (∀ c, 0 ≤ w c)⟩ := rfl

/-- Every entry of the meet pairs runtime-consistent operand entries. -/
theorem meetCell_cons (D1 D2 : FDist) (c : Fin (meetD D1 D2).n) :
    EConsTy (D1.ty (meetDL D1 D2 c)) (D2.ty (meetDR D1 D2 c)) :=
  witnessCell_prop EConsTy D1 D2 c

/-- The simple type of an entry of the meet is the simple meet of the operand
entries named by its tags. -/
theorem meetD_ty' (D1 D2 : FDist) (c : Fin (meetD D1 D2).n) :
    (meetD D1 D2).ty c
      = (meetTy (D1.ty (meetDL D1 D2 c)) (D2.ty (meetDR D1 D2 c))).getD .unk := by
  cases D1; cases D2; rfl

/-- `σ ⊓ ? = σ`. -/
@[simp] theorem meetTy_unk_right : ∀ (t : FTy), meetTy t .unk = some t
  | .real => rfl
  | .bool => rfl
  | .unk => rfl
  | .arrow _ _ => rfl

/-- The meet of two arrows is the arrow of the meets, defined when the meet of
the domains is. -/
@[simp] theorem meetTy_arrow (s1 s2 : FTy) (D1 D2 : FDist) :
    meetTy (.arrow s1 D1) (.arrow s2 D2)
      = (meetTy s1 s2).map (fun s => .arrow s (meetD D1 D2)) := by
  cases h : meetTy s1 s2 <;> simp [meetTy, h, meetD]

/-- Lemma 34 (consistency is definedness), simple types, forward direction: the
simple meet of runtime-consistent types is defined. -/
theorem cons_meetTy_isSome : ∀ {σ τ : FTy}, σ ∼̇ τ → (σ ⊓ τ).isSome
  | _, _, .real => rfl
  | _, _, .bool => rfl
  | _, _, .unkL => rfl
  | _, _, .unkR => by rw [meetTy_unk_right]; rfl
  | _, _, .arrow hs _ => by
      obtain ⟨s, hs_eq⟩ := Option.isSome_iff_exists.mp (cons_meetTy_isSome hs)
      simp only [meetTy, hs_eq, Option.isSome_some]


/-! ## The meet on tagged evidence

Consistent transitivity on tagged evidences, the operation the reduction rules
use. Its erasure is the meet of the erasures (`emeetD_toF`). It is the tagged
witness construction (`tagWitness`) on the erasures, with the tags composed as
in the article's definition of `W_f`: the entry `(i, j)` takes the left tag
`l i` of the left operand and the right tag `r j` of the right operand. -/

mutual
/-- The meet of tagged simple evidences (partial, as `meetTy`). The codomain
is `emeetD d1 d2`, written out because `emeetD` is defined after this block. -/
noncomputable def emeetTy : TagTy → TagTy → Option TagTy
  | .real, .real => some .real
  | .bool, .bool => some .bool
  | .unk, t => some t
  | t, .unk => some t
  | .arrow s1 d1, .arrow s2 d2 =>
      match emeetTy s1 s2 with
      | some s => some (.arrow s (tagWitness EConsTy d1.toF d2.toF (emeetDty d1 d2) d1.l d2.r))
      | none => none
  | _, _ => none
/-- The tagged simple types of the entries of `e1 ∘ e2`: the tagged simple meet
of the pair of operand entries that each entry enumerates (the entry function of
`emeetD`). -/
noncomputable def emeetDty : (e1 e2 : TagD) → Fin (liveK EConsTy e1.toF e2.toF).card → TagTy
  | .mk n1 ty1 C1 l1 r1, .mk n2 ty2 C2 l2 r2 => fun c =>
      (emeetTy
        (ty1 (witnessL EConsTy (TagD.mk n1 ty1 C1 l1 r1).toF (TagD.mk n2 ty2 C2 l2 r2).toF c))
        (ty2 (witnessR EConsTy (TagD.mk n1 ty1 C1 l1 r1).toF (TagD.mk n2 ty2 C2 l2 r2).toF c))
        ).getD .unk
end

/-- The meet of tagged distribution evidences: the tagged witness construction
on the erasures, with the entries `emeetDty` and the composed tags: the entry
`(i, j)` takes the left tag of `i` in `e1` and the right tag of `j` in `e2`.
Its number of entries and its formula are those of `meetD e1.toF e2.toF`,
definitionally. -/
noncomputable def emeetD (e1 e2 : TagD) : TagD :=
  tagWitness EConsTy e1.toF e2.toF (emeetDty e1 e2) e1.l e2.r

/-- `ε₁ ∘ ε₂`, consistent transitivity of tagged simple evidences
(Section 5.2), the meet of the evidences. It is partial: `ε₁ ∘ ε₂ = some ε`
reads as the article's `ε₁ ∘ ε₂ = ε`. The symbol is shared with function
composition; the type of the operands picks the reading. -/
scoped infixr:90 (name := emeetTyStx) " ∘ " => emeetTy
/-- `ξ₁ ∘ ξ₂`, consistent transitivity of tagged distribution evidences
(Section 5.2). -/
scoped infixr:90 (name := emeetDStx) " ∘ " => emeetD

/-- The tagged meet, unfolded: the number of entries and the formula of the
meet of the erasures, and the composed tags. -/
theorem emeetD_eq (e1 e2 : TagD) :
    emeetD e1 e2 = ⟨(meetD e1.toF e2.toF).n, emeetDty e1 e2, (meetD e1.toF e2.toF).C,
      fun c => e1.l (meetDL e1.toF e2.toF c), fun c => e2.r (meetDR e1.toF e2.toF c)⟩ := rfl

mutual
/-- Erasure of the tagged simple meet is the simple meet of the erasures. -/
theorem emeetTy_toF : ∀ (t1 t2 : TagTy),
    Option.map TagTy.toF (emeetTy t1 t2) = meetTy t1.toF t2.toF
  | .real, .real => rfl
  | .real, .bool => rfl
  | .real, .unk => rfl
  | .real, .arrow _ _ => rfl
  | .bool, .real => rfl
  | .bool, .bool => rfl
  | .bool, .unk => rfl
  | .bool, .arrow _ _ => rfl
  | .unk, .real => rfl
  | .unk, .bool => rfl
  | .unk, .unk => rfl
  | .unk, .arrow _ _ => rfl
  | .arrow _ _, .real => rfl
  | .arrow _ _, .bool => rfl
  | .arrow _ _, .unk => rfl
  | .arrow s1 d1, .arrow s2 d2 => by
      have hs := emeetTy_toF s1 s2
      have hd := emeetD_toF d1 d2
      cases hm : emeetTy s1 s2 with
      | none =>
          rw [hm] at hs
          simp only [emeetTy, meetTy, hm, ← hs, Option.map_none]
      | some s =>
          rw [hm] at hs
          simp only [emeetTy, meetTy, hm, ← hs, Option.map_some]
          show some (FTy.arrow s.toF (emeetD d1 d2).toF)
            = some (FTy.arrow s.toF (meetD d1.toF d2.toF))
          rw [hd]
/-- Erasure of the tagged distribution meet is the meet of the erasures. The
number of entries and the formula agree definitionally; the entries by
`emeetTy_toF`. -/
@[simp] theorem emeetD_toF : ∀ (e1 e2 : TagD),
    (emeetD e1 e2).toF = meetD e1.toF e2.toF
  | .mk n1 ty1 C1 l1 r1, .mk n2 ty2 C2 l2 r2 => by
      show witness EConsTy _ _ _ = witness EConsTy _ _ _
      congr 1
      funext c
      show ((emeetTy (ty1 _) (ty2 _)).getD .unk).toF
        = (meetTy ((ty1 _).toF) ((ty2 _).toF)).getD .unk
      rw [toF_getD_unk, emeetTy_toF]
end

/-- A defined tagged meet erases to a defined meet. -/
theorem emeetTy_toF_some {e1 e2 e3 : TagTy} (h : emeetTy e1 e2 = some e3) :
    meetTy e1.toF e2.toF = some e3.toF := by
  have he := emeetTy_toF e1 e2
  rw [h, Option.map_some] at he
  exact he.symm

/-- A defined meet of the erasures lifts to a defined tagged meet. -/
theorem emeetTy_some_of_meetTy {e1 e2 : TagTy} {t : FTy}
    (h : meetTy e1.toF e2.toF = some t) :
    ∃ e3, emeetTy e1 e2 = some e3 ∧ e3.toF = t := by
  have he := emeetTy_toF e1 e2
  rw [h] at he
  cases hm : emeetTy e1 e2 with
  | none => rw [hm, Option.map_none] at he; cases he
  | some e3 =>
      rw [hm, Option.map_some] at he
      exact ⟨e3, rfl, Option.some.inj he⟩

/-- The tagged meet is structurally defined when the erasures are
runtime-consistent. -/
theorem cons_emeetTy_isSome {e1 e2 : TagTy} (h : EConsTy e1.toF e2.toF) :
    ∃ e3, emeetTy e1 e2 = some e3 := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (cons_meetTy_isSome h)
  obtain ⟨e3, hm, -⟩ := emeetTy_some_of_meetTy ht
  exact ⟨e3, hm⟩

/-- `?` is a right unit of the tagged simple meet. -/
theorem emeetTy_unk_right : ∀ (e : TagTy), emeetTy e .unk = some e
  | .real => rfl
  | .bool => rfl
  | .unk => rfl
  | .arrow _ _ => rfl


/-! ## Type well-formedness (Lemma 6)

Under a well-formed environment, every well-typed TPLC term has a
well-formed type. The operators preserve well-formedness as in GPLC
(`GPLC.good_tm`), and the ascription rules carry the well-formedness of their
target type as a premise. -/

mutual
/-- Lemma 32 (well-formed types, TPLC), raw values: a raw value well-typed under
a well-formed environment has a well-formed type. -/
theorem wf_raw : ∀ {Γ} {u : Raw} {σ}, Γ ⊢ u : σ → CtxGood Γ → GoodTy σ
  | _, _, _, .real, _ => .real
  | _, _, _, .bool, _ => .bool
  | _, _, _, .lam hm hσ, hΓ =>
      .arrow hσ (wf_tm hm (ctxGood_cons hσ hΓ))
/-- Lemma 6 (type well-formedness, TPLC), item 1, also part of Lemma 32
(well-formed types, TPLC): a value well-typed under a well-formed environment
has a well-formed type. -/
theorem wf_val : ∀ {Γ} {v : Val} {σ}, Γ ⊢ v : σ → CtxGood Γ → GoodTy σ
  | _, _, _, .var hx, hΓ => ctxGood_get hΓ hx
  | _, _, _, .ascRaw _ _ _ hσ, _ => hσ
  | _, _, _, .err hσ, _ => hσ
/-- Lemma 6 (type well-formedness, TPLC), item 2, also part of Lemma 32
(well-formed types, TPLC): a term well-typed under a well-formed environment
has a well-formed type. -/
theorem wf_tm : ∀ {Γ} {m : Tm} {D}, Γ ⊢ m : D → CtxGood Γ → GoodD D
  | _, _, _, .val hv, hΓ => goodD_point (wf_val hv hΓ)
  | _, _, _, .app hv _, hΓ => by
      cases wf_val hv hΓ with
      | arrow _ hD => exact hD
  | _, _, _, @HasTyT.letin _ _ _ _ _ _ _ hm hbody, hΓ =>
      goodD_let (wf_tm hm hΓ) (fun i =>
        wf_tm (hbody i) (ctxGood_cons ((wf_tm hm hΓ).tys i) hΓ))
  | _, _, _, .choice ha0 ha1 hm hn, hΓ =>
      goodD_choose ha0 ha1 (wf_tm hm hΓ) (wf_tm hn hΓ)
  | _, _, _, .choiceU hm hn, hΓ =>
      goodD_chooseU (wf_tm hm hΓ) (wf_tm hn hΓ)
  | _, _, _, .ascT _ _ _ hDb, _ => hDb
  | _, _, _, .ascV _ _ _ hσ', _ => goodD_point hσ'
  | _, _, _, .ite _ hm hn, hΓ => goodD_chooseU (wf_tm hm hΓ) (wf_tm hn hΓ)
  | _, _, _, .add _ _, _ => goodD_point .real
  | _, _, _, .errD hD, _ => hD
end

/-! ## Determinism of TPLC typing

Every rule is determined by the shape of the term and its annotations, so the
judgment assigns at most one type. -/

mutual
/-- Lemma 36 (determinism of typing, TPLC), raw values: typing of raw values is
deterministic. -/
theorem det_raw : ∀ {Γ} {u : Raw} {σ1 σ2}, Γ ⊢ u : σ1 → Γ ⊢ u : σ2 → σ1 = σ2
  | _, _, _, _, .real, h2 => by cases h2 with | real => rfl
  | _, _, _, _, .bool, h2 => by cases h2 with | bool => rfl
  | _, _, _, _, .lam hm _, h2 => by
      cases h2 with
      | lam hm' _ => rw [det_tm hm hm']
/-- Lemma 36 (determinism of typing, TPLC), values: typing of values is
deterministic. -/
theorem det_val : ∀ {Γ} {v : Val} {σ1 σ2}, Γ ⊢ v : σ1 → Γ ⊢ v : σ2 → σ1 = σ2
  | _, _, _, _, .var hx, h2 => by
      cases h2 with
      | var hx' => exact Option.some.inj (hx.symm.trans hx')
  | _, _, _, _, .ascRaw _ _ _ _, h2 => by
      cases h2 with
      | ascRaw _ _ _ _ => rfl
  | _, _, _, _, .err _, h2 => by
      cases h2 with
      | err _ => rfl
/-- Lemma 36 (determinism of typing, TPLC), terms: typing of terms is
deterministic. -/
theorem det_tm : ∀ {Γ} {m : Tm} {D1 D2}, Γ ⊢ m : D1 → Γ ⊢ m : D2 → D1 = D2
  | _, _, _, _, .val hv, h2 => by
      cases h2 with
      | val hv' => rw [det_val hv hv']
  | _, _, _, _, .app hv _, h2 => by
      cases h2 with
      | app hv' _ =>
        injection det_val hv hv'
  | _, _, _, _, @HasTyT.letin _ _ _ _ _ _ F1 hm hbody, h2 => by
      cases h2 with
      | @letin _ _ _ ty2 C2 _ F2 hm2 hbody2 =>
        injection det_tm hm hm2 with _ hty hC
        subst hty hC
        congr 1
        funext j
        exact det_tm (hbody j) (hbody2 j)
  | _, _, _, _, .choice ha0 ha1 hm hn, h2 => by
      cases h2 with
      | choice _ _ hm' hn' => rw [det_tm hm hm', det_tm hn hn']
  | _, _, _, _, .choiceU hm hn, h2 => by
      cases h2 with
      | choiceU hm' hn' => rw [det_tm hm hm', det_tm hn hn']
  | _, _, _, _, .ascT _ _ _ _, h2 => by
      cases h2 with
      | ascT _ _ _ _ => rfl
  | _, _, _, _, .ascV _ _ _ _, h2 => by
      cases h2 with
      | ascV _ _ _ _ => rfl
  | _, _, _, _, .ite _ hm hn, h2 => by
      cases h2 with
      | ite _ hm' hn' => rw [det_tm hm hm', det_tm hn hn']
  | _, _, _, _, .add _ _, h2 => by
      cases h2 with
      | add _ _ => rfl
  | _, _, _, _, .errD _, h2 => by
      cases h2 with
      | errD _ => rfl
end

/-! ## Renaming and substitution

Single-variable substitution, used by rules (Dapp) and (Dlet). Both are
structurally recursive; on a `let` they map over the body family. -/

mutual
/-- Shift the de Bruijn indices `≥ c` of a raw value up by one. -/
def Raw.rename : Raw → ℕ → Raw
  | .real r, _ => .real r
  | .bool b, _ => .bool b
  | .lam σ m, c => .lam σ (m.rename (c+1))
/-- Shift the de Bruijn indices `≥ c` of a value up by one. -/
def Val.rename : Val → ℕ → Val
  | .var x, c => .var (if x < c then x else x+1)
  | .asc ε u σ, c => .asc ε (u.rename c) σ
  | .err σ, _ => .err σ
/-- Shift the de Bruijn indices `≥ c` of a term up by one. -/
def Tm.rename : Tm → ℕ → Tm
  | .val v, c => .val (v.rename c)
  | .app v w, c => .app (v.rename c) (w.rename c)
  | .letin m n ns, c => .letin (m.rename c) n (fun i => (ns i).rename (c+1))
  | .choice p m n, c => .choice p (m.rename c) (n.rename c)
  | .ascT ε m D, c => .ascT ε (m.rename c) D
  | .ascV ε v σ, c => .ascV ε (v.rename c) σ
  | .ite v m n, c => .ite (v.rename c) (m.rename c) (n.rename c)
  | .add v w, c => .add (v.rename c) (w.rename c)
  | .errD D, _ => .errD D
end

mutual
/-- Substitute the de Bruijn index `k` by the value `w` in a raw value (lifting
`w` under binders, decrementing higher indices). -/
def Raw.subst : Raw → ℕ → Val → Raw
  | .real r, _, _ => .real r
  | .bool b, _, _ => .bool b
  | .lam σ m, k, w => .lam σ (m.subst (k+1) (w.rename 0))
/-- Substitute the de Bruijn index `k` by the value `w` in a value. -/
def Val.subst : Val → ℕ → Val → Val
  | .var x, k, w => if x = k then w else if x > k then .var (x-1) else .var x
  | .asc ε u σ, k, w => .asc ε (u.subst k w) σ
  | .err σ, _, _ => .err σ
/-- Substitute the de Bruijn index `k` by the value `w` in a term. -/
def Tm.subst : Tm → ℕ → Val → Tm
  | .val v, k, w => .val (v.subst k w)
  | .app v u, k, w => .app (v.subst k w) (u.subst k w)
  | .letin m n ns, k, w => .letin (m.subst k w) n (fun i => (ns i).subst (k+1) (w.rename 0))
  | .choice pr m n, k, w => .choice pr (m.subst k w) (n.subst k w)
  | .ascT ε m D, k, w => .ascT ε (m.subst k w) D
  | .ascV ε v σ, k, w => .ascV ε (v.subst k w) σ
  | .ite v m n, k, w => .ite (v.subst k w) (m.subst k w) (n.subst k w)
  | .add v u, k, w => .add (v.subst k w) (u.subst k w)
  | .errD D, _, _ => .errD D
end

/-- `rename` on a `let` maps over the body family. -/
@[simp] theorem Tm.rename_letin (m : Tm) (n : ℕ) (ns : Fin n → Tm) (c : ℕ) :
    (Tm.letin m n ns).rename c = .letin (m.rename c) n (fun i => (ns i).rename (c + 1)) := rfl

/-- `subst` on a `let` maps over the body family. -/
@[simp] theorem Tm.subst_letin (m : Tm) (n : ℕ) (ns : Fin n → Tm) (k : ℕ) (w : Val) :
    (Tm.letin m n ns).subst k w
      = .letin (m.subst k w) n (fun i => (ns i).subst (k + 1) (w.rename 0)) := rfl

/-- Substitution of the innermost bound variable (index `0`). -/
@[reducible] def Tm.subst0 (m : Tm) (w : Val) : Tm := m.subst 0 w

/-! ## Reordering (Definition 10)

The reordering relation `=ʳ` on formula types. On distribution types it is the
coupling lifting of syntactic equality of entries: a positive weight forces
the two entries to be the same simple type. On arrows it is contravariant in
the domain. Like runtime consistency, it has no coverage clauses. -/

mutual
/-- Definition 10 (reordering), simple types. -/
inductive EReordTy : FTy → FTy → Prop where
  | real : EReordTy .real .real
  | bool : EReordTy .bool .bool
  | unk  : EReordTy .unk .unk
  | arrow : ∀ {s1 D1 s2 D2}, EReordTy s2 s1 → EReordD D1 D2 →
      EReordTy (.arrow s1 D1) (.arrow s2 D2)
/-- Definition 10 (reordering), distribution types: the lifting of equality
of entries to the two symbolic distributions (`SymLift`), that is, a coupling
of a solution of each formula supported on pairs of equal entries. -/
inductive EReordD : FDist → FDist → Prop where
  | mk : ∀ {D1 D2 : FDist},
      SymLift (fun i j => D1.ty i = D2.ty j) D1.C D2.C →
      EReordD D1 D2
end

/-- `σ =ʳ τ`, the reordering relation on formula simple types (Definition 10),
the article's `=` with an `r` above. -/
scoped infix:50 (name := eReordTyStx) " =ʳ " => EReordTy
/-- `D1 =ʳ D2`, the reordering relation on formula distribution types
(Definition 10). -/
scoped infix:50 (name := eReordDStx) " =ʳ " => EReordD

/-- The lifting clause of a reordering. -/
theorem EReordD.coup {D1 D2 : FDist} : EReordD D1 D2 →
    SymLift (fun i j => D1.ty i = D2.ty j) D1.C D2.C
  | .mk h => h

/-! ## Refinement

The relation by which type safety (Lemma 42) relates the computed type of the
result of a reduction to the type of the term. Where `=ʳ` couples some
solution of each side, refinement couples every solution of the left side
with some solution of the right side, so it composes with precision. It is
covariant in the domain of arrows. At distribution types with a satisfiable
left side it implies `=ʳ` (`ereordD_of_refDist`), the relation the article's type
safety states. -/

mutual
/-- Refinement of simple types. -/
inductive RefTy : FTy → FTy → Prop where
  | real : RefTy .real .real
  | bool : RefTy .bool .bool
  | unk  : RefTy .unk .unk
  | arrow : ∀ {s1 D1 s2 D2}, RefTy s1 s2 → RefDist D1 D2 →
      RefTy (.arrow s1 D1) (.arrow s2 D2)
/-- Refinement of distribution types: every solution of the left formula is
related to some solution of the right formula by the lifting of equality of
entries (`SymLiftAll`). -/
inductive RefDist : FDist → FDist → Prop where
  | mk : ∀ {D1 D2 : FDist},
      SymLiftAll (fun i j => D1.ty i = D2.ty j) D1.C D2.C →
      RefDist D1 D2
end

/-- Introduction form of `RefDist`. -/
theorem RefDist.intro {D1 D2 : FDist}
    (h : SymLiftAll (fun i j => D1.ty i = D2.ty j) D1.C D2.C) : RefDist D1 D2 :=
  .mk h

/-- The lifting clause of a refinement. -/
theorem RefDist.coup {D1 D2 : FDist} : RefDist D1 D2 →
    SymLiftAll (fun i j => D1.ty i = D2.ty j) D1.C D2.C
  | .mk h => h

/-- Refinement of a satisfiable type implies reordering (Definition 10). -/
theorem ereordD_of_refDist {D1 D2 : FDist} (hsat : ∃ p, D1.C p)
    (h : RefDist D1 D2) : EReordD D1 D2 :=
  .mk (h.coup.symLift hsat)

/-! Reordering is reflexive on well-formed types (the diagonal coupling). -/
mutual
/-- Reordering is reflexive on well-formed simple types. -/
theorem EReordTy.refl : ∀ {σ : FTy}, GoodTy σ → EReordTy σ σ
  | _, .real => .real
  | _, .bool => .bool
  | _, .unk => .unk
  | _, .arrow hs hD => .arrow (EReordTy.refl hs) (EReordD.refl hD)
/-- Reordering is reflexive on well-formed distribution types. -/
theorem EReordD.refl : ∀ {D : FDist}, GoodD D → EReordD D D
  | _, .mk hC _ => by
      obtain ⟨p, hp⟩ := hC.sat
      exact .mk (.refl hp (hC.nonneg p hp) fun _ => rfl)
end

/-! Reordering is symmetric (transpose the coupling). -/
mutual
/-- Reordering of simple types is symmetric. -/
theorem EReordTy.symm : ∀ {σ τ : FTy}, EReordTy σ τ → EReordTy τ σ
  | _, _, .real => .real
  | _, _, .bool => .bool
  | _, _, .unk => .unk
  | _, _, .arrow hs hD => .arrow (EReordTy.symm hs) (EReordD.symm hD)
/-- Reordering of distribution types is symmetric. -/
theorem EReordD.symm : ∀ {D1 D2 : FDist}, EReordD D1 D2 → EReordD D2 D1
  | _, _, .mk h => .mk (h.symm.mono fun _ _ => Eq.symm)
end

/-! ## Distribution configurations

The result of a reduction is a distribution configuration `⟨φ⟩ V`: a finite
family of values with symbolic probabilities, closed by a formula. -/

/-- A distribution configuration `⟨φ⟩ V`: `n` values and the formula `φ` over
their probabilities, as a set of solutions (as in `FDist`).

The article writes a configuration together with its type, `⊢ Φ ▷ 𝒱 : γ`
(rule (GV)). Here a configuration is just the triple; its type is not a
premise of the reduction rules but is computed from it (`DConf.confF`), and
the typing judgment of configurations (`DConfHasTy`, in `TPLC/TypeSafety`)
refers to that computed type. -/
structure DConf where
  n : ℕ
  val : Fin n → Val
  C : (Fin n → ℝ) → Prop

/-- The Dirac configuration `{v¹}`. -/
@[reducible] def DConf.point (v : Val) : DConf :=
  ⟨1, fun _ => v, fun p => p 0 = 1⟩

/-- `a·V₁ + (1−a)·V₂` at a concrete probability `a`, as built by rule (D⊕) for
a concrete annotation: the runtime counterpart of `chooseSem`. -/
def DConf.choose (a : ℝ) (V1 V2 : DConf) : DConf :=
  ⟨V1.n + V2.n, Fin.append V1.val V2.val,
    fun x => ∃ p q, V1.C p ∧ V2.C q ∧
      x = Fin.append (fun i => a * p i) (fun j => (1 - a) * q j)⟩

/-- `w₁·V₁ + w₂·V₂` for the unknown probability: the runtime counterpart of
`chooseSemU`. The fresh variables that rule (D⊕) introduces for the
probability of the choice are represented by an existential quantification
over `a ∈ [0,1]` inside the formula, separate for each application of the
rule. -/
def DConf.chooseU (V1 V2 : DConf) : DConf :=
  ⟨V1.n + V2.n, Fin.append V1.val V2.val,
    fun x => ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ ∃ p q, V1.C p ∧ V2.C q ∧
      x = Fin.append (fun i => a * p i) (fun j => (1 - a) * q j)⟩

/-- `Σ_k ω_k · V_k` with the weights ranging over the solutions of `W`: the
runtime counterpart of `letSem`, built by rule (Dlet). The formula of each
`V_k` is required only where `ω_k > 0`, as in the guarded conjunction of the
article's rule. -/
noncomputable def DConf.wsum {K : ℕ} (W : (Fin K → ℝ) → Prop)
    (V : Fin K → DConf) : DConf :=
  ⟨∑ k, (V k).n,
    fun c => (V (finSigmaFinEquiv.symm c).1).val (finSigmaFinEquiv.symm c).2,
    fun x => ∃ ω, W ω ∧ ∃ b : (k : Fin K) → Fin (V k).n → ℝ,
      (∀ k, 0 < ω k → (V k).C (b k)) ∧
      ∀ c, x c = ω (finSigmaFinEquiv.symm c).1 * b _ (finSigmaFinEquiv.symm c).2⟩

/-- `Σ_c ω_c · {wv c}`, a mixture of Dirac configurations: the values `wv c`
with formula `W`. The result of rule (D::μ). -/
def DConf.wsumPoint {K : ℕ} (W : (Fin K → ℝ) → Prop) (wv : Fin K → Val) : DConf :=
  ⟨K, wv, W⟩

/-- The outcomes of `a·V₁ + (1−a)·V₂`: those of `V₁` followed by those of `V₂`. -/
@[simp] theorem DConf.choose_n (a : ℝ) (V1 V2 : DConf) :
    (DConf.choose a V1 V2).n = V1.n + V2.n := rfl

/-- The outcomes of `w₁·V₁ + w₂·V₂`: those of `V₁` followed by those of `V₂`. -/
@[simp] theorem DConf.chooseU_n (V1 V2 : DConf) :
    (DConf.chooseU V1 V2).n = V1.n + V2.n := rfl

/-- A left outcome of `a·V₁ + (1−a)·V₂` is the corresponding outcome of `V₁`. -/
@[simp] theorem DConf.choose_val_castAdd (a : ℝ) (V1 V2 : DConf) (i : Fin V1.n) :
    (DConf.choose a V1 V2).val (Fin.castAdd V2.n i) = V1.val i := Fin.append_left _ _ _

/-- A right outcome of `a·V₁ + (1−a)·V₂` is the corresponding outcome of `V₂`. -/
@[simp] theorem DConf.choose_val_natAdd (a : ℝ) (V1 V2 : DConf) (j : Fin V2.n) :
    (DConf.choose a V1 V2).val (Fin.natAdd V1.n j) = V2.val j := Fin.append_right _ _ _

/-- A left outcome of `w₁·V₁ + w₂·V₂` is the corresponding outcome of `V₁`. -/
@[simp] theorem DConf.chooseU_val_castAdd (V1 V2 : DConf) (i : Fin V1.n) :
    (DConf.chooseU V1 V2).val (Fin.castAdd V2.n i) = V1.val i := Fin.append_left _ _ _

/-- A right outcome of `w₁·V₁ + w₂·V₂` is the corresponding outcome of `V₂`. -/
@[simp] theorem DConf.chooseU_val_natAdd (V1 V2 : DConf) (j : Fin V2.n) :
    (DConf.chooseU V1 V2).val (Fin.natAdd V1.n j) = V2.val j := Fin.append_right _ _ _

/-- The outcomes of `Σ_k ω_k · V_k`: the outcomes of every `V_k`, side by side. -/
@[simp] theorem DConf.wsum_n {K : ℕ} (W : (Fin K → ℝ) → Prop) (V : Fin K → DConf) :
    (DConf.wsum W V).n = ∑ k, (V k).n := rfl

/-- The outcomes of `Σ_c ω_c · {wv c}`: one per value. -/
@[simp] theorem DConf.wsumPoint_n {K : ℕ} (W : (Fin K → ℝ) → Prop) (wv : Fin K → Val) :
    (DConf.wsumPoint W wv).n = K := rfl

/-- The configuration of rule (Derr): one error per entry of `μ`, with the
formula of `μ`. -/
def DConf.errAt (μ : FDist) : DConf := ⟨μ.n, fun i => .err (μ.ty i), μ.C⟩

/-! ## Reordering initial evidence (Definition 11)

The operator `γ' ∥ γ` with which rules (Dlet) and (D::μ) compute their routing
evidence. On distribution types it is the witness construction
`W_{id₌}(γ', γ)` of `TPLC/Witness`: its entries are the pairs of equal operand
entries,
and its formula is the coupling condition. Restricting to equal entries leaves
no value without a branch because reduction does not introduce types
(`entriesIn_red`). Like the meet, the operator is partial (`Option`) on simple
types, and `reorderD` is a total function on distribution types; the article's
operator is defined when the formula is satisfiable, and that definedness is
stated separately (`reorderD_sat_iff_ereordD`). Its metatheory (Lemma 10) is
in `TPLC/Reorder`. -/

mutual
/-- Definition 11 (reordering initial evidence), simple types: base types and
`?` only with themselves, arrows componentwise. The codomain is
`reorderD D1 D2`, written out because `reorderD` is defined after this block. -/
noncomputable def reorderTy : FTy → FTy → Option FTy
  | .real, .real => some .real
  | .bool, .bool => some .bool
  | .unk, .unk => some .unk
  | .arrow s1 D1, .arrow s2 D2 =>
      match reorderTy s1 s2 with
      | some s => some (.arrow s (witness Eq D1 D2 (reorderDty D1 D2)))
      | none => none
  | _, _ => none
/-- The simple types of the entries of `D1 ∥ D2`: the simple reordering evidence
of the pair of operand entries that each entry enumerates (the entry function
of `reorderD`). -/
noncomputable def reorderDty : (D1 D2 : FDist) → Fin (liveK Eq D1 D2).card → FTy
  | .mk n1 ty1 C1, .mk n2 ty2 C2 => fun c =>
      (reorderTy (ty1 (witnessL Eq ⟨n1, ty1, C1⟩ ⟨n2, ty2, C2⟩ c))
        (ty2 (witnessR Eq ⟨n1, ty1, C1⟩ ⟨n2, ty2, C2⟩ c))).getD .unk
end

/-- Definition 11 (reordering initial evidence), distribution types:
`D1 ∥ D2 = W_{id₌}(D1, D2)`, the witness construction on the pairs of equal
entries, with the simple reordering evidence of each pair as entry
(`reorderDty`). -/
noncomputable def reorderD (D1 D2 : FDist) : FDist :=
  witness Eq D1 D2 (reorderDty D1 D2)

/-- `σ ∥ τ`, the reordering initial evidence of formula simple types
(Definition 11). The article draws it as `=` turned upright; `∥` (U+2225) is
the closest glyph that Mathlib's norm `‖·‖` leaves free. It is partial, as
`⊓`. -/
scoped infixl:69 (name := reorderTyStx) " ∥ " => reorderTy
/-- `D1 ∥ D2`, the reordering initial evidence of formula distribution types
(Definition 11), defined in the article when its formula is satisfiable. -/
scoped infixl:69 (name := reorderDStx) " ∥ " => reorderD

/-- The entry count of `∥` is the number of pairs of equal entries. -/
@[simp] theorem reorderD_n (D1 D2 : FDist) :
    (reorderD D1 D2).n = (liveK Eq D1 D2).card := rfl

/-- The pair of operand entries that an entry of `D1 ∥ D2` enumerates. -/
noncomputable def reorderCell (D1 D2 : FDist) (c : Fin (reorderD D1 D2).n) :
    Fin D1.n × Fin D2.n :=
  witnessCell Eq D1 D2 c

/-- Left provenance tag of an entry of `∥`: the index of the left operand's
entry it comes from. -/
noncomputable def reorderDL (D1 D2 : FDist) (c : Fin (reorderD D1 D2).n) : Fin D1.n :=
  (reorderCell D1 D2 c).1

/-- Right provenance tag of an entry of `∥`: the index of the right operand's
entry it comes from. -/
noncomputable def reorderDR (D1 D2 : FDist) (c : Fin (reorderD D1 D2).n) : Fin D2.n :=
  (reorderCell D1 D2 c).2

/-- The reordering initial evidence, unfolded: the article's triple, with the
coupling condition between the operands as formula. -/
theorem reorderD_eq (D1 D2 : FDist) :
    reorderD D1 D2 = ⟨(liveK Eq D1 D2).card, reorderDty D1 D2, fun w =>
      ∃ pp qq, D1.C pp ∧ D2.C qq ∧
        (∀ i, pushfwd (reorderDL D1 D2) w i = pp i) ∧
        (∀ j, pushfwd (reorderDR D1 D2) w j = qq j) ∧ (∀ c, 0 ≤ w c)⟩ := rfl

mutual
/-- The reordering initial evidence as a tagged evidence, simple types. The
codomain is `tagReorderD D1 D2`, written out because `tagReorderD` is defined
after this block. -/
noncomputable def tagReorderTy : FTy → FTy → Option TagTy
  | .real, .real => some .real
  | .bool, .bool => some .bool
  | .unk, .unk => some .unk
  | .arrow s1 D1, .arrow s2 D2 =>
      match tagReorderTy s1 s2 with
      | some s => some (.arrow s (tagWitness Eq D1 D2 (tagReorderDty D1 D2) Fin.val Fin.val))
      | none => none
  | _, _ => none
/-- The entries of the tagged `D1 ∥ D2` (the entry function of
`tagReorderD`). -/
noncomputable def tagReorderDty : (D1 D2 : FDist) → Fin (liveK Eq D1 D2).card → TagTy
  | .mk n1 ty1 C1, .mk n2 ty2 C2 => fun c =>
      (tagReorderTy (ty1 (witnessL Eq ⟨n1, ty1, C1⟩ ⟨n2, ty2, C2⟩ c))
        (ty2 (witnessR Eq ⟨n1, ty1, C1⟩ ⟨n2, ty2, C2⟩ c))).getD .unk
end

/-- The reordering initial evidence as a tagged distribution evidence: the
tagged witness construction on the pairs of equal entries, with the entries
`tagReorderDty` and the two projections of each pair as its left and right
tags. Its number of entries and its formula are those of `reorderD D1 D2`,
definitionally. -/
noncomputable def tagReorderD (D1 D2 : FDist) : TagD :=
  tagWitness Eq D1 D2 (tagReorderDty D1 D2) Fin.val Fin.val

/-- `σ ∥ᵗ τ`, the reordering initial evidence of formula simple types as a
tagged evidence. The article writes `∥` for both readings, since its evidences
always carry tags; Lean needs a second symbol because `reorderTy` and
`tagReorderTy` take the same arguments. -/
scoped infixl:69 (name := tagReorderTyStx) " ∥ᵗ " => tagReorderTy
/-- `D1 ∥ᵗ D2`, the reordering initial evidence of formula distribution types
as a tagged evidence: the routing evidence of rule (Dlet), and the left
operand of the routing evidence of rule (D::μ). -/
scoped infixl:69 (name := tagReorderDStx) " ∥ᵗ " => tagReorderD

/-- The tagged reordering evidence, unfolded: the number of entries and the
formula of `∥`, and the projections of each entry as tags. -/
theorem tagReorderD_eq (D1 D2 : FDist) :
    tagReorderD D1 D2 = ⟨(reorderD D1 D2).n, tagReorderDty D1 D2, (reorderD D1 D2).C,
      fun c => (reorderDL D1 D2 c).val, fun c => (reorderDR D1 D2 c).val⟩ := rfl

/-- The article's substitution `sub` (Figure 13): substituting an error does not
place it inside the body; the whole body becomes the error at the body's type
`γ`. -/
def Tm.subErr (n : Tm) (w : Val) (γ : FDist) : Tm :=
  match w with
  | .err _ => .errD γ
  | _ => n.subst0 w

/-- Substituting an error yields the error at the body's type. -/
@[simp] theorem Tm.subErr_err {n : Tm} {σ : FTy} {γ : FDist} :
    n.subErr (.err σ) γ = .errD γ := rfl

/-- Substituting an ascribed value is ordinary substitution. -/
@[simp] theorem Tm.subErr_asc {n : Tm} {ε : TagTy} {u : Raw} {σ : FTy}
    {γ : FDist} : n.subErr (.asc ε u σ) γ = n.subst0 (.asc ε u σ) := rfl


/-- The type a closed value displays: the annotation of an ascribed value or
of an error (`?` for a variable, which closed values do not contain). -/
@[reducible] def Val.tyEntry : Val → FTy
  | .asc _ _ σ => σ
  | .err σ => σ
  | .var _ => .unk

/-- The computed type of a configuration: the displayed types of its values,
with the configuration's own formula. The routed rules (Dlet) and (D::μ)
reorder this type against the static type of the term they reduce first. -/
@[reducible] def DConf.confF (V : DConf) : FDist :=
  ⟨V.n, fun i => (V.val i).tyEntry, V.C⟩

/-- The right tags of `e ∘ εd` are those of `εd`, so they name entries of the
type `μb` for which `εd` is right valid. -/
theorem emeetD_r_lt_of_hvalid {e εd : TagD} {μb : FDist} (h : HValid .r εd μb)
    (c : Fin (emeetD e εd).n) : (emeetD e εd).r c < μb.n :=
  h.tag_lt _

/-- The big-step reduction `m ⇓[k] V` of Figures 13 and 14.

The index `k` is a bound on the height of the derivation, used for induction;
the results quantify over it without constraint. Rule (Dmon) makes the
relation monotone in `k`.

The error rules of Figure 14 are (Derr::σ) (`eAscV`) and the four
error-propagation rules (Derr+) (`eAddL`), (+Derr) (`eAddR`), (Derr app)
(`eApp`) and (Derr if) (`eIte`): an error in a redex position reduces to the
error at the redex's type. The two outcomes of rules (D::σ) and (D::μ) are
separate constructors (`dascOk`/`dascErr`, `dascD`/`dascDErr`), each with all
the premises of its rule. -/
inductive Red : Tm → ℕ → DConf → Prop where
  | dv : ∀ {v}, Red (.val v) 1 (DConf.point v)
  -- (D⊕): both branches reduce; the weights stay symbolic, closed by the
  -- conjoined formula
  | dchoice : ∀ {a m n k1 k2 V1 V2}, 0 ≤ a → a ≤ 1 →
      Red m k1 V1 → Red n k2 V2 →
      Red (.choice (.q a) m n) (k1+k2+1) (DConf.choose a V1 V2)
  | dchoiceU : ∀ {m n k1 k2 V1 V2},
      Red m k1 V1 → Red n k2 V2 →
      Red (.choice .unk m n) (k1+k2+1) (DConf.chooseU V1 V2)
  | dadd : ∀ {ε1 : TagTy} {r1 : ℝ} {ε2 : TagTy} {r2 : ℝ} {ε3 : TagTy},
      emeetTy ε1 ε2 = some ε3 →
      Red (.add (.asc ε1 (.real r1) .real) (.asc ε2 (.real r2) .real)) 1
          (DConf.point (.asc ε3 (.real (r1+r2)) .real))
  | dmon : ∀ {m k V}, Red m k V → Red m (k+1) V
  | dit : ∀ {ε m n k V}, Red m k V →
      Red (.ite (.asc ε (.bool true) .bool) m n) (k+1) V
  | dif : ∀ {ε m n k V}, Red n k V →
      Red (.ite (.asc ε (.bool false) .bool) m n) (k+1) V
  | derr : ∀ {μ : FDist}, Red (.errD μ) 1 (DConf.errAt μ)
  -- (D::σ): the ascription succeeds when the composition `ε₁ ∘ ε₂` is
  -- defined, i.e. the meet exists structurally and is well-formed (its
  -- formula is satisfiable), and errs at the target type otherwise
  | dascOk : ∀ {ε1 : TagTy} {u σ} {ε2 : TagTy} {σ' ε3},
      emeetTy ε1 ε2 = some ε3 → GoodTy ε3.toF →
      Red (.ascV ε2 (.asc ε1 u σ) σ') 1 (DConf.point (.asc ε3 u σ'))
  | dascErr : ∀ {ε1 : TagTy} {u σ} {ε2 : TagTy} {σ'},
      ¬ (∃ ε3, emeetTy ε1 ε2 = some ε3 ∧ GoodTy ε3.toF) →
      Red (.ascV ε2 (.asc ε1 u σ) σ') 1 (DConf.point (.err σ'))
  -- (Dapp): the argument is coerced with the flipped domain of the evidence,
  -- and the ascribed body is run with the result substituted by `sub`
  | dapp : ∀ {ε : TagTy} {σ' m σa Dres v} {s : TagTy} {d : TagD} {k1 k2 w V},
      tagDom ε = some s → tagCod ε = some d →
      Red (.ascV s v σ') k1 (DConf.point w) →
      Red ((Tm.ascT d m Dres).subErr w Dres) k2 V →
      Red (.app (.asc ε (.lam σ' m) (.arrow σa Dres)) v) (k1+k2+1) V
  -- (Dlet): the routing evidence is `V.confF ∥ᵗ μ`, with `μ = ⟨n, ty, C⟩` the
  -- static type of the bound term. Its entry `c` pairs the outcome `reorderDL … c` of `V`
  -- with the entry `reorderDR … c` of `μ` (the article's `l(ω_c)` and
  -- `r(ω_c)`, read as indices): the rule coerces that outcome to that entry
  -- with the evidence of `c` and runs that entry's body; the result is the
  -- weighted sum `DConf.wsum` over the formula of the routing evidence
  | dlet : ∀ {m n} {ty : Fin n → FTy} {C : (Fin n → ℝ) → Prop} {ns : Fin n → Tm}
      {k1 k2} {V : DConf}
      {wv : Fin (tagReorderD V.confF ⟨n, ty, C⟩).n → Val}
      {Vk : Fin (tagReorderD V.confF ⟨n, ty, C⟩).n → DConf}
      {Fb : Fin (tagReorderD V.confF ⟨n, ty, C⟩).n → FDist},
      Red m k1 V → HasTyT [] m ⟨n, ty, C⟩ →
      (∀ c, Red (.ascV ((tagReorderD V.confF ⟨n, ty, C⟩).ty c)
        (V.val (reorderDL V.confF ⟨n, ty, C⟩ c)) (ty (reorderDR V.confF ⟨n, ty, C⟩ c))) 1
        (DConf.point (wv c))) →
      (∀ c, HasTyT [ty (reorderDR V.confF ⟨n, ty, C⟩ c)]
        (ns (reorderDR V.confF ⟨n, ty, C⟩ c)) (Fb c)) →
      (∀ c, Red ((ns (reorderDR V.confF ⟨n, ty, C⟩ c)).subErr (wv c) (Fb c)) k2 (Vk c)) →
      Red (.letin m n ns) (k1+k2+1) (DConf.wsum (tagReorderD V.confF ⟨n, ty, C⟩).toF.C Vk)
  -- (D::μ), first case: `εd` is valid for `μ ∼̇ μb` (Definition 9), with `μ`
  -- the static type of `m`, and the routing evidence is `(V.confF ∥ᵗ μ) ∘ εd`;
  -- the rule fires when its formula is satisfiable. Its entry `c` comes from
  -- the entry `meetDL … c` of the reordering, which names the outcome
  -- `reorderDL … (meetDL … c)` of `V`, and from the entry `meetDR … c` of
  -- `εd`, whose right tag is the right tag of `c` and names an entry of `μb`
  -- by the validity of `εd`. The rule coerces that outcome to that entry
  -- with the evidence of `c`
  | dascD : ∀ {εd : TagD} {m μ μb k1} {V : DConf}
      {wv : Fin (emeetD (tagReorderD V.confF μ) εd).n → Val}
      (hval : εd.HValidFor μ μb),
      Red m k1 V → HasTyT [] m μ →
      (∃ w, (emeetD (tagReorderD V.confF μ) εd).toF.C w) →
      (∀ c, Red (.ascV ((emeetD (tagReorderD V.confF μ) εd).ty c)
        (V.val (reorderDL V.confF μ (meetDL (tagReorderD V.confF μ).toF εd.toF c)))
        (μb.ty ⟨_, emeetD_r_lt_of_hvalid hval.2 c⟩)) 1 (DConf.point (wv c))) →
      Red (.ascT εd m μb) (k1+1)
        (DConf.wsumPoint (emeetD (tagReorderD V.confF μ) εd).toF.C wv)
  -- (D::μ), second case: under the same validity premise, the composition
  -- is undefined (its formula is unsatisfiable), and the term reduces to the
  -- error at the target type
  | dascDErr : ∀ {εd : TagD} {m μ μb k1} {V : DConf},
      εd.HValidFor μ μb →
      Red m k1 V → HasTyT [] m μ →
      ¬ (∃ w, (emeetD (tagReorderD V.confF μ) εd).toF.C w) →
      Red (.ascT εd m μb) (k1+1) (DConf.errAt μb)
  -- Error rules: an error in a redex position reduces to the error at the
  -- redex's type (for the conditional, the hull of the branch types)
  | eAscV : ∀ {ε : TagTy} {σ σ'},
      Red (.ascV ε (.err σ) σ') 1 (DConf.point (.err σ'))
  | eAddL : ∀ {σ w}, Red (.add (.err σ) w) 1 (DConf.point (.err .real))
  | eAddR : ∀ {v σ}, Red (.add v (.err σ)) 1 (DConf.point (.err .real))
  | eApp : ∀ {σa} {D : FDist} {w},
      Red (.app (.err (.arrow σa D)) w) 1 (DConf.errAt D)
  | eIte : ∀ {σ m n} {D1 D2 : FDist},
      HasTyT [] m D1 → HasTyT [] n D2 →
      Red (.ite (.err σ) m n) 1 (DConf.errAt (chooseSemU D1 D2))

/-- `m ⇓[k] V`, the reduction `m ⇓ₖ Φ ▷ 𝒱` of Figures 13 and 14: the
configuration `V` holds both the formula `Φ` and the distribution value `𝒱`. -/
scoped notation:50 (name := redStx) m:51 " ⇓[" k "] " V:51 => Red m k V

/-- Rule (Dlet) for a bound term of an abstract static type `μ` (`FDist` has no
definitional eta, so `dlet` cannot be applied to `μ` directly). -/
theorem Red.dlet' {m : Tm} {μ : FDist} {ns : Fin μ.n → Tm} {k1 k2 : ℕ} {V : DConf}
    {wv : Fin (tagReorderD V.confF μ).n → Val} {Vk : Fin (tagReorderD V.confF μ).n → DConf}
    {Fb : Fin (tagReorderD V.confF μ).n → FDist}
    (hm : Red m k1 V) (hty : HasTyT [] m μ)
    (hcell : ∀ c, Red (.ascV ((tagReorderD V.confF μ).ty c)
      (V.val (reorderDL V.confF μ c)) (μ.ty (reorderDR V.confF μ c))) 1 (DConf.point (wv c)))
    (hbty : ∀ c, HasTyT [μ.ty (reorderDR V.confF μ c)] (ns (reorderDR V.confF μ c)) (Fb c))
    (hbred : ∀ c, Red ((ns (reorderDR V.confF μ c)).subErr (wv c) (Fb c)) k2 (Vk c)) :
    Red (.letin m μ.n ns) (k1+k2+1) (DConf.wsum (tagReorderD V.confF μ).toF.C Vk) := by
  cases μ; exact .dlet hm hty hcell hbty hbred

/-- Rule (Glet) for a bound term of an abstract type `D` (`FDist` has no
definitional eta, so `letin` cannot be applied to `D` directly). -/
theorem HasTyT.letin' {Γ : List FTy} {m : Tm} {D : FDist} {ns : Fin D.n → Tm}
    {F : Fin D.n → FDist} (hm : HasTyT Γ m D)
    (hbody : ∀ i, HasTyT (D.ty i :: Γ) (ns i) (F i)) :
    HasTyT Γ (.letin m D.n ns) (letSem D F) := by
  cases D; exact .letin hm hbody

/-! ## Term precision (Figure 17)

The term precision of TPLC, used to state the dynamic gradual guarantee
(Theorem 5), and its lifting to distribution configurations (rule (⊑V)). -/

/- The judgment `Γ ⊑ Γ' ⊢ m ⊑ m'` is `PrecT Γ Γ' m m'`, for arbitrary `Γ` and
`Γ'`; the relation `Γ ⊑ Γ'` is a hypothesis of the results that need it. The
premises of the ascription rules (and of the `let` rule) on the type of a
subterm are required for every type of that subterm; since typing is
deterministic (`det_tm`), they coincide with the article's premises on
well-typed terms and hold vacuously on ill-typed ones. -/
mutual
/-- Term precision on raw values. -/
inductive PrecRaw : List FTy → List FTy → Raw → Raw → Prop where
  | real : ∀ {Γ Γ' r}, PrecRaw Γ Γ' (.real r) (.real r)
  | bool : ∀ {Γ Γ' b}, PrecRaw Γ Γ' (.bool b) (.bool b)
  | lam  : ∀ {Γ Γ' σ σ' m m'}, PrecTy σ σ' → PrecT (σ :: Γ) (σ' :: Γ') m m' →
             PrecRaw Γ Γ' (.lam σ m) (.lam σ' m')
/-- Term precision on values. -/
inductive PrecV : List FTy → List FTy → Val → Val → Prop where
  | var  : ∀ {Γ Γ' x}, PrecV Γ Γ' (.var x) (.var x)
  -- The evidences are compared by tag-aware precision `⊢[.r]` against the
  -- annotations, and by `⊢[.l]` against the types of the raw values in `Γ`,
  -- `Γ'
  | asc  : ∀ {Γ Γ'} {ε ε' : TagTy} {u u' σ σ'},
             TagPrecTy .r σ σ' ε ε' →
             (∀ {σv σv' : FTy}, HasTyRaw Γ u σv → HasTyRaw Γ' u' σv' →
               TagPrecTy .l σv σv' ε ε') →
             PrecRaw Γ Γ' u u' → PrecTy σ σ' →
             PrecV Γ Γ' (.asc ε u σ) (.asc ε' u' σ')
  -- An error is below any value of a less precise type
  | errV : ∀ {Γ Γ' σ σ' v'}, HasTyV Γ' v' σ' → PrecTy σ σ' →
             PrecV Γ Γ' (.err σ) v'
/-- Term precision `Γ ⊑ Γ' ⊢ m ⊑ m'` (Figure 17). -/
inductive PrecT : List FTy → List FTy → Tm → Tm → Prop where
  | val    : ∀ {Γ Γ' v v'}, PrecV Γ Γ' v v' → PrecT Γ Γ' (.val v) (.val v')
  | app    : ∀ {Γ Γ' v v' w w'}, PrecV Γ Γ' v v' → PrecV Γ Γ' w w' →
               PrecT Γ Γ' (.app v w) (.app v' w')
  -- The `let` pairs bodies by the types of their branches: every pair of
  -- precision-related entries of the bound term types relates the
  -- corresponding bodies, under the binder of their branch, and the bound term
  -- types are related by the lifting of precision on their entries
  | letin  : ∀ {Γ Γ'} {m m' : Tm} {n n' : ℕ} {ns : Fin n → Tm} {ns' : Fin n' → Tm},
               PrecT Γ Γ' m m' →
               (∀ {D D' : FDist}, HasTyT Γ m D → HasTyT Γ' m' D' →
                 ∀ (i : Fin D.n) (j : Fin D'.n),
                   PrecTy (D.ty i) (D'.ty j) →
                   ∀ (hi : i.val < n) (hj : j.val < n'),
                     PrecT (D.ty i :: Γ) (D'.ty j :: Γ')
                       (ns ⟨i.val, hi⟩) (ns' ⟨j.val, hj⟩)) →
               (∀ {D D' : FDist}, HasTyT Γ m D → HasTyT Γ' m' D' →
                 SymLiftAll (fun i j => PrecTy (D.ty i) (D'.ty j)) D.C D'.C) →
               PrecT Γ Γ' (.letin m n ns) (.letin m' n' ns')
  | choice : ∀ {Γ Γ' p p' m m' n n'}, GPLC.PrecP p p' →
               PrecT Γ Γ' m m' → PrecT Γ Γ' n n' →
               PrecT Γ Γ' (.choice p m n) (.choice p' m' n')
  | ascT   : ∀ {Γ Γ'} {εd εd' : TagD} {m n γa γb},
               (∀ {D D' : FDist}, HasTyT Γ m D → HasTyT Γ' n D' →
                 TagPrecD .r εd εd' γa γb) →
               (∀ {D D' : FDist}, HasTyT Γ m D → HasTyT Γ' n D' →
                 TagPrecD .l εd εd' D D') →
               PrecT Γ Γ' m n → PrecD γa γb →
               PrecT Γ Γ' (.ascT εd m γa) (.ascT εd' n γb)
  | ascV   : ∀ {Γ Γ'} {ε ε' : TagTy} {v v' σ σ'},
               TagPrecTy .r σ σ' ε ε' →
               (∀ {σv σv' : FTy}, HasTyV Γ v σv → HasTyV Γ' v' σv' →
                 TagPrecTy .l σv σv' ε ε') →
               PrecV Γ Γ' v v' → PrecTy σ σ' →
               PrecT Γ Γ' (.ascV ε v σ) (.ascV ε' v' σ')
  | ite    : ∀ {Γ Γ' v v' m m' n n'}, PrecV Γ Γ' v v' →
               PrecT Γ Γ' m m' → PrecT Γ Γ' n n' →
               PrecT Γ Γ' (.ite v m n) (.ite v' m' n')
  | add    : ∀ {Γ Γ' v v' w w'}, PrecV Γ Γ' v v' → PrecV Γ Γ' w w' →
               PrecT Γ Γ' (.add v w) (.add v' w')
  | errD   : ∀ {Γ Γ' γ γ'}, PrecD γ γ' → PrecT Γ Γ' (.errD γ) (.errD γ')
end

/-- `Γ ⊑ Γ' ⊢ u ⊑ u'`, term precision on raw values of TPLC (Figure 17). -/
scoped notation:50 (name := precRawStx) Γ:51 " ⊑ " Γ':51 " ⊢ " u:51 " ⊑ " u':51 =>
  PrecRaw Γ Γ' u u'
/-- `Γ ⊑ Γ' ⊢ v ⊑ v'`, term precision on values of TPLC (Figure 17). -/
scoped notation:50 (name := precVStx) Γ:51 " ⊑ " Γ':51 " ⊢ " v:51 " ⊑ " v':51 =>
  PrecV Γ Γ' v v'
/-- `Γ ⊑ Γ' ⊢ m ⊑ m'`, term precision on terms of TPLC (Figure 17). -/
scoped notation:50 (name := precTStx) Γ:51 " ⊑ " Γ':51 " ⊢ " m:51 " ⊑ " m':51 =>
  PrecT Γ Γ' m m'
/-- `u ⊑ u'`, term precision on closed raw values of TPLC, as the article
writes it for closed terms. -/
scoped infix:50 (name := precRawClosedStx) " ⊑ " => PrecRaw [] []
/-- `v ⊑ v'`, term precision on closed values of TPLC. -/
scoped infix:50 (name := precVClosedStx) " ⊑ " => PrecV [] []
/-- `m ⊑ m'`, term precision on closed terms of TPLC. -/
scoped infix:50 (name := precTClosedStx) " ⊑ " => PrecT [] []

/-- Rule (⊑V), precision of distribution configurations: every solution of the
more precise formula is related to some solution of the less precise one by
the lifting (`SymLiftAll`) of precision of values under empty environments. -/
def DConfPrec (V1 V2 : DConf) : Prop :=
  SymLiftAll (fun i j => V1.val i ⊑ V2.val j) V1.C V2.C

/-- `V ⊑ V'`, precision of distribution configurations (rule (⊑V)). -/
scoped infix:50 (name := dConfPrecStx) " ⊑ " => DConfPrec

/-- Lemma 50 (precision of configurations is a congruence), item 1: Dirac
configurations of related values are related. -/
theorem dconfprec_point {v v' : Val} (h : v ⊑ v') :
    DConf.point v ⊑ DConf.point v' :=
  fun _ hp => ⟨fun _ => 1, rfl, .point hp rfl h⟩

end GradualProb.TPLC
