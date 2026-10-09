import GradualProb.GPLC.Typing
import GradualProb.SPLC.Typing

/-!
# Conservative extension of the static semantics

Theorem 3 (conservative extension of the static semantics): on the terms of
SPLC, the type systems of SPLC and of GPLC agree, and the types they assign
correspond by realization (Definition 7, `RealizesTy`/`RealizesD`). The module
defines the inclusion of SPLC terms into GPLC terms (`embedV`/`embedT`), shows
that the two notions of well-formedness agree on static types, defines
realization, and shows that each type operator of GPLC realizes the
corresponding operator of SPLC.

## Main results

* `static_conservative_extension_forward`, `static_conservative_extension_backward`,
  `static_conservative_extension`: Theorem 3, for closed terms;
  `conservative_forward_val`, `conservative_forward_tm`,
  `conservative_backward_val`, `conservative_backward_tm` for open values and
  terms, under a realizing context.
* `eq_of_cons_ty`, `eq_of_cons_d`, `cons_of_eq_ty`, `cons_of_eq_d`: Lemma 30
  (static equality and consistency), with `realizesTy_lift`/`realizesD_lift`;
  `cons_of_eq_d` and `realizesD_lift`, with `econsD_of_consD`
  (`GPLC/FormulaTypes`) and `TPLC.meetD_sat_iff_econsD`, give Lemma 31
  (equality defined).

## Reading guide

The operator lemmas (`realizes_point`, `realizes_choice`, `realizes_hull`,
`realizes_letRes`) and the closure of realization under `=ₛ` (`realizesD_eq`)
come first; each obtains the lifting of its conclusion from the liftings of its
hypotheses with the constructions of `GradualProb/Coupling.lean`. Then comes
the collapse of consistency to equality on realizing types, and finally the two
directions of Theorem 3, each proved by induction bounded by the size of the
term. The two directions share one `mutual` block but do not call each other:
each recurses only on itself.
-/


namespace GradualProb.GPLC

open GradualProb.SPLC
open scoped BigOperators


/-! ## Embedding SPLC into GPLC -/

/- The inclusion of SPLC terms into GPLC terms: the syntax is the same, and a
choice probability `p` becomes the known gradual probability `.q p`. SPLC is
thus the fragment of GPLC of the terms with static annotations
(`SPLC.IsStaticVal`/`SPLC.IsStaticTm`). -/
mutual
/-- Inclusion of SPLC values into GPLC values. -/
def embedV : SPLC.Val → Val
  | .var x => .var x
  | .real r => .real r
  | .bool b => .bool b
  | .lam τ m => .lam τ (embedT m)
/-- Inclusion of SPLC terms into GPLC terms. -/
def embedT : SPLC.Tm → Tm
  | .val v => .val (embedV v)
  | .app v w => .app (embedV v) (embedV w)
  | .letin m n => .letin (embedT m) (embedT n)
  | .choice p m n => .choice (.q p) (embedT m) (embedT n)
  | .ascT m T => .ascT (embedT m) T
  | .ascV v τ => .ascV (embedV v) τ
  | .ite v m n => .ite (embedV v) (embedT m) (embedT n)
  | .add v w => .add (embedV v) (embedV w)
end


/-! ## Static and gradual well-formedness agree on static types -/

/-- A static entry list whose probabilities sum to `1` has every probability at
most `1`. -/
theorem static_pval_le_one {es : List (Ty × GProb)} (hst : IsStaticEntries es)
    (hm : (es.map (fun e => pval e.2)).sum = 1) : ∀ e ∈ es, pval e.2 ≤ 1 := by
  intro e he
  have hnn : ∀ x ∈ es.map (fun e => pval e.2), 0 ≤ x := by
    intro x hx
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 hx
    exact pval_nonneg_mem hst e' he'
  have := List.single_le_sum hnn (pval e.2) (List.mem_map.2 ⟨e, he, rfl⟩)
  rwa [hm] at this


/-- The pointwise `pval` assignment concretizes a static entry list whose
probabilities are bounded by `1`. -/
theorem forall₂_gammaP_pval : ∀ {es : List (Ty × GProb)}, IsStaticEntries es →
    (∀ e ∈ es, pval e.2 ≤ 1) →
    List.Forall₂ GammaP (es.map Prod.snd) (es.map (fun e => pval e.2))
  | [], _, _ => .nil
  | e :: _, hst, hb => by
      obtain ⟨-, r, hp, hrnn⟩ := hst e List.mem_cons_self
      refine .cons ?_ (forall₂_gammaP_pval (List.forall_mem_cons.1 hst).2
        (fun e he => hb e (List.mem_cons_of_mem _ he)))
      show GammaP e.2 (pval e.2)
      rw [hp]
      exact ⟨rfl, hrnn⟩

/-- A static entry list whose probabilities sum to `1` is plausible. -/
theorem plausible_of_static_mass {es : List (Ty × GProb)} (hst : IsStaticEntries es)
    (hm : (es.map (fun e => pval e.2)).sum = 1) : Plausible es :=
  ⟨es.map (fun e => pval e.2), forall₂_gammaP_pval hst (static_pval_le_one hst hm), hm⟩

mutual
/-- A static type well-formed in SPLC (Definition 12) is well-formed as an
annotation (Definition 14). -/
theorem wfTy_of_static : ∀ {t : Ty}, IsStaticTy t → SPLC.WfTy t → WfTy t
  | _, .real, _ => .real
  | _, .bool, _ => .bool
  | _, .arrow hs hd, hw => by
      cases hw with
      | arrow hws hwd => exact .arrow (wfTy_of_static hs hws) (wfDTy_of_static hd hwd)
/-- A static distribution type well-formed in SPLC (Definition 12) is
well-formed as an annotation (Definition 14). -/
theorem wfDTy_of_static : ∀ {T : DTy}, IsStaticDTy T → SPLC.WfDTy T → WfDTy T
  | _, .dist ht hp, hw => by
      cases hw with
      | dist hwes hm =>
        exact .dist (fun e he => wfTy_of_static (ht e he) (hwes e he))
          (plausible_of_static_mass (fun e he => ⟨ht e he, hp e he⟩) hm)
end

/-- On a static entry list, a `γ_p`-pointwise witness list is forced to the
`pval`s (concrete probabilities have singleton concretizations). -/
theorem static_forall₂_pval : ∀ {es : List (Ty × GProb)} {ps : List ℝ},
    IsStaticEntries es → List.Forall₂ GammaP (es.map Prod.snd) ps →
    ps = es.map (fun e => pval e.2)
  | [], _, _, hf => by cases hf; rfl
  | e :: _, _, hst, hf => by
      obtain ⟨-, r, hp, -⟩ := hst e List.mem_cons_self
      rw [List.map_cons, hp] at hf
      cases hf with
      | cons hh htail =>
        obtain ⟨h1, -, -⟩ := hh
        subst h1
        rw [static_forall₂_pval (List.forall_mem_cons.1 hst).2 htail, List.map_cons, hp]
        rfl

mutual
/-- A static type well-formed as an annotation (Definition 14) is well-formed in
SPLC (Definition 12). -/
theorem splcWfTy_of_static : ∀ {t : Ty}, IsStaticTy t → WfTy t → SPLC.WfTy t
  | _, .real, _ => .real
  | _, .bool, _ => .bool
  | _, .arrow hs hd, hw => by
      cases hw with
      | arrow hws hwd => exact .arrow (splcWfTy_of_static hs hws) (splcWfDTy_of_static hd hwd)
/-- A static distribution type well-formed as an annotation (Definition 14) is
well-formed in SPLC (Definition 12). -/
theorem splcWfDTy_of_static : ∀ {T : DTy}, IsStaticDTy T → WfDTy T → SPLC.WfDTy T
  | _, .dist ht hp, hw => by
      cases hw with
      | dist hwes hpl =>
        refine .dist (fun e he => splcWfTy_of_static (ht e he) (hwes e he)) ?_
        obtain ⟨ps, hf, hsum⟩ := hpl
        rwa [static_forall₂_pval (fun e he => ⟨ht e he, hp e he⟩) hf] at hsum
end


/-! ## The realization relation -/

/- Definition 7 (realization): `RealizesTy σ τ` and `RealizesD D T` say that the
formula type realizes the static type. -/
mutual
/-- Definition 7 (realization), simple types. -/
inductive RealizesTy : FTy → Ty → Prop where
  | real : RealizesTy .real .real
  | bool : RealizesTy .bool .bool
  | arrow : ∀ {s τ d T}, RealizesTy s τ → RealizesD d T →
      RealizesTy (.arrow s d) (.arrow τ T)
/-- Definition 7 (realization), distribution types: the formula is satisfiable;
a relation `R` relates entries whose simple types realize each other and covers
the entries of both sides; and every solution is related to the static
probabilities by the lifting (`Lift`, Definition 2) of the relation that holds
of `(i, j)` when some pair `(i, j')` is in `R` with `j'` and `j` of equal
simple types. -/
inductive RealizesD : FDist → DTy → Prop where
  | dist : ∀ {D : FDist} {es : List (Ty × GProb)}
      (R : Fin D.n → Fin es.length → Prop),
      (∀ i j, R i j → RealizesTy (D.ty i) (es.get j).1) →
      (∀ i, ∃ j, R i j) →
      (∀ j, ∃ i, R i j) →
      (∃ p, D.C p) →
      (∀ p, D.C p → Lift (fun i j => ∃ j', R i j' ∧ EqTy (es.get j').1 (es.get j).1)
        p (fun j => pval (es.get j).2)) →
      RealizesD D (.dist es)
end

/-- `σ ⇝ τ`, the formula simple type `σ` realizes the static type `τ`
(Definition 7). -/
scoped infix:50 (name := realizesTyStx) " ⇝ " => RealizesTy
/-- `D ⇝ T`, the formula distribution type `D` realizes the static type `T`
(Definition 7). -/
scoped infix:50 (name := realizesDStx) " ⇝ " => RealizesD

/-- Introduction form of `RealizesD`, with the relation `R` taken to be
`RealizesTy` on the entry types. -/
theorem RealizesD.intro {D : FDist} {es : List (Ty × GProb)}
    (hcovL : ∀ i, ∃ j, RealizesTy (D.ty i) (es.get j).1)
    (hcovR : ∀ j, ∃ i, RealizesTy (D.ty i) (es.get j).1)
    (hsat : ∃ p, D.C p)
    (hc : ∀ p, D.C p →
      Lift (fun i j => ∃ j', RealizesTy (D.ty i) (es.get j').1 ∧
          EqTy (es.get j').1 (es.get j).1)
        p (fun j => pval (es.get j).2)) :
    RealizesD D (.dist es) :=
  RealizesD.dist (fun i j => RealizesTy (D.ty i) (es.get j).1) (fun _ _ h => h)
    hcovL hcovR hsat hc

/-- Left coverage of a realization: every entry of the formula type realizes
an entry of the static type. -/
theorem RealizesD.covL : ∀ {D : FDist} {T : DTy}, RealizesD D T →
    ∀ i, ∃ j, RealizesTy (D.ty i) ((dentries T).get j).1
  | _, _, .dist _ hR hcovL _ _ _, i => let ⟨j, hj⟩ := hcovL i; ⟨j, hR i j hj⟩

/-- Right coverage of a realization: every entry of the static type is
realized by an entry of the formula type. -/
theorem RealizesD.covR : ∀ {D : FDist} {T : DTy}, RealizesD D T →
    ∀ j, ∃ i, RealizesTy (D.ty i) ((dentries T).get j).1
  | _, _, .dist _ hR _ hcovR _ _, j => let ⟨i, hi⟩ := hcovR j; ⟨i, hR i j hi⟩

/-- The formula of a realizing type is satisfiable. -/
theorem RealizesD.sat : ∀ {D : FDist} {T : DTy}, RealizesD D T → ∃ p, D.C p
  | _, _, .dist _ _ _ _ hsat _ => hsat

/-- The lifting clause of a realization, stated on `RealizesTy`. -/
theorem RealizesD.coup : ∀ {D : FDist} {T : DTy}, RealizesD D T → ∀ p, D.C p →
    Lift (fun i j => ∃ j', RealizesTy (D.ty i) ((dentries T).get j').1 ∧
        EqTy ((dentries T).get j').1 ((dentries T).get j).1)
      p (fun j => pval ((dentries T).get j).2)
  | _, _, .dist _ hR _ _ _ hc, p, hp =>
      (hc p hp).mono fun i _ ⟨j', hr, he⟩ => ⟨j', hR i j' hr, he⟩

/-- Introduction form of `RealizesD` for a static type whose entries are
presented by a function: `e` lists the entries of `T` at the positions
`Fin N`, and the clauses of the realization are stated on `e`. -/
theorem RealizesD.ofFn {D : FDist} {T : DTy} {N : ℕ} (e : Fin N → Ty × GProb)
    (hN : (dentries T).length = N) (he : ∀ j, (dentries T).get j = e (Fin.cast hN j))
    (hcovL : ∀ i, ∃ j, RealizesTy (D.ty i) (e j).1)
    (hcovR : ∀ j, ∃ i, RealizesTy (D.ty i) (e j).1)
    (hsat : ∃ p, D.C p)
    (hc : ∀ p, D.C p →
      Lift (fun i j => ∃ j', RealizesTy (D.ty i) (e j').1 ∧ EqTy (e j').1 (e j).1)
        p (fun j => pval (e j).2)) :
    RealizesD D T := by
  obtain ⟨es⟩ := T
  subst hN
  obtain rfl : e = es.get := funext fun j => (he j).symm
  exact .intro hcovL hcovR hsat hc

/-- The entries of `l₁.map f ++ l₂.map g`, read at the positions of `l₁`
followed by those of `l₂`. -/
theorem get_map_append_map {α β : Type*} (f g : α → β) (l₁ l₂ : List α)
    (h : (l₁.map f ++ l₂.map g).length = l₁.length + l₂.length)
    (j : Fin (l₁.map f ++ l₂.map g).length) :
    (l₁.map f ++ l₂.map g).get j
      = Fin.append (fun k => f (l₁.get k)) (fun k => g (l₂.get k)) (Fin.cast h j) := by
  obtain ⟨j, rfl⟩ : ∃ j', j = Fin.cast h.symm j' := ⟨Fin.cast h j, rfl⟩
  induction j using Fin.addCases with
  | left k => simp [List.getElem_append_left]
  | right k => simp [List.getElem_append_right]

/-- Static entry lists carry concrete probabilities. -/
theorem isStaticEntries_get {es : List (Ty × GProb)} (h : IsStaticEntries es)
    (i : Fin es.length) : ∃ r, (es.get i).2 = GProb.q r :=
  let ⟨_, r, hr, _⟩ := h _ (List.get_mem es i); ⟨r, hr⟩


/-! ## The lifting of a well-formed static type realizes it -/

mutual
/-- Lemma 27 (lifting realizes), simple types: the lifting `⌈τ⌉` of a
well-formed static simple type `τ` realizes `τ`. -/
theorem realizesTy_lift : ∀ {τ : Ty}, IsStaticTy τ → WfTy τ → ⌈τ⌉ ⇝ τ
  | _, .real => fun _ => by simp only [liftFTy]; exact .real
  | _, .bool => fun _ => by simp only [liftFTy]; exact .bool
  | _, .arrow hs hd => fun hw => by
      cases hw with
      | arrow hws hwd =>
        simp only [liftFTy]
        exact .arrow (realizesTy_lift hs hws) (realizesD_lift hd hwd)
/-- Lemma 27 (lifting realizes), distribution types: the lifting `⌈T⌉` of a
well-formed static distribution type `T` realizes `T`. The only solution of the
lifted formula gives each entry its static probability, and the coupling is the
diagonal (`Lift.refl`). With `cons_of_eq_d`, `econsD_of_consD` and
`TPLC.meetD_sat_iff_econsD`, it also gives Lemma 31 (equality defined). -/
theorem realizesD_lift : ∀ {T : DTy}, IsStaticDTy T → WfDTy T → ⌈T⌉ ⇝ T
  | .dist es, .dist hst hsp => fun hw => by
      have hse : IsStaticEntries es := fun e he => ⟨hst e he, hsp e he⟩
      cases hw with
      | dist hwe hpl =>
        simp only [liftFDist]
        have hent : ∀ i, RealizesTy (liftFTy (es.get i).1) (es.get i).1 :=
          fun i => realizesTy_lift (hst _ (List.get_mem _ i)) (hwe _ (List.get_mem _ i))
        refine RealizesD.intro (fun i => ⟨i, hent i⟩)
          (fun j => ⟨j, hent j⟩) (plausible_fin hpl) ?_
        rintro p ⟨hg, _⟩
        have hp : ∀ j, p j = pval (es.get j).2 := fun j => by
          obtain ⟨r, hr⟩ := isStaticEntries_get hse j
          have hj := hg j
          rw [hr] at hj ⊢
          exact hj.1
        exact (Lift.refl (fun i => (gammaP_mem_unit (hg i)).1) fun i =>
          ⟨i, hent i, EqTy.refl (isStaticEntries_get_ty hse i)⟩).congr (fun _ => rfl) hp
end

/-! ## Realization of singleton types (the results of values, `ascV` and `add`) -/

/-- Lemma 29 (realization and the type operators), singleton types: if `σ`
realizes `τ`, then `[ω = 1] {{σ^ω}}` realizes `{{τ^1}}`. The coupling has the
single weight `1` (`Lift.point`). -/
theorem realizes_point {σ : FTy} {τ : Ty} (h : σ ⇝ τ) (hs : IsStaticTy τ) :
    pointF σ ⇝ .dist [(τ, .q 1)] := by
  refine RealizesD.intro (fun _ => ⟨(0 : Fin 1), h⟩) (fun j => ?_) ⟨fun _ => 1, rfl⟩
    fun _ hp => .point hp rfl ⟨(0 : Fin 1), h, EqTy.refl hs⟩
  obtain rfl : j = (0 : Fin 1) := Fin.fin_one_eq_zero j
  exact ⟨0, h⟩


/-! ## Realization of probabilistic choice -/

/-- Lemma 29 (realization and the type operators), probabilistic choice: if
`D₁` realizes `T₁` and `D₂` realizes `T₂`, then `chooseSem a D₁ D₂` realizes the
SPLC choice result `a·T₁ + (1−a)·T₂`. The coupling is `a` times the coupling of
the first realization on the first block and `1 − a` times the coupling of the
second on the second block (`Lift.smul`, `Lift.append`). -/
theorem realizes_choice {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {D1 D2 : FDist}
    {T1 T2 : DTy} (h1 : D1 ⇝ T1) (h2 : D2 ⇝ T2) :
    chooseSem a D1 D2 ⇝ addD (scaleD a T1) (scaleD (1 - a) T2) := by
  obtain ⟨es1⟩ := T1
  obtain ⟨es2⟩ := T2
  refine RealizesD.ofFn
    (Fin.append (fun k => ((es1.get k).1, GProb.q (a * pval (es1.get k).2)))
      (fun k => ((es2.get k).1, GProb.q ((1 - a) * pval (es2.get k).2))))
    (by simp [addD, scaleD]) (get_map_append_map _ _ es1 es2 _) ?_ ?_ ?_ ?_
  · intro i
    refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i
    · obtain ⟨j1, hj1⟩ := h1.covL i1
      exact ⟨Fin.castAdd _ j1, by simpa using hj1⟩
    · obtain ⟨j2, hj2⟩ := h2.covL i2
      exact ⟨Fin.natAdd _ j2, by simpa using hj2⟩
  · intro j
    refine Fin.addCases (fun j1 => ?_) (fun j2 => ?_) j
    · obtain ⟨i1, hi1⟩ := h1.covR j1
      exact ⟨Fin.castAdd _ i1, by simpa using hi1⟩
    · obtain ⟨i2, hi2⟩ := h2.covR j2
      exact ⟨Fin.natAdd _ i2, by simpa using hi2⟩
  · obtain ⟨p, hp⟩ := h1.sat
    obtain ⟨q, hq⟩ := h2.sat
    exact ⟨_, p, q, hp, hq, rfl⟩
  · rintro x ⟨p, q, hp, hq, rfl⟩
    refine (((h1.coup p hp).smul ha0).append ((h2.coup q hq).smul (sub_nonneg.2 ha1))
      ?_ ?_).congr (fun _ => rfl) fun j => ?_
    · rintro i j ⟨j', hr, he⟩
      exact ⟨Fin.castAdd _ j', by simpa using hr, by simpa using he⟩
    · rintro i j ⟨j', hr, he⟩
      exact ⟨Fin.natAdd _ j', by simpa using hr, by simpa using he⟩
    · induction j using Fin.addCases <;> simp


/-! ## Realization is closed under `=ₛ` on the static side -/

mutual
/-- Lemma 28 (realization and static equality), simple types: if `σ` realizes
`τ` and `τ =ₛ τ'`, then `σ` realizes `τ'`. -/
theorem realizesTy_eq : ∀ {σ : FTy} {τ τ' : Ty}, σ ⇝ τ → τ =ₛ τ' →
    σ ⇝ τ'
  | _, _, _, .real, hc => by cases hc; exact .real
  | _, _, _, .bool, hc => by cases hc; exact .bool
  | _, _, _, .arrow hs hd, hc => by
      cases hc with
      | arrow hcs hcd => exact .arrow (realizesTy_eq hs hcs) (realizesD_eq hd hcd)
/-- Lemma 28 (realization and static equality), distribution types: if `D`
realizes `T` and `T =ₛ T'`, then `D` realizes `T'`. The coupling of a solution
is the composition of the coupling of the realization with the coupling of
`T =ₛ T'` (`Lift.trans`). -/
theorem realizesD_eq : ∀ {D : FDist} {T T' : DTy}, D ⇝ T → T =ₛ T' →
    D ⇝ T'
  | _, _, .dist es', @RealizesD.dist D es R hR hcovL hcovR hsat hc, hceq => by
      obtain ⟨hcL, hcR⟩ := hceq.cov
      refine RealizesD.dist
        (fun i k => ∃ j, R i j ∧ EqTy (es.get j).1 (es'.get k).1) ?_ ?_ ?_ hsat ?_
      · rintro i k ⟨j, hij, hjk⟩
        exact realizesTy_eq (hR i j hij) hjk
      · intro i
        obtain ⟨j, hij⟩ := hcovL i
        obtain ⟨k, hjk⟩ := hcL j
        exact ⟨k, j, hij, hjk⟩
      · intro k
        obtain ⟨j, hjk⟩ := hcR k
        obtain ⟨i, hij⟩ := hcovR j
        exact ⟨i, j, hij, hjk⟩
      · intro p hp
        exact (hc p hp).trans hceq.coup fun i j k ⟨j', hij', he⟩ hjk =>
          ⟨k, ⟨j', hij', EqTy.trans he hjk⟩, EqTy.trans (EqTy.symm hjk) hjk⟩
end

/-! ## Realization of the conditional -/

/-- Lemma 29 (realization and the type operators), the conditional: when the
branches realize `=ₛ`-equal static types, the convex hull realizes the type of
the first branch, the type that rule (Tif) of SPLC assigns. The second branch
realizes the type of the first, since realization is closed under `=ₛ`
(`realizesD_eq`); the coupling of a solution `(t·p, (1−t)·q)` of the hull is `t`
times the coupling of the first branch above `1 − t` times the coupling of the
second (`Lift.smul`, `Lift.stack`). -/
theorem realizes_hull {D1 D2 : FDist} {T1 T2 : DTy}
    (h1 : D1 ⇝ T1) (h2 : D2 ⇝ T2) (hc : T2 =ₛ T1) (hs1 : IsStaticDTy T1) :
    chooseSemU D1 D2 ⇝ T1 := by
  have h2 : RealizesD D2 T1 := realizesD_eq h2 hc
  obtain ⟨es⟩ := T1
  refine RealizesD.intro ?_ ?_ ?_ ?_
  · intro i
    refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i
    · obtain ⟨j, hj⟩ := h1.covL i1
      exact ⟨j, by simpa using hj⟩
    · obtain ⟨j, hj⟩ := h2.covL i2
      exact ⟨j, by simpa using hj⟩
  · intro j
    obtain ⟨i, hi⟩ := h1.covR j
    exact ⟨Fin.castAdd _ i, by simpa using hi⟩
  · obtain ⟨p, hp⟩ := h1.sat
    obtain ⟨q, hq⟩ := h2.sat
    exact ⟨_, 1, zero_le_one, le_refl 1, p, q, hp, hq, rfl⟩
  · rintro x ⟨t, ht0, ht1, p, q, hp, hq, rfl⟩
    exact (((h1.coup p hp).smul ht0).stack ((h2.coup q hq).smul (sub_nonneg.2 ht1))
      (fun i j ⟨j', hr, he⟩ => ⟨j', by simpa using hr, he⟩)
      (fun i j ⟨j', hr, he⟩ => ⟨j', by simpa using hr, he⟩)).congr (fun _ => rfl)
      fun j => by ring

/-! ## Realization of `let` -/

/-- The number of entries of `letRes es Ts`: those of every `Ts j`, side by
side. -/
theorem letRes_length (es : List (Ty × GProb)) (Ts : Fin es.length → DTy) :
    (dentries (letRes es Ts)).length = ∑ j, (dentries (Ts j)).length :=
  dentries_sumScaled_length fun j => (pval (es.get j).2, Ts j)

/-- The entries of `letRes es Ts` on the dependent concatenation of the
positions of the `Ts j`: the entry at position `l` of the block `j` is the
`l`-th entry of `Ts j`, with its probability scaled by that of the `j`-th
entry of `es`. -/
def letResEntry (es : List (Ty × GProb)) (Ts : Fin es.length → DTy)
    (κ : Fin (∑ j, (dentries (Ts j)).length)) : Ty × GProb :=
  (((dentries (Ts (finSigmaFinEquiv.symm κ).1)).get (finSigmaFinEquiv.symm κ).2).1,
    GProb.q (pval (es.get (finSigmaFinEquiv.symm κ).1).2 *
      pval ((dentries (Ts (finSigmaFinEquiv.symm κ).1)).get (finSigmaFinEquiv.symm κ).2).2))

/-- The entry that `letResEntry` lists at a packed position. -/
theorem letResEntry_mk (es : List (Ty × GProb)) (Ts : Fin es.length → DTy)
    (j : Fin es.length) (l : Fin (dentries (Ts j)).length) :
    letResEntry es Ts (finSigmaFinEquiv ⟨j, l⟩)
      = (((dentries (Ts j)).get l).1,
          GProb.q (pval (es.get j).2 * pval ((dentries (Ts j)).get l).2)) := by
  rw [letResEntry, Equiv.symm_apply_apply]

/-- The entries of `letRes es Ts` are those that `letResEntry` lists. -/
theorem letRes_get (es : List (Ty × GProb)) (Ts : Fin es.length → DTy)
    (κ : Fin (dentries (letRes es Ts)).length) :
    (dentries (letRes es Ts)).get κ
      = letResEntry es Ts (Fin.cast (letRes_length es Ts) κ) := by
  have hv := @finSigmaFinEquiv_apply es.length (fun j => (dentries (Ts j)).length)
    (finSigmaFinEquiv.symm (Fin.cast (letRes_length es Ts) κ))
  rw [Equiv.apply_symm_apply] at hv
  exact dentries_sumScaled_getElem (fun j => (pval (es.get j).2, Ts j)) _ _ hv κ.isLt

/-- Lemma 29 (realization and the type operators), `let`: `letSem D F` realizes
the SPLC result `letRes es Ts`. The hypothesis `halign` (branch types at entries
of equal simple types are `=ₛ`) is the determinism of SPLC up to `=ₛ`,
`det_eq_tm`. For a pair `(i, j)` of positive weight in the coupling of the bound
term, `i`
has a partner `j'` with `Ts j' =ₛ Ts j`, so `F i` realizes `Ts j`
(`realizesD_eq`); the coupling of the result is the product of the coupling of
the bound term with the couplings of these realizations (`Lift.sigmaFin`). -/
theorem realizes_letRes {D : FDist} {es : List (Ty × GProb)} {F : Fin D.n → FDist}
    {Ts : Fin es.length → DTy}
    (hD : D ⇝ .dist es)
    (hF : ∀ i j, D.ty i ⇝ (es.get j).1 → F i ⇝ Ts j)
    (halign : ∀ j j', (es.get j).1 =ₛ (es.get j').1 → Ts j =ₛ Ts j') :
    letSem D F ⇝ letRes es Ts := by
  refine RealizesD.ofFn (letResEntry es Ts) (letRes_length es Ts) (letRes_get es Ts)
    ?_ ?_ ?_ ?_
  · -- left coverage: a partner `j` of the block, then a partner in `Ts j`
    intro κ
    obtain ⟨j, hj⟩ := hD.covL (finSigmaFinEquiv.symm κ).1
    obtain ⟨l, hl⟩ := (hF _ j hj).covL (finSigmaFinEquiv.symm κ).2
    exact ⟨finSigmaFinEquiv ⟨j, l⟩, by rw [letResEntry_mk]; exact hl⟩
  · -- right coverage
    intro κ'
    obtain ⟨i, hi⟩ := hD.covR (finSigmaFinEquiv.symm κ').1
    obtain ⟨k, hk⟩ := (hF i _ hi).covR (finSigmaFinEquiv.symm κ').2
    exact ⟨finSigmaFinEquiv ⟨i, k⟩, by rw [letSem_ty_mk]; exact hk⟩
  · -- satisfiability
    obtain ⟨p, hp⟩ := hD.sat
    have hbs : ∀ i, ∃ b, (F i).C b := fun i =>
      let ⟨j, hj⟩ := hD.covL i; (hF i j hj).sat
    choose b hb using hbs
    exact ⟨_, p, hp, b, hb, fun κ => rfl⟩
  · -- the coupling
    rintro x ⟨p, hp, b, hb, hx⟩
    obtain ⟨w, hw, hs⟩ := hD.coup p hp
    refine (Lift.sigmaFin hw hs (fun i j ⟨j', hr, he⟩ =>
      (realizesD_eq (hF i j' hr) (halign j' j he)).coup (b i) (hb i)) ?_).congr
      (fun κ => (hx κ).symm) fun κ' => ?_
    · rintro i j k l - ⟨l', hr, he⟩
      refine ⟨finSigmaFinEquiv ⟨j, l'⟩, ?_, ?_⟩
      · rw [letSem_ty_mk, letResEntry_mk]; exact hr
      · rw [letResEntry_mk, letResEntry_mk]; exact he
    · rw [← Finset.sum_mul, hw.col]; rfl


/-! ## Lemma 30 (static equality and consistency)

On realizing types, consistency is `=ₛ` of the realized types, in both
directions. -/

mutual
/-- Lemma 30 (static equality and consistency), simple types: consistency of
realizing types implies `=ₛ` of the realized types. -/
theorem eq_of_cons_ty : ∀ {σ1 σ2 : FTy} {τ1 τ2 : Ty},
    σ1 ∼ σ2 → σ1 ⇝ τ1 → σ2 ⇝ τ2 → τ1 =ₛ τ2
  | _, _, _, _, hc, .real, .real => .real
  | _, _, _, _, hc, .real, .bool => nomatch hc
  | _, _, _, _, hc, .real, .arrow _ _ => nomatch hc
  | _, _, _, _, hc, .bool, .real => nomatch hc
  | _, _, _, _, hc, .bool, .bool => .bool
  | _, _, _, _, hc, .bool, .arrow _ _ => nomatch hc
  | _, _, _, _, hc, .arrow _ _, .real => nomatch hc
  | _, _, _, _, hc, .arrow _ _, .bool => nomatch hc
  | _, _, _, _, hc, .arrow hs1 hd1, .arrow hs2 hd2 => by
      cases hc with
      | arrow hcs hcd =>
        exact .arrow (eq_of_cons_ty hcs hs1 hs2) (eq_of_cons_d hcd hd1 hd2)
/-- Lemma 30 (static equality and consistency), distribution types: if
`D₁ ∼ D₂`, `D₁` realizes `T₁` and `D₂` realizes `T₂`, then `T₁ =ₛ T₂`. The
coupling composes the transpose of the coupling of the first realization, the
coupling of the consistency and the coupling of the second realization
(`Lift.symm`, `Lift.comp`, `Lift.trans`). -/
theorem eq_of_cons_d : ∀ {D1 D2 : FDist} {T1 T2 : DTy},
    D1 ∼ D2 → D1 ⇝ T1 → D2 ⇝ T2 → T1 =ₛ T2
  | _, _, _, _, .mk Ru fLu fRu hRu hlu hufL hufR,
      @RealizesD.dist _ es1 R1 hR1 hcovL1 hcovR1 _ hc1,
      @RealizesD.dist _ es2 R2 hR2 hcovL2 hcovR2 _ hc2 => by
      obtain ⟨p, q, hp, hq, hl⟩ := hlu
      refine EqD.intro ?_ ⟨?_, ?_⟩
      · exact ((hc1 p hp).symm.comp hl).trans (hc2 q hq)
          fun _ i2 _ ⟨i, ⟨j1', hr1, he1⟩, hi⟩ ⟨j2', hr2, he2⟩ =>
            EqTy.trans (EqTy.symm he1) (EqTy.trans
              (eq_of_cons_ty (hRu i i2 hi) (hR1 i j1' hr1) (hR2 i2 j2' hr2)) he2)
      · -- coverage: go up to a realizing entry, cross by the coverage of
        -- consistency, go down by the realization of the other side
        intro j1
        obtain ⟨i, hij1⟩ := hcovR1 j1
        obtain ⟨j2, hij2⟩ := hcovL2 (fLu i)
        exact ⟨j2, eq_of_cons_ty (hufL i) (hR1 i j1 hij1) (hR2 (fLu i) j2 hij2)⟩
      · intro j2
        obtain ⟨i2, hij2⟩ := hcovR2 j2
        obtain ⟨j1, hij1⟩ := hcovL1 (fRu i2)
        exact ⟨j1, eq_of_cons_ty (hufR i2) (hR1 (fRu i2) j1 hij1) (hR2 i2 j2 hij2)⟩
end

mutual
/-- Lemma 30 (static equality and consistency), converse, simple types: `=ₛ`
of the realized types implies consistency of the realizing types. Used for the
consistency premises in the forward direction of Theorem 3. -/
theorem cons_of_eq_ty : ∀ {σ1 σ2 : FTy} {τ1 τ2 : Ty},
    σ1 ⇝ τ1 → τ1 =ₛ τ2 → σ2 ⇝ τ2 → σ1 ∼ σ2
  | _, _, _, _, .real, hc, h2 => by
      cases hc
      cases h2
      exact .real
  | _, _, _, _, .bool, hc, h2 => by
      cases hc
      cases h2
      exact .bool
  | _, _, _, _, .arrow hs1 hd1, hc, h2 => by
      cases hc with
      | arrow hcs hcd =>
        cases h2 with
        | arrow hs2 hd2 =>
          exact .arrow (cons_of_eq_ty hs1 hcs hs2) (cons_of_eq_d hd1 hcd hd2)
/-- Lemma 30 (static equality and consistency), converse, distribution types: if
`D₁` realizes `T₁`, `T₁ =ₛ T₂` and `D₂` realizes `T₂`, then `D₁ ∼ D₂`. The
coupling composes the coupling of the first realization, the coupling of
`T₁ =ₛ T₂` and the transpose of the coupling of the second realization
(`Lift.comp`, `Lift.symm`, `Lift.trans`). With `realizesD_lift`,
`econsD_of_consD` and `TPLC.meetD_sat_iff_econsD`, it also gives Lemma 31
(equality defined). -/
theorem cons_of_eq_d : ∀ {D1 D2 : FDist} {T1 T2 : DTy},
    D1 ⇝ T1 → T1 =ₛ T2 → D2 ⇝ T2 → D1 ∼ D2
  | _, _, _, _, @RealizesD.dist _ es1 R1 hR1 hcovL1 hcovR1 hsat1 hc1, hc, h2 => by
      cases h2 with
      | @dist _ es2 R2 hR2 hcovL2 hcovR2 hsat2 hc2 =>
      obtain ⟨p, hp⟩ := hsat1
      obtain ⟨q, hq⟩ := hsat2
      obtain ⟨hcL, hcR⟩ := hc.cov
      refine ConsD.intro ⟨p, q, hp, hq, ?_⟩ ⟨?_, ?_⟩
      · exact ((hc1 p hp).comp hc.coup).trans (hc2 q hq).symm
          fun i1 _ i2 ⟨_, ⟨j1', hr1, he1⟩, he⟩ ⟨j2', hr2, he2⟩ =>
            cons_of_eq_ty (hR1 i1 j1' hr1)
              (EqTy.trans he1 (EqTy.trans he (EqTy.symm he2))) (hR2 i2 j2' hr2)
      · -- coverage: go down to a realized entry, cross by the coverage of
        -- `EqD`, go up by the realization of the other side
        intro i1
        obtain ⟨j1, hij1⟩ := hcovL1 i1
        obtain ⟨j2, he⟩ := hcL j1
        obtain ⟨i2, hij2⟩ := hcovR2 j2
        exact ⟨i2, cons_of_eq_ty (hR1 i1 j1 hij1) he (hR2 i2 j2 hij2)⟩
      · intro i2
        obtain ⟨j2, hij2⟩ := hcovL2 i2
        obtain ⟨j1, he⟩ := hcR j2
        obtain ⟨i1, hij1⟩ := hcovR1 j1
        exact ⟨i1, cons_of_eq_ty (hR1 i1 j1 hij1) he (hR2 i2 j2 hij2)⟩
end


/-! ## Realizing contexts -/

/-- A context of formula types realizes a static context, pointwise. -/
def RealizesCtx (Φ : List FTy) (Γ : Ctx) : Prop := List.Forall₂ RealizesTy Φ Γ

/-- A variable bound in the static context is bound in a realizing formula
context, at a realizing type. -/
theorem realizesCtx_getElemS : ∀ {Φ : List FTy} {Γ : Ctx}, RealizesCtx Φ Γ →
    ∀ {x : ℕ} {τ : Ty}, Γ[x]? = some τ → ∃ σ, Φ[x]? = some σ ∧ RealizesTy σ τ
  | _, _, .nil, x, τ, hx => by simp at hx
  | _, _, .cons hab htail, x, τ, hx => by
      cases x with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨_, by simp, hab⟩
      | succ n =>
        simp only [List.getElem?_cons_succ] at hx
        obtain ⟨σ, h1, h2⟩ := realizesCtx_getElemS htail hx
        exact ⟨σ, by simpa using h1, h2⟩

/-- A variable bound in a formula context is bound in the static context it
realizes, at a realized type. -/
theorem realizesCtx_getElemF : ∀ {Φ : List FTy} {Γ : Ctx}, RealizesCtx Φ Γ →
    ∀ {x : ℕ} {σ : FTy}, Φ[x]? = some σ → ∃ τ, Γ[x]? = some τ ∧ RealizesTy σ τ
  | _, _, .nil, x, σ, hx => by simp at hx
  | _, _, .cons hab htail, x, σ, hx => by
      cases x with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨_, by simp, hab⟩
      | succ n =>
        simp only [List.getElem?_cons_succ] at hx
        obtain ⟨τ, h1, h2⟩ := realizesCtx_getElemF htail hx
        exact ⟨τ, by simpa using h1, h2⟩


/-! ## Theorem 3 (conservative extension of the static semantics)

Each direction is proved by induction on a natural number `k` that bounds the
size of the term. The two directions do not call each other: the forward
lemmas recurse only on forward lemmas and the backward ones only on backward
ones, so the `let` case of each direction uses its own induction hypothesis on
the body. The single `mutual` block and the index `k` are how the recursion is
packaged. -/

mutual
/-- Theorem 3, item 1, forward direction, for open values, with a size bound `k`. -/
theorem conservative_forward_val_bounded : ∀ (k : ℕ) {Γ : Ctx} {Φ : List FTy} {v : SPLC.Val} {τ : Ty},
    SPLC.HasTyV Γ v τ → RealizesCtx Φ Γ → CtxStatic Γ → CtxWf Γ → IsStaticVal v →
    sizeOf v ≤ k → ∃ σ, HasTyV Φ (embedV v) σ ∧ RealizesTy σ τ := by
  intro k Γ Φ v τ h hctx hΓs hΓw hsv hk
  cases h with
  | var hx =>
      obtain ⟨σ, h1, h2⟩ := realizesCtx_getElemS hctx hx
      exact ⟨σ, .var h1, h2⟩
  | real => exact ⟨.real, .real, .real⟩
  | bool => exact ⟨.bool, .bool, .bool⟩
  | @lam _ τa _ _ hm hτwf =>
      cases hsv with
      | lam hsτ hsm =>
        have hwτ : WfTy τa := wfTy_of_static hsτ hτwf
        have hlift := realizesTy_lift hsτ hwτ
        obtain ⟨D, hd, hr⟩ := conservative_forward_tm_bounded _ hm (.cons hlift hctx)
          (ctxStatic_cons hsτ hΓs) (ctxWf_cons hτwf hΓw) hsm (le_refl _)
        exact ⟨_, .lam hd hwτ, .arrow hlift hr⟩
termination_by k => k
decreasing_by
  all_goals simp only [SPLC.Val.lam.sizeOf_spec] at hk
  all_goals omega

/-- Theorem 3, item 2, forward direction, for open terms, with a size bound `k`: an
SPLC-typed term is GPLC-typed at a realizing formula type. In the `let` case,
every entry of the GPLC bound term type takes its body typing from its partner
under left coverage; the branch types are identified by determinism of GPLC
(`det_tm`) and aligned by determinism of SPLC up to `=ₛ` (`det_eq_tm`), and
`realizes_letRes` concludes. -/
theorem conservative_forward_tm_bounded : ∀ (k : ℕ) {Γ : Ctx} {Φ : List FTy} {m : SPLC.Tm} {T : DTy},
    SPLC.HasTyT Γ m T → RealizesCtx Φ Γ → CtxStatic Γ → CtxWf Γ → IsStaticTm m →
    sizeOf m ≤ k → ∃ D, HasTyT Φ (embedT m) D ∧ RealizesD D T := by
  intro k Γ Φ m T h hctx hΓs hΓw hs hk
  cases h with
  | val hv =>
      cases hs with
      | val hsv =>
        obtain ⟨σ, hv', hr⟩ := conservative_forward_val_bounded _ hv hctx hΓs hΓw hsv (le_refl _)
        exact ⟨_, .val hv', realizes_point hr (isStatic_val hv hΓs hsv)⟩
  | app hv hw hceq =>
      cases hs with
      | app hsv hsw =>
        obtain ⟨σv, hv', hrv⟩ := conservative_forward_val_bounded _ hv hctx hΓs hΓw hsv (le_refl _)
        cases hrv with
        | arrow hrs hrd =>
          obtain ⟨σw, hw', hrw⟩ := conservative_forward_val_bounded _ hw hctx hΓs hΓw hsw (le_refl _)
          exact ⟨_, .app hv' hw' .arrow
            (cons_of_eq_ty hrw (EqTy.symm hceq) hrs), hrd⟩
  | @letin _ mm nb es Tb hm hFst =>
      cases hs with
      | letin hsm hsn =>
        classical
        obtain ⟨D0, hm', hr0⟩ := conservative_forward_tm_bounded _ hm hctx hΓs hΓw hsm (le_refl _)
        have hesS : IsStaticEntries es := by
          exact (isStatic_tm hm hΓs hsm).entries
        have hesW := wfDTy_dist_inv (wf_tm hm hΓw)
        have hbctxS : ∀ j : Fin es.length, CtxStatic ((es.get j).1 :: Γ) :=
          fun j => ctxStatic_cons (isStaticEntries_get_ty hesS j) hΓs
        have hbctxW : ∀ j : Fin es.length, CtxWf ((es.get j).1 :: Γ) :=
          fun j => ctxWf_cons (hesW.1 _ (List.get_mem es j)) hΓw
        -- every entry of the GPLC bound term takes its body from the static
        -- entry it covers (left coverage of the realization)
        have hbody : ∀ i : Fin D0.n,
            ∃ Fi, HasTyT (D0.ty i :: Φ) (embedT nb) Fi := by
          intro i
          obtain ⟨j, hij⟩ := hr0.covL i
          obtain ⟨Fi, hFi, -⟩ := conservative_forward_tm_bounded _ (hFst j) (.cons hij hctx)
            (hbctxS j) (hbctxW j) hsn (le_refl _)
          exact ⟨Fi, hFi⟩
        choose Fb hFb using hbody
        refine ⟨letSem D0 Fb, HasTyT.letin hm' hFb, ?_⟩
        refine realizes_letRes hr0 ?_ ?_
        · -- bodies: recursion at each realizing pair, plus determinism of GPLC
          intro i j hstrict
          obtain ⟨T'', hd'', hr''⟩ := conservative_forward_tm_bounded _ (hFst j)
            (.cons hstrict hctx) (hbctxS j) (hbctxW j) hsn (le_refl _)
          rwa [det_tm hd'' (hFb i)] at hr''
        · -- branch alignment: determinism of SPLC up to `=ₛ`
          intro j j' hceq
          exact det_eq_tm (hFst j) (hFst j') (.cons hceq (eqCtx_refl hΓs))
            (hbctxS j) (hbctxS j') (hbctxW j) (hbctxW j') hsn
  | choice hm hn =>
      cases hs with
      | choice hp0 hp1 hsm hsn =>
        obtain ⟨D1, h1', hr1⟩ := conservative_forward_tm_bounded _ hm hctx hΓs hΓw hsm (le_refl _)
        obtain ⟨D2, h2', hr2⟩ := conservative_forward_tm_bounded _ hn hctx hΓs hΓw hsn (le_refl _)
        exact ⟨_, .choice hp0 hp1 h1' h2', realizes_choice hp0 hp1 hr1 hr2⟩
  | ascT hm hceq hwfS =>
      cases hs with
      | ascT hsm hsT =>
        obtain ⟨D', hm', hr'⟩ := conservative_forward_tm_bounded _ hm hctx hΓs hΓw hsm (le_refl _)
        have hwf := wfDTy_of_static hsT hwfS
        have hliftr := realizesD_lift hsT hwf
        exact ⟨_, .ascT hm' (cons_of_eq_d hr' hceq hliftr) hwf, hliftr⟩
  | ascV hv hceq hwfS =>
      cases hs with
      | ascV hsv hsτ =>
        obtain ⟨σ, hv', hr⟩ := conservative_forward_val_bounded _ hv hctx hΓs hΓw hsv (le_refl _)
        have hwf := wfTy_of_static hsτ hwfS
        have hl := realizesTy_lift hsτ hwf
        exact ⟨_, .ascV hv' (cons_of_eq_ty hr hceq hl) hwf, realizes_point hl hsτ⟩
  | add hv hc1 hw hc2 =>
      cases hs with
      | add hsv hsw =>
        obtain ⟨σ1, hv', hr1⟩ := conservative_forward_val_bounded _ hv hctx hΓs hΓw hsv (le_refl _)
        obtain ⟨σ2, hw', hr2⟩ := conservative_forward_val_bounded _ hw hctx hΓs hΓw hsw (le_refl _)
        exact ⟨_, .add hv' (cons_of_eq_ty hr1 hc1 .real)
          hw' (cons_of_eq_ty hr2 hc2 .real), realizes_point .real .real⟩
  | ite hv hcb hm hn hceq =>
      cases hs with
      | ite hsv hsm hsn =>
        obtain ⟨σv, hv', hrv⟩ := conservative_forward_val_bounded _ hv hctx hΓs hΓw hsv (le_refl _)
        obtain ⟨D1, h1', hr1⟩ := conservative_forward_tm_bounded _ hm hctx hΓs hΓw hsm (le_refl _)
        obtain ⟨D2, h2', hr2⟩ := conservative_forward_tm_bounded _ hn hctx hΓs hΓw hsn (le_refl _)
        exact ⟨_, .ite hv' (cons_of_eq_ty hrv hcb .bool) h1' h2'
          (cons_of_eq_d hr1 hceq hr2),
          realizes_hull hr1 hr2 (EqD.symm hceq) (isStatic_tm hm hΓs hsm)⟩
termination_by k => k
decreasing_by
  all_goals
    simp only [SPLC.Val.lam.sizeOf_spec, SPLC.Tm.val.sizeOf_spec, SPLC.Tm.app.sizeOf_spec,
      SPLC.Tm.letin.sizeOf_spec, SPLC.Tm.choice.sizeOf_spec, SPLC.Tm.ascT.sizeOf_spec,
      SPLC.Tm.ascV.sizeOf_spec, SPLC.Tm.add.sizeOf_spec, SPLC.Tm.ite.sizeOf_spec] at hk
  all_goals omega

/-- Theorem 3, item 1, backward direction, for open values, with a size bound `k`. -/
theorem conservative_backward_val_bounded : ∀ (k : ℕ) {Γ : Ctx} {Φ : List FTy} (v : SPLC.Val) {σ : FTy},
    HasTyV Φ (embedV v) σ → RealizesCtx Φ Γ → CtxStatic Γ → CtxWf Γ → IsStaticVal v →
    sizeOf v ≤ k → ∃ τ, SPLC.HasTyV Γ v τ ∧ RealizesTy σ τ := by
  intro k Γ Φ v σ h hctx hΓs hΓw hsv hk
  cases v with
  | var x =>
      cases h with
      | var hx =>
        obtain ⟨τ, h1, h2⟩ := realizesCtx_getElemF hctx hx
        exact ⟨τ, .var h1, h2⟩
  | real r =>
      cases h with
      | real => exact ⟨.real, .real, .real⟩
  | bool b =>
      cases h with
      | bool => exact ⟨.bool, .bool, .bool⟩
  | lam τa m =>
      cases h with
      | lam hm hwτ =>
        cases hsv with
        | lam hsτ hsm =>
          have hl := realizesTy_lift hsτ hwτ
          have hwS := splcWfTy_of_static hsτ hwτ
          obtain ⟨Tb, hd, hr⟩ := conservative_backward_tm_bounded _ m hm (.cons hl hctx)
            (ctxStatic_cons hsτ hΓs) (ctxWf_cons hwS hΓw) hsm (le_refl _)
          exact ⟨_, .lam hd hwS, .arrow hl hr⟩
termination_by k => k
decreasing_by
  all_goals simp only [SPLC.Val.lam.sizeOf_spec] at hk
  all_goals omega

/-- Theorem 3, item 2, backward direction, for open terms, with a size bound `k`: a
GPLC-typed SPLC term is SPLC-typed at a static type realized by the GPLC type.
The `let` case mirrors the forward one, with right coverage and determinism of
SPLC (`SPLC.det_tm`). -/
theorem conservative_backward_tm_bounded : ∀ (k : ℕ) {Γ : Ctx} {Φ : List FTy} (m : SPLC.Tm) {D : FDist},
    HasTyT Φ (embedT m) D → RealizesCtx Φ Γ → CtxStatic Γ → CtxWf Γ → IsStaticTm m →
    sizeOf m ≤ k → ∃ T, SPLC.HasTyT Γ m T ∧ RealizesD D T := by
  intro k Γ Φ m D h hctx hΓs hΓw hs hk
  cases m with
  | val v =>
      cases h with
      | val hv =>
        cases hs with
        | val hsv =>
          obtain ⟨τ, hd, hr⟩ := conservative_backward_val_bounded _ v hv hctx hΓs hΓw hsv (le_refl _)
          exact ⟨_, .val hd, realizes_point hr (isStatic_val hd hΓs hsv)⟩
  | app v w =>
      cases h with
      | app hv hw hdc hcons =>
        cases hs with
        | app hsv hsw =>
          obtain ⟨τv, hdv, hrv⟩ := conservative_backward_val_bounded _ v hv hctx hΓs hΓw hsv (le_refl _)
          cases hdc with
          | arrow =>
            cases hrv with
            | arrow hrs hrd =>
              obtain ⟨τw, hdw, hrw⟩ := conservative_backward_val_bounded _ w hw hctx hΓs hΓw hsw (le_refl _)
              have hceq := eq_of_cons_ty hcons hrw hrs
              exact ⟨_, .app hdv hdw (EqTy.symm hceq), hrd⟩
          | unk => cases hrv
  | letin mm nb =>
      cases h with
      | @letin _ _ _ D0 Ff hm hFf =>
        cases hs with
        | letin hsm hsn =>
          classical
          obtain ⟨Ts0, hdm, hr0⟩ := conservative_backward_tm_bounded _ mm hm hctx hΓs hΓw hsm (le_refl _)
          obtain ⟨es, rfl⟩ : ∃ es, Ts0 = .dist es := by
            cases Ts0
            exact ⟨_, rfl⟩
          have hesS : IsStaticEntries es := by
            exact (isStatic_tm hdm hΓs hsm).entries
          have hesW := wfDTy_dist_inv (wf_tm hdm hΓw)
          have hbctxS : ∀ j : Fin es.length, CtxStatic ((es.get j).1 :: Γ) :=
            fun j => ctxStatic_cons (isStaticEntries_get_ty hesS j) hΓs
          have hbctxW : ∀ j : Fin es.length, CtxWf ((es.get j).1 :: Γ) :=
            fun j => ctxWf_cons (hesW.1 _ (List.get_mem es j)) hΓw
          -- every static entry takes its body from a realizing entry (right
          -- coverage of the realization)
          have hbody : ∀ j : Fin es.length,
              ∃ Tj, SPLC.HasTyT ((es.get j).1 :: Γ) nb Tj := by
            intro j
            obtain ⟨i, hij⟩ := hr0.covR j
            obtain ⟨Tj, hTj, -⟩ := conservative_backward_tm_bounded _ nb (hFf i) (.cons hij hctx)
              (hbctxS j) (hbctxW j) hsn (le_refl _)
            exact ⟨Tj, hTj⟩
          choose Ts hTs using hbody
          refine ⟨letRes es Ts, .letin hdm hTs, ?_⟩
          refine realizes_letRes hr0 ?_ ?_
          · -- bodies: recursion at each realizing pair, plus determinism of SPLC
            intro i j hstrict
            obtain ⟨Tj', hTj', hr''⟩ := conservative_backward_tm_bounded _ nb (hFf i)
              (.cons hstrict hctx) (hbctxS j) (hbctxW j) hsn (le_refl _)
            rwa [SPLC.det_tm hTj' (hTs j)] at hr''
          · -- branch alignment: determinism of SPLC up to `=ₛ`
            intro j j' hceq
            exact det_eq_tm (hTs j) (hTs j') (.cons hceq (eqCtx_refl hΓs))
              (hbctxS j) (hbctxS j') (hbctxW j) (hbctxW j') hsn
  | choice p m1 n1 =>
      cases h with
      | choice ha0 ha1 h1 h2 =>
        cases hs with
        | choice _ _ hsm hsn =>
          obtain ⟨T1, hd1, hr1⟩ := conservative_backward_tm_bounded _ m1 h1 hctx hΓs hΓw hsm (le_refl _)
          obtain ⟨T2, hd2, hr2⟩ := conservative_backward_tm_bounded _ n1 h2 hctx hΓs hΓw hsn (le_refl _)
          exact ⟨_, .choice hd1 hd2, realizes_choice ha0 ha1 hr1 hr2⟩
  | ascT m1 T1 =>
      cases h with
      | ascT hm hcons hwf =>
        cases hs with
        | ascT hsm hsT =>
          obtain ⟨T', hd', hr'⟩ := conservative_backward_tm_bounded _ m1 hm hctx hΓs hΓw hsm (le_refl _)
          have hliftr := realizesD_lift hsT hwf
          have hceq := eq_of_cons_d hcons hr' hliftr
          exact ⟨_, .ascT hd' hceq (splcWfDTy_of_static hsT hwf), hliftr⟩
  | ascV v τ =>
      cases h with
      | ascV hv hcons hwf =>
        cases hs with
        | ascV hsv hsτ =>
          obtain ⟨τ', hd', hr'⟩ := conservative_backward_val_bounded _ v hv hctx hΓs hΓw hsv (le_refl _)
          have hl := realizesTy_lift hsτ hwf
          have hceq := eq_of_cons_ty hcons hr' hl
          exact ⟨_, .ascV hd' hceq (splcWfTy_of_static hsτ hwf),
            realizes_point hl hsτ⟩
  | ite v m1 n1 =>
      cases h with
      | ite hv hcb h1 h2 hcons =>
        cases hs with
        | ite hsv hsm hsn =>
          obtain ⟨τv, hdv, hrv⟩ := conservative_backward_val_bounded _ v hv hctx hΓs hΓw hsv (le_refl _)
          have hceqb := eq_of_cons_ty hcb hrv .bool
          obtain ⟨T1, hd1, hr1⟩ := conservative_backward_tm_bounded _ m1 h1 hctx hΓs hΓw hsm (le_refl _)
          obtain ⟨T2, hd2, hr2⟩ := conservative_backward_tm_bounded _ n1 h2 hctx hΓs hΓw hsn (le_refl _)
          have hceq := eq_of_cons_d hcons hr1 hr2
          exact ⟨_, .ite hdv hceqb hd1 hd2 hceq,
            realizes_hull hr1 hr2 (EqD.symm hceq) (isStatic_tm hd1 hΓs hsm)⟩
  | add v w =>
      cases h with
      | add hv hc1 hw hc2 =>
        cases hs with
        | add hsv hsw =>
          obtain ⟨τ1, hd1, hr1⟩ := conservative_backward_val_bounded _ v hv hctx hΓs hΓw hsv (le_refl _)
          obtain ⟨τ2, hd2, hr2⟩ := conservative_backward_val_bounded _ w hw hctx hΓs hΓw hsw (le_refl _)
          exact ⟨_, .add hd1 (eq_of_cons_ty hc1 hr1 .real)
            hd2 (eq_of_cons_ty hc2 hr2 .real), realizes_point .real .real⟩
termination_by k => k
decreasing_by
  all_goals
    simp only [SPLC.Val.lam.sizeOf_spec, SPLC.Tm.val.sizeOf_spec, SPLC.Tm.app.sizeOf_spec,
      SPLC.Tm.letin.sizeOf_spec, SPLC.Tm.choice.sizeOf_spec, SPLC.Tm.ascT.sizeOf_spec,
      SPLC.Tm.ascV.sizeOf_spec, SPLC.Tm.add.sizeOf_spec, SPLC.Tm.ite.sizeOf_spec] at hk
  all_goals omega
end

/-! ### Unbounded forms -/

/-- Theorem 3 (conservative extension of the static semantics), item 1,
forward direction, open values: under a realizing context, an SPLC-typed value is
GPLC-typed at a realizing type. -/
theorem conservative_forward_val {Γ : Ctx} {Φ : List FTy} {v : SPLC.Val} {τ : Ty}
    (h : Γ ⊢ₛ v : τ) (hctx : RealizesCtx Φ Γ) (hΓs : CtxStatic Γ)
    (hΓw : CtxWf Γ) (hsv : IsStaticVal v) :
    ∃ σ, Φ ⊢ embedV v : σ ∧ σ ⇝ τ :=
  conservative_forward_val_bounded (sizeOf v) h hctx hΓs hΓw hsv (le_refl _)

/-- Theorem 3 (conservative extension of the static semantics), item 2,
forward direction, open terms: under a realizing context, an SPLC-typed term is
GPLC-typed at a realizing type. -/
theorem conservative_forward_tm {Γ : Ctx} {Φ : List FTy} {m : SPLC.Tm} {T : DTy}
    (h : SPLC.HasTyT Γ m T) (hctx : RealizesCtx Φ Γ) (hΓs : CtxStatic Γ)
    (hΓw : CtxWf Γ) (hs : IsStaticTm m) :
    ∃ D, HasTyT Φ (embedT m) D ∧ RealizesD D T :=
  conservative_forward_tm_bounded (sizeOf m) h hctx hΓs hΓw hs (le_refl _)

/-- Theorem 3 (conservative extension of the static semantics), item 1,
backward direction, open values: under a realizing context, a GPLC-typed SPLC value is
SPLC-typed at a realized type. -/
theorem conservative_backward_val (v : SPLC.Val) {Γ : Ctx} {Φ : List FTy} {σ : FTy}
    (h : Φ ⊢ embedV v : σ) (hctx : RealizesCtx Φ Γ) (hΓs : CtxStatic Γ)
    (hΓw : CtxWf Γ) (hsv : IsStaticVal v) :
    ∃ τ, Γ ⊢ₛ v : τ ∧ σ ⇝ τ :=
  conservative_backward_val_bounded (sizeOf v) v h hctx hΓs hΓw hsv (le_refl _)

/-- Theorem 3 (conservative extension of the static semantics), item 2,
backward direction, open terms: under a realizing context, a GPLC-typed SPLC term is
SPLC-typed at a realized type. -/
theorem conservative_backward_tm (m : SPLC.Tm) {Γ : Ctx} {Φ : List FTy} {D : FDist}
    (h : HasTyT Φ (embedT m) D) (hctx : RealizesCtx Φ Γ) (hΓs : CtxStatic Γ)
    (hΓw : CtxWf Γ) (hs : IsStaticTm m) :
    ∃ T, SPLC.HasTyT Γ m T ∧ RealizesD D T :=
  conservative_backward_tm_bounded (sizeOf m) m h hctx hΓs hΓw hs (le_refl _)

/-! ## Theorem 3, closed terms -/

/-- Theorem 3 (conservative extension of the static semantics), item 2,
forward direction: a closed SPLC-typed term is GPLC-typed at a formula type realizing
its SPLC type. -/
theorem static_conservative_extension_forward {m : SPLC.Tm} {T : DTy} (hs : IsStaticTm m) (h : ⊢ₛ m : T) :
    ∃ D, ⊢ embedT m : D ∧ D ⇝ T :=
  conservative_forward_tm h .nil (fun τ h => by simp at h) (fun τ h => by simp at h)
    hs

/-- Theorem 3 (conservative extension of the static semantics), item 2,
backward direction: a closed SPLC term typed in GPLC is SPLC-typed at a static type
realized by its GPLC type. -/
theorem static_conservative_extension_backward {m : SPLC.Tm} {D : FDist} (hs : IsStaticTm m)
    (h : ⊢ embedT m : D) : ∃ T, ⊢ₛ m : T ∧ D ⇝ T :=
  conservative_backward_tm m h .nil (fun τ h => by simp at h) (fun τ h => by simp at h)
    hs

/-- Theorem 3 (conservative extension of the static semantics), as
typeability: a closed SPLC term is typeable in SPLC iff it is typeable in GPLC.
The forward and backward forms add that the types correspond by realization. -/
theorem static_conservative_extension {m : SPLC.Tm} (hs : IsStaticTm m) :
    (∃ T, ⊢ₛ m : T) ↔ (∃ D, ⊢ embedT m : D) := by
  constructor
  · rintro ⟨T, h⟩
    obtain ⟨D, hd, _⟩ := static_conservative_extension_forward hs h
    exact ⟨D, hd⟩
  · rintro ⟨D, h⟩
    obtain ⟨T, hd, _⟩ := static_conservative_extension_backward hs h
    exact ⟨T, hd⟩

end GradualProb.GPLC
