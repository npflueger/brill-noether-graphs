import DraismaVargas.LocalCases.NonDanglingValency
import DraismaVargas.LocalCases.PresentationDecomposition

/-!
# One full-dimensional stable-source presentation

This module provides a single structure carrying the global consequences of
full-dimensionality, so that the local source cases need not assume them again
at each wall, together with the consequences that genuinely follow from it and
a precise record of the inputs that do not.

## The structure

`FullDimensionalSourcePresentation data coordinate` bundles

* the datum's validity, and the Part-I standing target hypotheses
  (connected, genus zero);
* the **numerical** statement of full-dimensionality,
  `|E(target)| = 2 g(source) + 2 degree - 5`;
* an honest stable length-matrix labelling
  (`W4StableSource.StableLengthMatrixLabelling`) and nonsingularity of its
  matrix;
* trivalence of the stable graph, in its two consumable forms: the upper bound
  `nd(v) ≤ 3` and the absence of cyclic stable paths
  (`W4StableSource.HasPathEnds`).

Everything else that the local cases need is derived here:
change-minimality, the combinatorial-type conditions, dangling-no-glue, the
`nd(v) ∈ {0, 2, 3}` trichotomy at every source vertex and at every wall block,
the stable-path count, and an ordered presentation that simultaneously
decomposes the pruned source and has rows that are genuine walks.

## The `w4` wall interface is about a different datum

`W4StableSource.AuxR0SourceInput data star` is **not** satisfiable by a
full-dimensional datum, and not for a small reason.  Two of its fields fail:

* `equation_c : data.targetExcess wall = 1` contradicts change-minimality
  (`targetExcess = 0` everywhere), which full-dimensionality forces.  This
  already makes `NonDanglingValency.auxR0SourceInput_of_det_ne_zero` vacuous:
  it assumes `data.ChangeMinimal` *and* `data.targetExcess wall = 1`
  (`false_of_changeMinimal_auxR0SourceInput`).
* `stablePath_card : #(StablePath data) = |E(target)| + 1` contradicts the
  mere existence of a `StableLengthMatrixLabelling data coordinate`, whose two
  equivalences force `#(StablePath data) = |E(target)|` exactly
  (`stablePath_card`, `stablePath_card_ne_succ`).  So the second hypothesis of
  `auxR0SourceInput_of_det_ne_zero` is inconsistent with its fourth,
  independently of the first failure.

This reflects the fact that `AuxR0SourceInput` describes the
**codimension-one wall datum**, whose target has one edge fewer than the
incoming full-dimensional one, while a square honest stable presentation
describes the **full-dimensional datum**.  The two cannot be the same `data`.
What relates them is therefore a *bridge between two data*, not an extra field
on one; `WallDegeneration` below states exactly the part of that bridge which
the `stablePath_card` field needs, and
`stablePath_card_of_wallDegeneration` derives the field from it.
-/

namespace DraismaVargas.LocalCases.FullDimensionalSource

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.DanglingDescent
open DraismaVargas.LocalCases.NonDanglingValency
open DraismaVargas.LocalCases.PresentationDecomposition

variable {target : CFGraph} {degree : ℕ}

/-! ## Change-minimality and Equation (C) are incompatible -/

/-- A target vertex with `ch(v) + val(v) - 3 = 1` is not change-minimal.  The
W4 wall is such a vertex, by `AuxR0SourceInput.equation_c`. -/
theorem not_changeMinimal_of_targetExcess_eq_one
    {data : GluingDatum target degree} {vertex : target.V}
    (hExcess : data.targetExcess vertex = 1) : ¬ data.ChangeMinimal := by
  intro hMinimal
  have hZero : data.targetExcess vertex = 0 := hMinimal vertex
  omega

/-- **The first vacuity.**  `AuxR0SourceInput` and `ChangeMinimal` cannot hold
of the same datum, so `NonDanglingValency.auxR0SourceInput_of_det_ne_zero`,
which assumes both, is vacuous. -/
theorem false_of_changeMinimal_auxR0SourceInput
    {data : GluingDatum target degree} {wall : target.V}
    {star : W4TargetPairings.FourStar target wall}
    (hMinimal : data.ChangeMinimal) (input : AuxR0SourceInput data star) :
    False :=
  not_changeMinimal_of_targetExcess_eq_one input.equation_c hMinimal

/-! ## A square honest stable presentation counts the stable paths exactly -/

section Labelling

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {data : GluingDatum target degree}

omit [DecidableEq coordinate] in
/-- The two equivalences of an honest stable labelling already say how many
stable paths there are: exactly one per target edge occurrence.  No separate
`stablePath_card` hypothesis is needed, or indeed available. -/
theorem stablePath_card_of_labelling
    (labelling : StableLengthMatrixLabelling data coordinate) :
    Fintype.card (StablePath data) = target.edges.card := by
  classical
  calc Fintype.card (StablePath data)
      = Fintype.card coordinate := Fintype.card_congr labelling.row
    _ = Fintype.card target.edges := Fintype.card_congr labelling.targetEdge
    _ = target.edges.card := Multiset.card_coe target.edges

omit [DecidableEq coordinate] in
/-- **The second vacuity.**  The wall cardinality `|E(target)| + 1` is refuted,
not merely unproved, by the existence of a square honest stable presentation. -/
theorem stablePath_card_ne_succ
    (labelling : StableLengthMatrixLabelling data coordinate) :
    Fintype.card (StablePath data) ≠ target.edges.card + 1 := by
  rw [stablePath_card_of_labelling labelling]
  omega

omit [DecidableEq coordinate] in
/-- Consequently no W4 wall interface exists for a datum carrying a square
honest stable presentation, whether or not that datum is change-minimal. -/
theorem false_of_labelling_auxR0SourceInput
    {wall : target.V} {star : W4TargetPairings.FourStar target wall}
    (labelling : StableLengthMatrixLabelling data coordinate)
    (input : AuxR0SourceInput data star) : False :=
  stablePath_card_ne_succ labelling input.stablePath_card

end Labelling

/-! ## Nontriviality of a full-dimensional target -/

/-- A one-vertex target is loopless, hence edgeless, and `2 g + 2 d - 5` is
odd.  So the dimension-saturation equation forces the target to have at least
two vertices — the hypothesis `CombinatorialType.correctionNonnegative`
needs. -/
theorem nontrivial_target_of_saturated {data : GluingDatum target degree}
    (hSaturated : (target.edges.card : ℤ) =
      2 * genus data.sourceGraph + 2 * degree - 5) :
    Nontrivial target.V := by
  rcases subsingleton_or_nontrivial target.V with _ | hNontrivial
  · exfalso
    have hEmpty : target.edges = 0 := by
      refine Multiset.eq_zero_of_forall_notMem ?_
      rintro ⟨a, b⟩ hMem
      have hPair : ((a, b) : target.V × target.V) = (a, a) := by
        rw [Subsingleton.elim b a]
      rw [hPair] at hMem
      exact target.loopless a hMem
    rw [hEmpty] at hSaturated
    simp only [Multiset.card_zero, Nat.cast_zero] at hSaturated
    omega
  · exact hNontrivial

/-! ## The structure -/

/-- **The global consequences of full-dimensionality, in one object.**

The fields, and the consumer that forces each:

* `valid` — ambient source data; every local case needs it, and
  `nonDanglingValency_ne_one` needs its connectedness half.
* `targetConnected`, `targetGenus` — the standing Part-I target hypotheses,
  carried by `SemanticAtlasMarch.PresentedProgress` itself.  `targetConnected`
  is what `CombinatorialType.correctionNonnegative` consumes and `targetGenus`
  is what `dimensionCorrection_of_target_genus_zero` consumes.
* `saturated` — full-dimensionality as a *number*, in exactly the form
  `GluingDatum.changeMinimal_of_genus_zero_dimension_saturated` takes.  This is
  the field that pays: change-minimality, and with it dangling-no-glue, become
  theorems rather than hypotheses.
* `labelling` — the honest stable length-matrix labelling.  Its rows are the
  actual stable-path classes, which is what makes `Decomposes` provable and
  what pins the stable-path count.
* `det_ne_zero` — nonsingularity; the input to
  `combinatorialType_of_det_ne_zero` and `danglingEdgeNoGlue_of_det_ne_zero`.
* `trivalent` — trivalence of the stable graph `H(M)`, in the form the wall
  cases need.  This bound is *not* a consequence of validity, dangling-no-glue
  and Equation (C) (see the module docstring of `NonDanglingValency`); the
  section at the end of this file explains why it remains an input.
* `pathEnds` — trivalence again, in the complementary form "no stable path is
  a cycle".  This is the hypothesis
  `W4StableSource.StableLengthMatrixLabelling.orderedPath` carries, and hence
  what the `ClosedEndpoint.InputRefinement` receipt consumes.  It does not
  follow from `trivalent`: a pruned source all of whose vertices have
  surviving valency two is a disjoint union of cycles, satisfies `trivalent`,
  and has no path end anywhere.

Deliberately *not* fields, because they are theorems below: change-minimality,
the combinatorial-type conditions, dangling-no-glue, the decomposition of the
pruned source by the stable rows, and the stable-path count. -/
structure FullDimensionalSourcePresentation
    (data : GluingDatum target degree) (coordinate : Type*)
    [Fintype coordinate] [DecidableEq coordinate] where
  /-- The incoming datum is a valid gluing datum. -/
  valid : data.Valid
  /-- Part-I standing hypothesis on the target. -/
  targetConnected : graph_connected target
  /-- Part-I standing hypothesis on the target. -/
  targetGenus : genus target = 0
  /-- Full-dimensionality: the dimension formula is saturated. -/
  saturated : (target.edges.card : ℤ) =
    2 * genus data.sourceGraph + 2 * degree - 5
  /-- The honest stable length-matrix labelling of the pruned source. -/
  labelling : StableLengthMatrixLabelling data coordinate
  /-- Its length matrix is nonsingular. -/
  det_ne_zero : (GluingDatum.LengthMatrixPresentation.matrix
    labelling.presentation).det ≠ 0
  /-- The stable graph is trivalent: no source vertex has four or more
  surviving incident occurrences. -/
  trivalent : ∀ vertex : data.SourceVertex, nonDanglingValency data vertex ≤ 3
  /-- The stable graph has minimal valency three: no stable path is a cycle. -/
  pathEnds : HasPathEnds data

namespace FullDimensionalSourcePresentation

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {data : GluingDatum target degree}
  (fd : FullDimensionalSourcePresentation data coordinate)

include fd

/-! ### Derived: the combinatorial type and change-minimality -/

/-- Connectedness of the quotient source. -/
theorem connected : data.Connected := fd.valid.1

/-- A full-dimensional target has at least two vertices. -/
theorem nontrivial_target : Nontrivial target.V :=
  nontrivial_target_of_saturated fd.saturated

/-- Nonsingularity makes the datum a combinatorial type: no target fibre is
entirely dangling, and the change at every divalent target vertex is
positive. -/
theorem combinatorialType : CombinatorialType data :=
  fd.labelling.combinatorialType_of_det_ne_zero fd.valid fd.det_ne_zero

/-- No target edge occurrence has an entirely dangling fibre. -/
theorem noDanglingTargetFibres : NoDanglingTargetFibres data :=
  fd.combinatorialType.noDanglingTargetFibres

/-- Every dimension-correction term is nonnegative. -/
theorem correctionNonnegative : data.CorrectionNonnegative := by
  have := fd.nontrivial_target
  exact fd.combinatorialType.correctionNonnegative fd.valid fd.targetConnected

/-- **Change-minimality is derived, not assumed.**  Nonnegative corrections
summing to the saturated dimension formula force every one of them to vanish.
Without this structure the local cases would have to carry it as a
hypothesis. -/
theorem changeMinimal : data.ChangeMinimal :=
  data.changeMinimal_of_genus_zero_dimension_saturated fd.correctionNonnegative
    fd.targetGenus fd.saturated

/-- Every target vertex of a full-dimensional datum has `ch(v) + val(v) = 3`. -/
theorem targetExcess_eq_zero (vertex : target.V) :
    data.targetExcess vertex = 0 := fd.changeMinimal vertex

/-- **Dangling-no-glue is derived, not assumed**: every dangling occurrence
has index one. -/
theorem danglingEdgeNoGlue : DanglingEdgeNoGlue data :=
  danglingEdgeNoGlue_of_det_ne_zero data fd.valid fd.changeMinimal fd.labelling
    fd.det_ne_zero

/-! ### Derived: the stable paths -/

/-- **The stable-path count is derived, not assumed**: one stable path per
target edge occurrence. -/
theorem stablePath_card : Fintype.card (StablePath data) = target.edges.card :=
  stablePath_card_of_labelling fd.labelling

/-- **The decomposition is derived, not assumed**: the rows of the honest
stable presentation partition the surviving source occurrences. -/
theorem decomposes : Decomposes fd.labelling.presentation :=
  stableLengthMatrixLabelling_decomposes fd.labelling

/-! ### Derived: the valency trichotomy -/

/-- **The valency trichotomy at every source vertex.**  `nd ≠ 1` is
`NonDanglingValency.nonDanglingValency_ne_one`, which needs only
connectedness; `nd ≤ 3` is the trivalence field.  This is the
`nonDangling_valency` obligation of `W4StableSource.AuxR0SourceInput`, proved
once globally instead of per wall. -/
theorem nonDanglingValency_trichotomy (vertex : data.SourceVertex) :
    nonDanglingValency data vertex = 0 ∨ nonDanglingValency data vertex = 2 ∨
      nonDanglingValency data vertex = 3 :=
  nonDanglingValency_eq_zero_or_two_or_three data fd.connected vertex
    (fd.trivalent vertex)

/-- The wall-block form, matching the `nonDangling_valency` field of
`W4StableSource.AuxR0SourceInput` verbatim, at every target vertex at once. -/
theorem wallBlock_nonDanglingValency_trichotomy (wall : target.V)
    (sourceBlock : WallBlock data wall) :
    nonDanglingValency data
        (WallBlock.sourceVertex data wall sourceBlock) = 0 ∨
      nonDanglingValency data
          (WallBlock.sourceVertex data wall sourceBlock) = 2 ∨
        nonDanglingValency data
          (WallBlock.sourceVertex data wall sourceBlock) = 3 :=
  fd.nonDanglingValency_trichotomy _

/-! ### Derived: the ordered presentation -/

/-- The honest stable presentation rebuilt on traversal-ordered rows. -/
noncomputable def orderedPresentation : data.LengthMatrixPresentation coordinate :=
  fd.labelling.orderedPresentation fd.pathEnds

/-- Reordering the rows does not change the length matrix. -/
theorem matrix_orderedPresentation :
    GluingDatum.LengthMatrixPresentation.matrix fd.orderedPresentation =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation :=
  fd.labelling.matrix_orderedPresentation fd.pathEnds

/-- The ordered presentation is still nonsingular. -/
theorem det_orderedPresentation_ne_zero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.orderedPresentation).det ≠ 0 := by
  rw [fd.matrix_orderedPresentation]
  exact fd.det_ne_zero

/-- Consecutive entries of an ordered row meet at a surviving valency-two
source vertex. -/
theorem orderedPresentation_chain (row : coordinate) :
    (fd.orderedPresentation.path row).IsChain fun first second ↦
      ∃ vertex : data.SourceVertex, Incident data first vertex ∧
        Incident data second vertex ∧ nonDanglingValency data vertex = 2 :=
  fd.labelling.orderedPath_chain fd.pathEnds row

/-- **The combination the refinement receipt needs**: the traversal-ordered
presentation both decomposes the pruned source and has rows that are genuine
walks. -/
theorem orderedDecomposes : Decomposes fd.orderedPresentation := by
  refine ⟨fun row ↦ fd.labelling.orderedPath_nodup fd.pathEnds row,
    fun row row' hNe edge hMem hMem' ↦ ?_, fun edge hSurvives ↦ ?_,
    fun edge hDangling row hMem ↦ ?_⟩
  · obtain ⟨_, hRow⟩ :=
      (fd.labelling.mem_orderedPath_iff fd.pathEnds row edge).mp hMem
    obtain ⟨_, hRow'⟩ :=
      (fd.labelling.mem_orderedPath_iff fd.pathEnds row' edge).mp hMem'
    exact hNe (hRow.symm.trans hRow')
  · exact ⟨fd.labelling.row (NonDanglingEdge.stablePath ⟨edge, hSurvives⟩),
      (fd.labelling.mem_orderedPath_iff fd.pathEnds _ edge).mpr
        ⟨hSurvives, rfl⟩⟩
  · exact ((fd.labelling.mem_orderedPath_iff fd.pathEnds row edge).mp
      hMem).choose hDangling

/-! ### The wall interface is unreachable from here -/

/-- A full-dimensional datum is never a W4 wall datum.  Both the
`stablePath_card` and the `equation_c` fields of
`W4StableSource.AuxR0SourceInput` fail. -/
theorem false_of_auxR0SourceInput {wall : target.V}
    {star : W4TargetPairings.FourStar target wall}
    (input : AuxR0SourceInput data star) : False :=
  false_of_labelling_auxR0SourceInput fd.labelling input

end FullDimensionalSourcePresentation

/-! ## The codimension-one bridge -/

/-- The part of the wall degeneration that `W4StableSource.AuxR0SourceInput`'s
`stablePath_card` field needs.  A W4 wall datum `wallDatum` is obtained from a
full-dimensional `data` by contracting one target edge; the paper's content is
that the stable model `H(M)` is unchanged by that contraction, so the wall
datum has one more stable path than its target has edges.

Both fields are hypotheses; this module proves neither. -/
structure WallDegeneration {wallTarget : CFGraph}
    (data : GluingDatum target degree)
    (wallDatum : GluingDatum wallTarget degree) : Prop where
  /-- One target edge has been contracted. -/
  edge_card : target.edges.card = wallTarget.edges.card + 1
  /-- The stable model is unchanged. -/
  stablePath : Nonempty (StablePath wallDatum ≃ StablePath data)

/-- Given the bridge, the `stablePath_card` field of
`W4StableSource.AuxR0SourceInput` is a consequence of the full-dimensional
presentation of the incoming datum rather than a per-wall assumption. -/
theorem stablePath_card_of_wallDegeneration
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    {data : GluingDatum target degree} {wallTarget : CFGraph}
    {wallDatum : GluingDatum wallTarget degree}
    (fd : FullDimensionalSourcePresentation data coordinate)
    (bridge : WallDegeneration data wallDatum) :
    Fintype.card (StablePath wallDatum) = wallTarget.edges.card + 1 := by
  obtain ⟨equiv⟩ := bridge.stablePath
  rw [Fintype.card_congr equiv, fd.stablePath_card, bridge.edge_card]


/-!
## What this structure does not provide

Four points, none of them forced by the other fields.

1. **`trivalent` is an input, not a theorem.**  The natural derivation is a
   count on the *pruned source graph* `Γ`: writing `m` for the number of stable
   paths, `n` for the number of source vertices of surviving valency at least
   three and `c` for the number of components of `Γ`,

   ```
   ∑_{nd(v) ≥ 3} nd(v) = 2 m        (each stable path has two ends)
   n = m - g(Γ) + c                 (Euler characteristic of the stable graph)
   ```

   so `nd(v) ≥ 3` everywhere on the stable graph gives `3 n ≤ 2 m`, hence
   `m ≤ 3 g(Γ) - 3 c`.

   The pruned source is the `CFGraph` `PrunedSource.prunedSource`, and
   `PrunedSource`, `Trivalence`, `StablePathCount`, `DanglingBetti` and
   `TrivalenceClosure` between them carry out the count described above --
   including `cyclomatic_nonneg` without a spanning forest, and
   `cyclomatic_prunedSource_eq_genus_sourceGraph`.

   Trivalence nevertheless remains an input, and this is the point that
   matters: `TrivalenceClosure.trivalent_iff_genus_eq` proves trivalence
   **equivalent** to an exact value of the source genus, not implied by the
   count.  The count supplies `m ≤ 3 g(Γ) - 3 c` only; nothing in the structure
   bounds the genus from above, so no amount of further Euler bookkeeping turns
   `trivalent` into a theorem.  It is a construction input, and the seed
   supplies it because the seed lives at `ρ = 0` by design.

   The identity `|E(target)| = 3 g - 3 c` is
   `TrivalenceClosure.card_target_edges_eq_of_presentation`, and it follows from
   the `trivalent` field, not from `saturated`.  That matters in practice,
   because it makes `3 ∣ |E(target)|` a constraint every presentation obeys;
   `W4Bridge` uses it to rule out small candidate shapes.

2. **`pathEnds` is an input for the same reason**, and is not implied by
   `trivalent`: a component of `Γ` that is a single cycle has `nd(v) = 2`
   everywhere, satisfies `trivalent`, and its one stable path has no end.  Ruling
   such a component out is again the `n = m - g(Γ) + c` count.

3. **`WallDegeneration` proves neither of its fields.**  `edge_card` is a
   statement about `TargetExpansion.graph`; `stablePath` is the paper's claim
   that contracting a target edge leaves the stable model `H(M)` unchanged.
   Moreover, even with those two, the remaining `AuxR0SourceInput` fields
   `dangling_no_glue` and `nonDangling_valency` do **not** transfer: they are
   statements about the wall datum's own pruned source, and transferring them
   needs an equivalence `wallDatum.SourceEdge ≃ data.SourceEdge` compatible
   with `IsDangling` and with `Incident`.  `WallDegeneration` deliberately does
   not claim that.

4. **`equation_c` is not obtainable from a full-dimensional presentation of the
   same datum at all** — it is the assertion that the datum is *not*
   change-minimal at the wall, which `changeMinimal` above refutes.  It belongs
   to the wall datum, and its derivation
   (`W4StableSource.AuxR0SourceInput.ofChangeMinimalExpansion`, via
   `GlobalResolution.targetExcess_wall_eq_one_of_changeMinimal_of_block_card`)
   takes change-minimality of the *resolved* datum, which is the right shape.
   Those constructors are unaffected by the vacuity above.

### A non-vacuous form of the wall interface

`NonDanglingValency.auxR0SourceInput_of_det_ne_zero` is the only declaration in
this library that asks one datum to be both full-dimensional and a wall
(`false_of_changeMinimal_auxR0SourceInput`,
`false_of_labelling_auxR0SourceInput`).  A non-vacuous restatement keeps its
conclusion and replaces its `stablePath_card`, `hMinimal`, `labelling` and
`hDet` hypotheses by a `FullDimensionalSourcePresentation` of the **incoming**
datum plus a `WallDegeneration` onto the wall datum.  Independently, the
`stablePath_card` field of `AuxR0SourceInput` could be replaced by the labelling
it is only ever used to build, `W4StableSource.StablePathLabelling data`
(`StablePath data ≃ Option target.edges`), which is the non-square shape a wall
datum actually has and which carries no hidden inconsistency.

### Instances

No instance of `FullDimensionalSourcePresentation` is constructed in this
module, and nothing here shows its fields are jointly satisfiable.  Given the
vacuity of `AuxR0SourceInput` for full-dimensional data, that caveat is not
rhetorical.  An instance built from an actual full-dimensional gluing datum is
`CaterpillarRows.fullDim`, the caterpillar seed of Vargas, Part II.
-/

end DraismaVargas.LocalCases.FullDimensionalSource
