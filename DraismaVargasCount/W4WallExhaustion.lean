import DraismaVargasCount.DiscreteW4Normalization
import DraismaVargasCount.StarFrameIso
import DraismaVargasCount.UniformExpansionRecognition
import DraismaVargasCount.W4LimitContraction
import DraismaVargasCount.W4PairingRigidity
import DraismaVargasCount.FrameColumnRigidity

/-!
# Exhaustion of the labelled geometric star at an arbitrary discrete four-valent wall

Source: Vargas, Part II (arXiv:2609.09109), the star of a codimension-one wall; the walls are
those of case `{w4}` of Draisma--Vargas Part I (arXiv:1909.12924).

## What is proved

"The labelled geometric star of this wall is `Fin 3`" is proved here for an arbitrary core
`core`, an arbitrary nondegenerate request `y`, an arbitrary degree, and an arbitrary
regrowth `wall` subject to exactly two conditions on its limit, given three candidates
(see "What is NOT proved"):

* `hFour` -- the merged vertex `mergeVertex wall` of `wall.limit` is
  **four-valent** (this is the `w4` family condition; the `4` is a valency, and
  is unrelated to `degree`, which stays arbitrary);
* `hDiscrete` -- the merged sheet partition there is **discrete**.

Section 0 explains why those two conditions are not independent, and why this
is *exactly* the `w4` case: a discrete vertex partition is unramified
(`targetChange_eq_zero_of_discrete`), so equation (C) -- `ch(w) + val(w) - 3 =
1`, the `equation_c` field of `LocalCases.W4StableSource.AuxR0SourceInput` --
forces `val(w) = 4` (`card_incidentEdges_eq_four_of_discrete`).
Contrapositively, no wall of any of the other nine families carries a discrete
merged partition (`vertexPartition_ne_discrete_of_card_ne_four`).

Section 1 classifies an arbitrary member at such a wall:
`map_merge`, `limit_discrete`, `local_partitions`, `inheritedStar`,
`inheritedStar_edge`, `pairing`, `pairing_placement`.  Each is a one-line
application of `Count.DiscreteContraction` or
`LocalCases.W4IncomingTargetNormalization`, using nothing beyond `hFour` and
`hDiscrete`.

Section 2 records what the uniform expansion `GeometricUniformExpansion.data`
does at a wall vertex; section 3 packages a **candidate**.  A `Candidate` at a
pairing `q` is a full-dimensional, core-identified gluing datum on the expanded
wall target whose vanishing coordinate is the regrown occurrence, which
satisfies the three partition conditions `Count.W4LimitContraction` asks of a
target expansion, and whose canonical contraction dictionary is over the core.
`Candidate.data_eq` shows that a candidate's datum *is* the uniform expansion,
as a literal equality of gluing data.

Sections 4--6 are the count:

* `frameIso` -- **the upward lift**.  An arbitrary regrowth carrying *any*
  labelled limit isomorphism to the wall is isomorphic over the labelled core
  to the candidate at its own pairing index.  Assembled from
  `DiscreteW4Normalization.datumIso`,
  `GeometricUniformExpansion.lift` and `UniformExpansionRecognition.ofEq`,
  glued by `StarFrameIso.ofLimitSquare` against the two squares `source_square`
  and `edge_square`.
* `exists_cls_eq`, `cls_surjective`, `card_le_three` -- exhaustion, and the
  upper bound, with no distinctness receipt used.
* `cls_injective` -- **distinctness, request-free**.  It goes through
  `FrameColumnRigidity.column_eq_allColumns` and
  `W4PairingRigidity.pairing_eq_of_expansionIso`, not through a pointwise
  coordinate identity at a single request.  No coordinate-distinctness
  receipt and no choice of request enters.
* `starEquiv`, `card_eq_three`, `card_odd` -- the exact count.

## What is NOT proved (every surviving hypothesis, explicitly)

* **The candidates are a hypothesis.**  Nothing here constructs a `Candidate`,
  and nothing here says that any wall has three of them.  That is the per-wall
  W4 outgoing family, which is built from an
  `LocalCases.W4StableSource.AuxR0SourceInput` for the wall, the block census
  of `LocalCases.W4OutgoingStableRows`, `LocalCases.W4PositiveExit` and a
  nonvanishing single-column-update determinant.  None of that is here.
  Consequently `card_le_three`, `card_eq_three`, `card_odd` and `starEquiv`
  all carry `cand` as an argument and say nothing about a wall for which no
  candidate package is supplied.  Three candidates need not exist: at a
  discrete four-valent wall a candidate exists exactly at the nonsingular
  pairings, and `W4StarParity` proves the star clause in that form.
* **`hFour` and `hDiscrete` are hypotheses.**  Nothing here proves that a wall
  of the Draisma--Vargas count schedule is four-valent, or that its merged
  partition is discrete.  Section 0 shows `hDiscrete` plus equation (C) implies
  `hFour`, but equation (C) is itself not assumed anywhere below, and nothing
  here proves `hDiscrete` for any wall.  At a regrowth's own wall, `hFour` is
  characterized rather than bare: `RegrowthWallInput.sourceCase_eq_w4_iff`
  is the `Iff` `cls.sourceCase = .w4 ↔ (incidentEdges wall).card = 4` for the
  regrowth's ten-way classification, so `hFour` there is exactly "the
  classification takes the `w4` tag" (`sourceCase_eq_w4`); it is not
  proved of every wall, only related to the classification's own case split.
  `LocalCases.W4StableSource.AuxR0SourceInput` does
  **not** imply `hDiscrete`; its `equation_c` field only pins the valency once
  discreteness is known.
* **Nothing about multiplicities.**  No `Count.signedMult`,
  `fdDenominatorProduct` or leaf-count statement is made; in particular the
  hypothesis `hIndex` of `Count.W4UnitBalance` (discharged in `W4IncomingIndex`)
  is not used, and no parity of a multiplicity sum is claimed.  `card_odd` is
  the parity of the star's *cardinality*.
* **Nothing about the other nine families.**  `w3Four`, `w3Shift`,
  `w3Nd3CoarseFine`, `w3Nd2CoarseFine`, `w2M11`, `w2M1k`, `w2Mkk`, `w2P` and
  `w2R1` (`LocalCases.ClassifiedContinuation.SourceCase`) are untouched.  The
  `Fin 3` here is the three `2+2` pairings of four occurrences and has no
  counterpart in a family of different arity.
* **No `Count.CountSchedule` statement.**  Nothing here says that the walls of
  a count schedule are of this shape, or assembles a global count.
* `Count.CoreIdentification`, `GeometricSegmentWalls.FrameIso` and
  `GeometricStar.Star` are used exactly as they stand; none is weakened or
  further quotiented.

## Consumers

`W4StarParity` (the star clause at every discrete four-valent regrowth), and the star
censuses and exhaustion proofs of the other families, which reuse `mergeVertex`,
`map_merge` and `right_map`.
-/
namespace DraismaVargas.Count.W4WallExhaustion

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GraphContraction GluingContraction TargetExpansion
open W4TargetPairings (FourStar)
open GeometricSegmentWalls (FrameIso)
open WallStar (Regrowth Nondegenerate)
open SegmentWalls (Frame)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-! ## 0.  Why this is exactly the `w4` case

A discrete vertex partition has no ramification, so at a codimension-one wall
-- where equation (C) reads `ch(w) + val(w) - 3 = 1` -- discreteness *forces*
four-valency.  Contrapositively, no wall of any of the other nine families of
`LocalCases.ClassifiedContinuation.SourceCase` has a discrete merged partition,
and so none of them can reuse the argument below by transcription. -/

private theorem discrete_block {d : ℕ} (i : Fin d) :
    (SheetPartition.discrete d).block i = {i} :=
  Finset.ext fun j ↦ by
    rw [SheetPartition.mem_block_iff, SheetPartition.discrete_rel_iff, Finset.mem_singleton,
      eq_comm]

/-- **A discrete vertex partition is unramified.** -/
theorem targetChange_eq_zero_of_discrete {target : CFGraph} {degree : ℕ}
    (data : GluingDatum target degree) (vertex : target.V)
    (hDiscrete : data.vertexPartition vertex = SheetPartition.discrete degree) :
    data.targetChange vertex = 0 := by
  have hRel : ∀ i j : Fin degree, (data.vertexPartition vertex).Rel i j ↔ i = j := by
    intro i j
    rw [hDiscrete]
    exact SheetPartition.discrete_rel_iff i j
  rw [GluingDatum.targetChange]
  apply Finset.sum_eq_zero
  intro block _
  have hBlock : (data.vertexPartition vertex).block block.1 = {block.1} :=
    Finset.ext fun j ↦ by
      rw [SheetPartition.mem_block_iff, Finset.mem_singleton, hRel, eq_comm]
  have hCard : (data.vertexPartition vertex).blockCard block.1 = 1 := by
    rw [SheetPartition.blockCard, hBlock, Finset.card_singleton]
  have hEdge : ∀ edge ∈ GluingDatum.incidentEdges vertex,
      ((data.edgePartition edge).blockCountWithin (data.vertexPartition vertex) block.1 : ℤ)
        = 1 := by
    intro edge _
    rw [SheetPartition.blockCountWithin, hBlock, Finset.image_singleton, Finset.card_singleton]
    norm_num
  rw [GluingDatum.localRamification, Finset.sum_congr rfl hEdge, Finset.sum_const, hCard]
  push_cast
  ring

/-- **A discrete codimension-one wall is four-valent.**  Equation (C)
(`GluingDatum.targetExcess wall = 1`, the `equation_c` field of
`LocalCases.W4StableSource.AuxR0SourceInput` and of
`LocalCases.SecondEquation`/`ThirdEquation`) plus discreteness give
`val(w) = 4`; so `hFour` below is not an independent assumption at a wall of
the count schedule. -/
theorem card_incidentEdges_eq_four_of_discrete {target : CFGraph} {degree : ℕ}
    (data : GluingDatum target degree) (vertex : target.V)
    (hDiscrete : data.vertexPartition vertex = SheetPartition.discrete degree)
    (hExcess : data.targetExcess vertex = 1) :
    (GluingDatum.incidentEdges vertex).card = 4 := by
  rw [GluingDatum.targetExcess, targetChange_eq_zero_of_discrete data vertex hDiscrete] at hExcess
  omega

/-- **The contrapositive, which is the scope statement for the other nine
families.**  A codimension-one wall that is not four-valent -- every `w3*` and
`w2*` wall -- does not carry a discrete merged partition. -/
theorem vertexPartition_ne_discrete_of_card_ne_four {target : CFGraph} {degree : ℕ}
    (data : GluingDatum target degree) (vertex : target.V)
    (hExcess : data.targetExcess vertex = 1)
    (hCard : (GluingDatum.incidentEdges vertex).card ≠ 4) :
    data.vertexPartition vertex ≠ SheetPartition.discrete degree :=
  fun hDiscrete ↦ hCard (card_incidentEdges_eq_four_of_discrete data vertex hDiscrete hExcess)

/-! ## 1.  The merged vertex, and the classification of an arbitrary member -/

/-- The merged vertex of a regrowth's own limit: the image of the two
endpoints of the occurrence its vanishing coordinate names. -/
def mergeVertex (w : Regrowth core y degree) : (w.frame.limitTarget w.column).V :=
  ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
    fst_ne_snd (w.frame.edgeOf w.column)⟩

variable {hy : Nondegenerate y} {wall : Regrowth core y degree}

/-- **A four-valent wall pins the merged vertex.**  Any labelled limit
isomorphism to the wall carries an arbitrary member's merged vertex to the
wall's, because full-dimensionality bounds every other valency by three. -/
theorem map_merge (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall)
    (hFour : (GluingDatum.incidentEdges (mergeVertex wall)).card = 4) :
    iso.datum.targetVertex (mergeVertex other) = mergeVertex wall :=
  DiscreteContraction.map_merge_of_four_valent other.frame.data other.frame.fullDim rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    wall.limit iso.datum (mergeVertex wall) hFour

/-- Discreteness of the wall's merged partition is inherited by every member. -/
theorem limit_discrete (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall)
    (hFour : (GluingDatum.incidentEdges (mergeVertex wall)).card = 4)
    (hDiscrete : wall.limit.vertexPartition (mergeVertex wall) = SheetPartition.discrete degree) :
    other.limit.vertexPartition (mergeVertex other) = SheetPartition.discrete degree := by
  apply DiscreteContraction.eq_discrete_of_relabel _ (iso.datum.vertexPerm (mergeVertex other))
  refine (iso.datum.vertexPartition (mergeVertex other)).symm.trans ?_
  rw [map_merge other iso hFour]
  exact hDiscrete

/-- The three local partitions of an arbitrary member above a discrete
four-valent wall are forced to be discrete. -/
theorem local_partitions (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall)
    (hFour : (GluingDatum.incidentEdges (mergeVertex wall)).card = 4)
    (hDiscrete : wall.limit.vertexPartition (mergeVertex wall) = SheetPartition.discrete degree) :
    other.frame.data.vertexPartition
      (other.frame.edgeOf other.column : other.frame.target.V × other.frame.target.V).1 =
        SheetPartition.discrete degree ∧
    other.frame.data.vertexPartition
      (other.frame.edgeOf other.column : other.frame.target.V × other.frame.target.V).2 =
        SheetPartition.discrete degree ∧
    other.frame.data.edgePartition (other.frame.edgeOf other.column) =
      SheetPartition.discrete degree :=
  DiscreteContraction.partitions_discrete_of_four_valent_iso other.frame.data
    other.frame.fullDim rfl (fst_ne_snd (other.frame.edgeOf other.column))
    (other.frame.numEdges_edgeOf other.column) wall.limit iso.datum (mergeVertex wall)
    hFour hDiscrete

/-- The four occurrence labels an arbitrary member inherits from the wall's. -/
noncomputable def inheritedStar (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall)
    (hFour : (GluingDatum.incidentEdges (mergeVertex wall)).card = 4)
    (star : FourStar (wall.frame.limitTarget wall.column) (mergeVertex wall)) :
    FourStar (other.frame.limitTarget other.column) (mergeVertex other) :=
  DiscreteContraction.pullbackFourStar other.limit wall.limit iso.datum
    (mergeVertex other) (mergeVertex wall) (map_merge other iso hFour) star

theorem inheritedStar_edge (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall)
    (hFour : (GluingDatum.incidentEdges (mergeVertex wall)).card = 4)
    (star : FourStar (wall.frame.limitTarget wall.column) (mergeVertex wall)) (label : Fin 4) :
    iso.datum.targetEdge ((inheritedStar other iso hFour star).edge label) = star.edge label :=
  DiscreteContraction.pullbackFourStar_edge other.limit wall.limit iso.datum
    (mergeVertex other) (mergeVertex wall) (map_merge other iso hFour) star label

/-- **The pairing index an arbitrary member presents**, in inherited wall
occurrence labels. -/
noncomputable def pairing (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall)
    (hFour : (GluingDatum.incidentEdges (mergeVertex wall)).card = 4)
    (star : FourStar (wall.frame.limitTarget wall.column) (mergeVertex wall)) : Fin 3 :=
  W4IncomingTargetNormalization.pairing other.frame.data other.frame.fullDim rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    (inheritedStar other iso hFour star)

theorem pairing_placement (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall)
    (hFour : (GluingDatum.incidentEdges (mergeVertex wall)).card = 4)
    (star : FourStar (wall.frame.limitTarget wall.column) (mergeVertex wall)) :
    (∀ edge ∈ GluingDatum.incidentEdges (mergeVertex other),
      IncomingTargetExpansion.right rfl (fst_ne_snd (other.frame.edgeOf other.column))
        (other.frame.numEdges_edgeOf other.column) edge =
      (inheritedStar other iso hFour star).right (pairing other iso hFour star) edge) ∨
    (∀ edge ∈ GluingDatum.incidentEdges (mergeVertex other),
      IncomingTargetExpansion.right rfl (fst_ne_snd (other.frame.edgeOf other.column))
        (other.frame.numEdges_edgeOf other.column) edge =
      !((inheritedStar other iso hFour star).right (pairing other iso hFour star) edge)) :=
  W4IncomingTargetNormalization.pairing_placement other.frame.data other.frame.fullDim rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    (inheritedStar other iso hFour star)

/-! ## 2.  The uniform expansion at a pairing, and its contraction data -/

/-- The uniform expansion of the wall's limit at the pairing `q`: the wall
partition is duplicated at both expanded endpoints and on the regrown
occurrence. -/
noncomputable abbrev expansion (wall : Regrowth core y degree)
    (star : FourStar (wall.frame.limitTarget wall.column) (mergeVertex wall)) (q : Fin 3) :
    GluingDatum (graph (wall.frame.limitTarget wall.column) (mergeVertex wall) (star.right q))
      degree :=
  GeometricUniformExpansion.data wall.limit (mergeVertex wall) (star.right q)

section Uniform

variable (star : FourStar (wall.frame.limitTarget wall.column) (mergeVertex wall)) (q : Fin 3)

theorem expansion_old (vertex : (wall.frame.limitTarget wall.column).V) :
    (expansion wall star q).vertexPartition
        (oldVertex (wall.frame.limitTarget wall.column) vertex) =
      wall.limit.vertexPartition vertex :=
  GeometricUniformExpansion.vertexPartition wall.limit (mergeVertex wall) (star.right q)
    (oldVertex (wall.frame.limitTarget wall.column) vertex)

theorem expansion_fresh :
    (expansion wall star q).vertexPartition (freshVertex (wall.frame.limitTarget wall.column)) =
      wall.limit.vertexPartition (mergeVertex wall) :=
  GeometricUniformExpansion.vertexPartition wall.limit (mergeVertex wall) (star.right q)
    (freshVertex (wall.frame.limitTarget wall.column))

/-- At a **discrete** wall the two expanded endpoints rejoin to the wall
partition.  This is the `hMerge` input of `Count.W4LimitContraction.limitIso`. -/
theorem expansion_merge
    (hDiscrete : wall.limit.vertexPartition (mergeVertex wall) = SheetPartition.discrete degree) :
    SheetPartition.join
        ((expansion wall star q).vertexPartition
          (oldVertex (wall.frame.limitTarget wall.column) (mergeVertex wall)))
        ((expansion wall star q).vertexPartition
          (freshVertex (wall.frame.limitTarget wall.column))) =
      wall.limit.vertexPartition (mergeVertex wall) := by
  rw [expansion_old, expansion_fresh, hDiscrete]
  exact W4LimitContraction.join_discrete_discrete degree

/-- Every retained occurrence keeps the wall's occurrence partition. -/
theorem expansion_retained (edge : (wall.frame.limitTarget wall.column).edges) :
    (expansion wall star q).edgePartition
        (occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall)
          (star.right q) (some edge)) = wall.limit.edgePartition edge :=
  GeometricUniformExpansion.edgePartition_some _ _ _ _

/-! ## 3.  A W4 candidate at a pairing -/

/-- The frame a candidate presentation carries. -/
noncomputable def candFrame
    (data : GluingDatum (graph (wall.frame.limitTarget wall.column) (mergeVertex wall)
      (star.right q)) degree)
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation data (Fin p))
    (ident : CoreIdentification core data) : Frame core degree :=
  ⟨_, data, fullDim, ident⟩

/-- The regrowth it becomes once its vanishing coordinate is named. -/
noncomputable def candRegrowth
    (data : GluingDatum (graph (wall.frame.limitTarget wall.column) (mergeVertex wall)
      (star.right q)) degree)
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation data (Fin p))
    (ident : CoreIdentification core data) (column : Fin p)
    (degenerate : (candFrame star q data fullDim ident).DegenerateAt y column) :
    Regrowth core y degree :=
  ⟨candFrame star q data fullDim ident, column, degenerate⟩

/-- The `hMerge` input of `Count.W4LimitContraction.limitIso`, derived from the
two expanded endpoint partitions at a **discrete** wall. -/
theorem cand_merge
    (hDiscrete : wall.limit.vertexPartition (mergeVertex wall) = SheetPartition.discrete degree)
    (data : GluingDatum (graph (wall.frame.limitTarget wall.column) (mergeVertex wall)
      (star.right q)) degree)
    (side_old : data.vertexPartition
        (oldVertex (wall.frame.limitTarget wall.column) (mergeVertex wall)) =
      wall.limit.vertexPartition (mergeVertex wall))
    (side_fresh : data.vertexPartition (freshVertex (wall.frame.limitTarget wall.column)) =
      wall.limit.vertexPartition (mergeVertex wall)) :
    SheetPartition.join
        (data.vertexPartition
          (oldVertex (wall.frame.limitTarget wall.column) (mergeVertex wall)))
        (data.vertexPartition (freshVertex (wall.frame.limitTarget wall.column))) =
      wall.limit.vertexPartition (mergeVertex wall) := by
  rw [side_old, side_fresh, hDiscrete]
  exact W4LimitContraction.join_discrete_discrete degree

/-- **The canonical limit dictionary of a candidate.**  Contracting the regrown
occurrence returns the wall's own limit, by the literal contraction
dictionaries; no choice enters. -/
noncomputable def candDatumIso
    (hDiscrete : wall.limit.vertexPartition (mergeVertex wall) = SheetPartition.discrete degree)
    (data : GluingDatum (graph (wall.frame.limitTarget wall.column) (mergeVertex wall)
      (star.right q)) degree)
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation data (Fin p))
    (ident : CoreIdentification core data) (column : Fin p)
    (degenerate : (candFrame star q data fullDim ident).DegenerateAt y column)
    (column_eq : (candFrame star q data fullDim ident).edgeOf column =
      occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall) (star.right q) none)
    (side_old : data.vertexPartition
        (oldVertex (wall.frame.limitTarget wall.column) (mergeVertex wall)) =
      wall.limit.vertexPartition (mergeVertex wall))
    (side_fresh : data.vertexPartition (freshVertex (wall.frame.limitTarget wall.column)) =
      wall.limit.vertexPartition (mergeVertex wall))
    (away : ∀ vertex : (wall.frame.limitTarget wall.column).V, vertex ≠ mergeVertex wall →
      data.vertexPartition (oldVertex (wall.frame.limitTarget wall.column) vertex) =
        wall.limit.vertexPartition vertex)
    (retained : ∀ edge : (wall.frame.limitTarget wall.column).edges,
      data.edgePartition (occurrenceEquiv (wall.frame.limitTarget wall.column)
        (mergeVertex wall) (star.right q) (some edge)) = wall.limit.edgePartition edge) :
    GeometricDatumIso
      (candRegrowth star q data fullDim ident column degenerate).limit wall.limit :=
  W4LimitContraction.limitIso rfl
    (fst_ne_snd ((candFrame star q data fullDim ident).edgeOf column))
    ((candFrame star q data fullDim ident).numEdges_edgeOf column) column_eq
    wall.limit data (cand_merge star q hDiscrete data side_old side_fresh) away retained

/-- **A W4 candidate at the pairing `q`.**  The first five fields present a
full-dimensional core-identified regrowth of the expanded wall whose vanishing
coordinate is the regrown occurrence; the next four are the three partition
conditions `Count.W4LimitContraction` asks of a target expansion; the last two
say that the resulting canonical contraction dictionary is over the core. -/
structure Candidate (hy : Nondegenerate y) (wall : Regrowth core y degree)
    (hDiscrete : wall.limit.vertexPartition (mergeVertex wall) = SheetPartition.discrete degree)
    (star : FourStar (wall.frame.limitTarget wall.column) (mergeVertex wall)) (q : Fin 3) where
  /-- The candidate's gluing datum on the expanded wall target. -/
  data : GluingDatum (graph (wall.frame.limitTarget wall.column) (mergeVertex wall)
    (star.right q)) degree
  /-- Its full-dimensional presentation. -/
  fullDim : FullDimensionalSource.FullDimensionalSourcePresentation data (Fin p)
  /-- Its identification of the stable graph with the requested core. -/
  ident : CoreIdentification core data
  /-- The coordinate that vanishes at the wall request. -/
  column : Fin p
  /-- It really vanishes, and nothing else does. -/
  degenerate : (candFrame star q data fullDim ident).DegenerateAt y column
  /-- It is the regrown occurrence. -/
  column_eq : (candFrame star q data fullDim ident).edgeOf column =
    occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall) (star.right q) none
  /-- The old expanded endpoint carries the wall partition. -/
  side_old : data.vertexPartition
      (oldVertex (wall.frame.limitTarget wall.column) (mergeVertex wall)) =
    wall.limit.vertexPartition (mergeVertex wall)
  /-- …and so does the fresh one. -/
  side_fresh : data.vertexPartition (freshVertex (wall.frame.limitTarget wall.column)) =
    wall.limit.vertexPartition (mergeVertex wall)
  /-- Away from the wall nothing changes. -/
  away : ∀ vertex : (wall.frame.limitTarget wall.column).V, vertex ≠ mergeVertex wall →
    data.vertexPartition (oldVertex (wall.frame.limitTarget wall.column) vertex) =
      wall.limit.vertexPartition vertex
  /-- Retained occurrences keep the wall's occurrence partitions. -/
  retained : ∀ edge : (wall.frame.limitTarget wall.column).edges,
    data.edgePartition (occurrenceEquiv (wall.frame.limitTarget wall.column)
      (mergeVertex wall) (star.right q) (some edge)) = wall.limit.edgePartition edge
  /-- The canonical contraction dictionary preserves the inherited branch
  labels. -/
  overCore_vertex : ∀ branch : StableGraphIncidence.BranchVertex
      (candRegrowth star q data fullDim ident column degenerate).limit,
    (InheritedLimitIncidence.coreIdentification wall hy).vertex
        ((candDatumIso star q hDiscrete data fullDim ident column degenerate column_eq
          side_old side_fresh away retained).branchVertexEquiv
            (InheritedLimitRows.limit_connected _) branch) =
      (InheritedLimitIncidence.coreIdentification
        (candRegrowth star q data fullDim ident column degenerate) hy).vertex branch
  /-- …and the inherited row labels. -/
  overCore_row : ∀ row : W4StableSource.StablePath
      (candRegrowth star q data fullDim ident column degenerate).limit,
    (InheritedLimitIncidence.coreIdentification wall hy).row
        ((candDatumIso star q hDiscrete data fullDim ident column degenerate column_eq
          side_old side_fresh away retained).stablePathEquiv
            (InheritedLimitRows.limit_connected _) row) =
      (InheritedLimitIncidence.coreIdentification
        (candRegrowth star q data fullDim ident column degenerate) hy).row row

namespace Candidate

variable {star q}
variable {hDiscrete : wall.limit.vertexPartition (mergeVertex wall) = SheetPartition.discrete degree}

/-- The candidate's frame. -/
noncomputable def frame (c : Candidate hy wall hDiscrete star q) : Frame core degree :=
  candFrame star q c.data c.fullDim c.ident

/-- The candidate's regrowth. -/
noncomputable def regrowth (c : Candidate hy wall hDiscrete star q) : Regrowth core y degree :=
  candRegrowth star q c.data c.fullDim c.ident c.column c.degenerate

theorem regrowth_frame (c : Candidate hy wall hDiscrete star q) : c.regrowth.frame = c.frame := rfl

/-- The candidate's canonical limit dictionary. -/
noncomputable def datumIso (c : Candidate hy wall hDiscrete star q) :
    GeometricDatumIso c.regrowth.limit wall.limit :=
  candDatumIso star q hDiscrete c.data c.fullDim c.ident c.column c.degenerate c.column_eq
    c.side_old c.side_fresh c.away c.retained

/-- **A candidate is a labelled member of the wall's geometric star.** -/
noncomputable def starLimitIso (c : Candidate hy wall hDiscrete star q) :
    GeometricStar.LimitIso hy c.regrowth wall where
  datum := c.datumIso
  overCore_vertex := c.overCore_vertex
  overCore_row := c.overCore_row

noncomputable def starMember (c : Candidate hy wall hDiscrete star q) :
    GeometricStar.StarMember hy wall := ⟨c.regrowth, ⟨c.starLimitIso⟩⟩

@[simp] theorem starMember_member (c : Candidate hy wall hDiscrete star q) :
    (c.starMember).member = c.regrowth := rfl

/-- The regrown occurrence carries the wall partition.  This is forced by the
candidate's own `refines_left` field together with the discrete endpoint
partition; no local resolution datum enters. -/
theorem newEdge_discrete (c : Candidate hy wall hDiscrete star q) :
    c.data.edgePartition (occurrenceEquiv (wall.frame.limitTarget wall.column)
        (mergeVertex wall) (star.right q) none) =
      wall.limit.vertexPartition (mergeVertex wall) := by
  have hSide : c.data.vertexPartition
      (oldVertex (wall.frame.limitTarget wall.column) (mergeVertex wall)) =
      SheetPartition.discrete degree := c.side_old.trans hDiscrete
  have hRefines := c.data.refines_left (occurrenceEquiv (wall.frame.limitTarget wall.column)
    (mergeVertex wall) (star.right q) none)
  rw [occurrenceEquiv_none] at hRefines
  have hOld : (c.data.edgePartition (occurrenceEquiv (wall.frame.limitTarget wall.column)
      (mergeVertex wall) (star.right q) none)).Refines
      (c.data.vertexPartition
        (oldVertex (wall.frame.limitTarget wall.column) (mergeVertex wall))) := hRefines
  rw [hSide] at hOld
  rw [hDiscrete]
  exact DiscreteContraction.eq_discrete_of_refines _ hOld

/-- **A candidate's datum is literally the uniform expansion at its pairing**: an
equality of gluing data, not an isomorphism. -/
theorem data_eq (c : Candidate hy wall hDiscrete star q) :
    c.data = expansion wall star q :=
  UniformExpansionRecognition.eq_uniformExpansion wall.limit (mergeVertex wall) (star.right q)
    c.data c.side_old c.side_fresh c.away c.newEdge_discrete c.retained

/-- **The candidate's source contraction, read through its own limit
dictionary, is the wall's own source endpoint.** -/
theorem member_contractSourceVertex (c : Candidate hy wall hDiscrete star q)
    (vertex : c.data.SourceVertex) :
    c.datumIso.sourceVertexEquiv (InheritedLimitBranches.vertexMap c.regrowth vertex) =
      wall.limit.sourceEndpoint
        (contractVertex (wall.frame.limitTarget wall.column) (mergeVertex wall) vertex.1.1)
        vertex.1.2 :=
  W4LimitContraction.sourceVertexEquiv_sourceVertexMap rfl
    (fst_ne_snd (c.frame.edgeOf c.column)) (c.frame.numEdges_edgeOf c.column) c.column_eq
    wall.limit c.data (cand_merge star q hDiscrete c.data c.side_old c.side_fresh)
    c.away c.retained vertex

/-- **The candidate's retained occurrence embedding**, on the underlying
occurrence/sheet pair. -/
theorem member_edgeEmbedding_val (c : Candidate hy wall hDiscrete star q)
    (edge : c.regrowth.limit.SourceEdge) :
    (InheritedLimitRows.edgeEmbedding c.regrowth edge).1 =
      (occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall) (star.right q)
          (some (c.datumIso.sourceEdgeEquiv edge).1.1),
        (c.datumIso.sourceEdgeEquiv edge).1.2) := by
  have hVal : (c.datumIso.sourceEdgeEquiv edge).1 =
      (W4LimitContraction.edgeEquiv rfl (fst_ne_snd (c.frame.edgeOf c.column))
        (c.frame.numEdges_edgeOf c.column) c.column_eq edge.1.1, edge.1.2) :=
    W4LimitContraction.sourceEdgeEquiv_val rfl (fst_ne_snd (c.frame.edgeOf c.column))
      (c.frame.numEdges_edgeOf c.column) c.column_eq wall.limit c.data
      (cand_merge star q hDiscrete c.data c.side_old c.side_fresh) c.away c.retained edge
  rw [hVal]
  refine (IncomingNormalizationRows.sourceEdgeEmbedding_val c.data rfl
    (fst_ne_snd (c.frame.edgeOf c.column)) (c.frame.numEdges_edgeOf c.column) edge).trans ?_
  exact Prod.ext (W4LimitContraction.occurrenceEquiv_edgeEquiv rfl
    (fst_ne_snd (c.frame.edgeOf c.column)) (c.frame.numEdges_edgeOf c.column) c.column_eq
    edge.1.1).symm rfl

end Candidate

end Uniform

/-! ## 4.  The upward frame isomorphism -/

section Exhaustion

variable (hFour : (GluingDatum.incidentEdges (mergeVertex wall)).card = 4)
  (hDiscrete : wall.limit.vertexPartition (mergeVertex wall) = SheetPartition.discrete degree)
  (star : FourStar (wall.frame.limitTarget wall.column) (mergeVertex wall))

/-- The pairing index an arbitrary member of the wall's star presents. -/
noncomputable abbrev index (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) : Fin 3 :=
  pairing other iso hFour star

/-- **Step one.**  Normalize the arbitrary frame onto the uniform expansion of
its *own* limit, at its own pairing.  Legitimate because the member's merged
partition is discrete (`limit_discrete`). -/
noncomputable def normIso (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) :
    GeometricDatumIso other.frame.data
      (GeometricUniformExpansion.data other.limit (mergeVertex other)
        ((inheritedStar other iso hFour star).right (index hFour star other iso))) :=
  DiscreteW4Normalization.datumIso other.frame.data other.frame.fullDim rfl
    (fst_ne_snd (other.frame.edgeOf other.column))
    (other.frame.numEdges_edgeOf other.column)
    (inheritedStar other iso hFour star) (limit_discrete other iso hFour hDiscrete)

/-- Side compatibility for the transported expansion is a theorem of the four
inherited occurrence labels, not a further choice. -/
theorem right_map (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall)
    (edge : (other.frame.limitTarget other.column).edges) :
    star.right (index hFour star other iso) (iso.datum.targetEdge edge) =
      (inheritedStar other iso hFour star).right (index hFour star other iso) edge :=
  GeometricUniformExpansion.right_map_of_star_edges iso.datum (mergeVertex other)
    (mergeVertex wall) (inheritedStar other iso hFour star) star
    (inheritedStar_edge other iso hFour star) _ edge

/-- **Step two.**  Carry that uniform expansion onto the uniform expansion of
the wall along the given limit isomorphism. -/
noncomputable def transIso (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) :
    GeometricDatumIso
      (GeometricUniformExpansion.data other.limit (mergeVertex other)
        ((inheritedStar other iso hFour star).right (index hFour star other iso)))
      (expansion wall star (index hFour star other iso)) :=
  GeometricUniformExpansion.lift iso.datum (mergeVertex other) (mergeVertex wall)
    (map_merge other iso hFour) _ _ (right_map hFour star other iso)

variable (cand : ∀ q : Fin 3, Candidate hy wall hDiscrete star q)

/-- **The datum half of the upward lift**: an actual geometric isomorphism from
the arbitrary frame's datum onto the candidate's datum.  The third step is the
literal equality `Candidate.data_eq`, moved across by
`Count.UniformExpansionRecognition.ofEq`. -/
noncomputable def frameDatum (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) :
    GeometricDatumIso other.frame.data (cand (index hFour star other iso)).data :=
  ((normIso hFour hDiscrete star other iso).trans (transIso hFour star other iso)).trans
    (UniformExpansionRecognition.ofEq
      (Candidate.data_eq (cand (index hFour star other iso))).symm)

theorem frameDatum_sourceVertex (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (vertex : other.frame.data.SourceVertex) :
    ((frameDatum hFour hDiscrete star cand other iso).sourceVertexEquiv vertex).1 =
      ((transIso hFour star other iso).sourceVertexEquiv
        ((normIso hFour hDiscrete star other iso).sourceVertexEquiv vertex)).1 :=
  UniformExpansionRecognition.ofEq_sourceVertexEquiv
    (Candidate.data_eq (cand (index hFour star other iso))).symm
    ((transIso hFour star other iso).sourceVertexEquiv
      ((normIso hFour hDiscrete star other iso).sourceVertexEquiv vertex))

theorem frameDatum_sourceEdge (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (edge : other.frame.data.SourceEdge) :
    ((frameDatum hFour hDiscrete star cand other iso).sourceEdgeEquiv edge).1 =
      ((transIso hFour star other iso).sourceEdgeEquiv
        ((normIso hFour hDiscrete star other iso).sourceEdgeEquiv edge)).1 :=
  UniformExpansionRecognition.ofEq_sourceEdgeEquiv
    (Candidate.data_eq (cand (index hFour star other iso))).symm
    ((transIso hFour star other iso).sourceEdgeEquiv
      ((normIso hFour hDiscrete star other iso).sourceEdgeEquiv edge))

/-- **The branch square.**  Contracting the arbitrary source and reading the
result in the wall agrees with transporting first and contracting the
candidate's source. -/
theorem source_square (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (vertex : other.frame.data.SourceVertex) :
    (cand (index hFour star other iso)).datumIso.sourceVertexEquiv
        (InheritedLimitBranches.vertexMap (cand (index hFour star other iso)).regrowth
          ((frameDatum hFour hDiscrete star cand other iso).sourceVertexEquiv vertex)) =
      iso.datum.sourceVertexEquiv (InheritedLimitBranches.vertexMap other vertex) := by
  have hMember := Candidate.member_contractSourceVertex (cand (index hFour star other iso))
    ((frameDatum hFour hDiscrete star cand other iso).sourceVertexEquiv vertex)
  have hVal := frameDatum_sourceVertex hFour hDiscrete star cand other iso vertex
  have hNorm : InheritedLimitBranches.vertexMap other vertex =
      GeometricUniformExpansion.contractSourceVertex other.limit (mergeVertex other)
        ((inheritedStar other iso hFour star).right (index hFour star other iso))
        ((normIso hFour hDiscrete star other iso).sourceVertexEquiv vertex) :=
    DiscreteW4Normalization.contractSourceVertex_datumIso other.frame.data other.frame.fullDim
      rfl (fst_ne_snd (other.frame.edgeOf other.column))
      (other.frame.numEdges_edgeOf other.column) (inheritedStar other iso hFour star)
      (limit_discrete other iso hFour hDiscrete) vertex
  have hLift := GeometricUniformExpansion.contractSourceVertex_lift iso.datum
    (mergeVertex other) (mergeVertex wall) (map_merge other iso hFour) _ _
    (right_map hFour star other iso)
    ((normIso hFour hDiscrete star other iso).sourceVertexEquiv vertex)
  rw [hMember, hVal, hNorm, hLift]
  exact (UniformExpansionRecognition.contractSourceVertex_eq_sourceEndpoint wall.limit
    (mergeVertex wall) (star.right (index hFour star other iso)) _).symm

/-- **The row square**, on retained quotient-source occurrences. -/
theorem edge_square (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (edge : other.limit.SourceEdge) :
    (frameDatum hFour hDiscrete star cand other iso).sourceEdgeEquiv
        (InheritedLimitRows.edgeEmbedding other edge) =
      InheritedLimitRows.edgeEmbedding (cand (index hFour star other iso)).regrowth
        (StarFrameIso.transfer iso (cand (index hFour star other iso)).starLimitIso edge) := by
  apply Subtype.ext
  have hNorm : (normIso hFour hDiscrete star other iso).sourceEdgeEquiv
      (InheritedLimitRows.edgeEmbedding other edge) =
      GeometricUniformExpansion.retainedSourceEdge other.limit (mergeVertex other)
        ((inheritedStar other iso hFour star).right (index hFour star other iso)) edge :=
    DiscreteW4Normalization.retainedSourceEdge_datumIso other.frame.data other.frame.fullDim rfl
      (fst_ne_snd (other.frame.edgeOf other.column))
      (other.frame.numEdges_edgeOf other.column) (inheritedStar other iso hFour star)
      (limit_discrete other iso hFour hDiscrete) edge
  have hLift : (transIso hFour star other iso).sourceEdgeEquiv
      (GeometricUniformExpansion.retainedSourceEdge other.limit (mergeVertex other)
        ((inheritedStar other iso hFour star).right (index hFour star other iso)) edge) =
      GeometricUniformExpansion.retainedSourceEdge wall.limit (mergeVertex wall)
        (star.right (index hFour star other iso)) (iso.datum.sourceEdgeEquiv edge) :=
    GeometricUniformExpansion.retainedSourceEdge_lift iso.datum (mergeVertex other)
      (mergeVertex wall) (map_merge other iso hFour) _ _ (right_map hFour star other iso) edge
  have hMember := Candidate.member_edgeEmbedding_val (cand (index hFour star other iso))
    (StarFrameIso.transfer iso (cand (index hFour star other iso)).starLimitIso edge)
  have hTransfer : (cand (index hFour star other iso)).datumIso.sourceEdgeEquiv
      (StarFrameIso.transfer iso (cand (index hFour star other iso)).starLimitIso edge) =
      iso.datum.sourceEdgeEquiv edge :=
    StarFrameIso.datum_sourceEdgeEquiv_transfer iso
      (cand (index hFour star other iso)).starLimitIso edge
  rw [frameDatum_sourceEdge, hNorm, hLift, hMember, hTransfer]
  rfl

/-- **The upward frame isomorphism.**  An arbitrary regrowth of the core
carrying *any* labelled limit isomorphism to the wall is isomorphic over the
labelled core to the candidate at its own pairing index.  Every hypothesis is
displayed. -/
noncomputable def frameIso (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) :
    FrameIso other.frame (cand (index hFour star other iso)).frame :=
  StarFrameIso.ofLimitSquare iso (cand (index hFour star other iso)).starLimitIso
    (frameDatum hFour hDiscrete star cand other iso)
    (source_square hFour hDiscrete star cand other iso)
    (edge_square hFour hDiscrete star cand other iso)

/-! ## 5.  Exhaustion -/

include hFour in
/-- **Exhaustion.**  Every member of the wall's labelled geometric star lies in
one of the three candidate classes. -/
theorem exists_cls_eq (member : GeometricStar.StarMember hy wall) :
    ∃ q : Fin 3, member.cls = ((cand q).starMember).cls := by
  obtain ⟨limIso⟩ := member.specializes
  exact ⟨index hFour star member.member limIso,
    Quotient.sound ⟨frameIso hFour hDiscrete star cand member.member limIso⟩⟩

include hFour in
theorem cls_surjective :
    Function.Surjective fun q : Fin 3 ↦ ((cand q).starMember).cls := by
  refine Quotient.ind ?_
  intro member
  obtain ⟨q, hq⟩ := exists_cls_eq hFour hDiscrete star cand member
  exact ⟨q, hq.symm⟩

include hFour hDiscrete star cand in
/-- **The star has at most three classes**, unconditionally in the candidate
package: no distinctness receipt is used. -/
theorem card_le_three : Fintype.card (GeometricStar.Star hy wall) ≤ 3 := by
  have h := Fintype.card_le_of_surjective _ (cls_surjective hFour hDiscrete star cand)
  simpa using h

/-! ## 6.  Distinctness of the three candidates, and the exact count -/

/-- A frame isomorphism transports each column label of the source frame to the
column label its induced permutation names. -/
theorem targetEdge_column {k l : Frame core degree} (fi : FrameIso k l) (c : Fin p) :
    fi.datum.targetEdge (k.fullDim.labelling.targetEdge c) =
      l.fullDim.labelling.targetEdge (fi.column c) :=
  (l.fullDim.labelling.targetEdge.apply_symm_apply
    (fi.datum.targetEdge (k.fullDim.labelling.targetEdge c))).symm

theorem retainedColumns_limitColumns (w w' : Regrowth core y degree)
    (limIso : GeometricDatumIso w.limit w'.limit) (c : {c : Fin p // c ≠ w.column}) :
    StarMetricCompatibility.retainedColumns w'.frame w'.column
        (InheritedLimitRows.limitColumns w w' limIso c) =
      limIso.targetEdge (StarMetricCompatibility.retainedColumns w.frame w.column c) := by
  simp [InheritedLimitRows.limitColumns]

/-- A candidate's retained column labels are exactly the wall's retained
occurrences, read through its own canonical limit dictionary. -/
theorem occurrence_retained {q : Fin 3} (c : Candidate hy wall hDiscrete star q)
    (col : {col : Fin p // col ≠ c.regrowth.column}) :
    occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall) (star.right q)
        (some (c.datumIso.targetEdge
          (StarMetricCompatibility.retainedColumns c.regrowth.frame c.regrowth.column col))) =
      c.regrowth.frame.fullDim.labelling.targetEdge col.1 :=
  (W4LimitContraction.occurrenceEquiv_edgeEquiv rfl
    (fst_ne_snd (c.regrowth.frame.edgeOf c.regrowth.column))
    (c.regrowth.frame.numEdges_edgeOf c.regrowth.column) c.column_eq _).trans
    (InheritedLimitRows.unfoldEdge_retainedColumns c.regrowth col)

/-- The composite limit dictionary between two candidates. -/
noncomputable def candLimIso (first second : Fin 3) :
    GeometricDatumIso (cand first).regrowth.limit (cand second).regrowth.limit :=
  (cand first).datumIso.trans ((cand second).datumIso).symm

theorem candLimIso_targetEdge_apply (first second : Fin 3)
    (edge : ((cand first).regrowth.frame.limitTarget (cand first).regrowth.column).edges) :
    (candLimIso hDiscrete star cand first second).targetEdge edge =
      (cand second).datumIso.targetEdge.symm ((cand first).datumIso.targetEdge edge) := rfl

theorem candLimIso_targetEdge (first second : Fin 3)
    (edge : ((cand first).regrowth.frame.limitTarget (cand first).regrowth.column).edges) :
    (cand second).datumIso.targetEdge
        ((candLimIso hDiscrete star cand first second).targetEdge edge) =
      (cand first).datumIso.targetEdge edge := by
  rw [candLimIso_targetEdge_apply, Equiv.apply_symm_apply]

/-- Both candidates are members of the wall's star, so the composite preserves
the inherited row labels. -/
theorem candLimIso_rowLabel (first second : Fin 3)
    (row : W4StableSource.StablePath (cand first).regrowth.limit) :
    InheritedLimitRows.rowLabel (cand second).regrowth hy
        ((candLimIso hDiscrete star cand first second).stablePathEquiv
          (InheritedLimitRows.limit_connected (cand first).regrowth) row) =
      InheritedLimitRows.rowLabel (cand first).regrowth hy row :=
  ((cand first).starLimitIso.trans ((cand second).starLimitIso).symm).overCore_row row

/-- **Request-free column rigidity at this wall.**  Every frame isomorphism
between two candidates induces exactly the retained-column dictionary of their
composite limit isomorphism (`Count.FrameColumnRigidity.column_eq_allColumns`);
no coordinate-distinctness receipt and no choice of request enters. -/
theorem column_eq_limitColumns (first second : Fin 3)
    (fi : FrameIso (cand first).regrowth.frame (cand second).regrowth.frame) :
    fi.column = InheritedLimitRows.allColumns (cand first).regrowth (cand second).regrowth
      (candLimIso hDiscrete star cand first second) :=
  FrameColumnRigidity.column_eq_allColumns (cand first).regrowth (cand second).regrowth hy
    (candLimIso hDiscrete star cand first second)
    (candLimIso_rowLabel hDiscrete star cand first second) fi

/-- **The canonical occurrence labels of the two expansions are matched.**  This
is the `hlabel` input of `Count.W4PairingRigidity.pairing_eq_of_expansionIso`. -/
theorem occurrence_map (first second : Fin 3)
    (fi : FrameIso (cand first).regrowth.frame (cand second).regrowth.frame)
    (label : Option (wall.frame.limitTarget wall.column).edges) :
    fi.datum.targetEdge
        (occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall)
          (star.right first) label) =
      occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall)
        (star.right second) label := by
  cases label with
  | none =>
    have hcol : fi.column (cand first).regrowth.column = (cand second).regrowth.column := by
      rw [column_eq_limitColumns hDiscrete star cand first second]
      exact InheritedLimitRows.allColumns_collapsed (cand first).regrowth
        (cand second).regrowth (candLimIso hDiscrete star cand first second)
    refine (congrArg fi.datum.targetEdge ((cand first).column_eq).symm).trans ?_
    refine (targetEdge_column fi (cand first).regrowth.column).trans ?_
    rw [hcol]
    exact (cand second).column_eq
  | some edge =>
    obtain ⟨col, hEdge⟩ : ∃ col : {col : Fin p // col ≠ (cand first).regrowth.column},
        (cand first).datumIso.targetEdge
          (StarMetricCompatibility.retainedColumns (cand first).regrowth.frame
            (cand first).regrowth.column col) = edge :=
      ⟨(StarMetricCompatibility.retainedColumns (cand first).regrowth.frame
          (cand first).regrowth.column).symm ((cand first).datumIso.targetEdge.symm edge), by
          rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]⟩
    have hLeft : occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall)
        (star.right first) (some edge) =
        (cand first).regrowth.frame.fullDim.labelling.targetEdge col.1 := by
      rw [← hEdge]
      exact occurrence_retained hDiscrete star (cand first) col
    have hColumn : fi.column col.1 =
        (InheritedLimitRows.limitColumns (cand first).regrowth (cand second).regrowth
          (candLimIso hDiscrete star cand first second) col).1 := by
      rw [column_eq_limitColumns hDiscrete star cand first second]
      exact InheritedLimitRows.allColumns_retained (cand first).regrowth (cand second).regrowth
        (candLimIso hDiscrete star cand first second) col
    rw [hLeft, targetEdge_column fi col.1, hColumn]
    refine ((occurrence_retained hDiscrete star (cand second)
      (InheritedLimitRows.limitColumns (cand first).regrowth (cand second).regrowth
        (candLimIso hDiscrete star cand first second) col)).symm).trans ?_
    rw [retainedColumns_limitColumns, candLimIso_targetEdge hDiscrete star cand first second,
      hEdge]

/-- **The pairing index is recovered from the frame.** -/
theorem pairing_eq_of_frameIso (first second : Fin 3)
    (fi : FrameIso (cand first).regrowth.frame (cand second).regrowth.frame) : first = second :=
  W4PairingRigidity.pairing_eq_of_expansionIso star first second
    fi.datum.targetVertex fi.datum.targetEdge fi.datum.ends
    (occurrence_map hDiscrete star cand first second fi)

/-- **The three candidate classes are pairwise distinct.** -/
theorem cls_injective : Function.Injective fun q : Fin 3 ↦ ((cand q).starMember).cls := by
  intro first second h
  obtain ⟨fi⟩ := Quotient.exact h
  exact pairing_eq_of_frameIso hDiscrete star cand first second fi

include hFour in
/-- **The wall's labelled geometric star is `Fin 3`.** -/
noncomputable def starEquiv : Fin 3 ≃ GeometricStar.Star hy wall :=
  Equiv.ofBijective _
    ⟨cls_injective hDiscrete star cand, cls_surjective hFour hDiscrete star cand⟩

include hFour hDiscrete star cand in
/-- **Exact cardinality**, not a lower bound. -/
theorem card_eq_three : Fintype.card (GeometricStar.Star hy wall) = 3 := by
  rw [← Fintype.card_congr (starEquiv hFour hDiscrete star cand), Fintype.card_fin]

include hFour hDiscrete star cand in
theorem card_odd : Odd (Fintype.card (GeometricStar.Star hy wall)) := by
  rw [card_eq_three hFour hDiscrete star cand]
  exact ⟨1, rfl⟩

end Exhaustion

end DraismaVargas.Count.W4WallExhaustion
