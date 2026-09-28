import DraismaVargasCount.W4WallExhaustion
import DraismaVargas.LocalCases.W4Bridge

/-!
# Merge-pinning at an arbitrary wall, without a valency hypothesis

Source: Vargas, Part II (arXiv:2609.09109), the star of a codimension-one wall.

## The problem

`Count.DiscreteContraction.map_merge_of_four_valent` pins the merged vertex of
an arbitrary member of a star by **valency**: full-dimensionality of the
member's own source bounds every non-merge vertex of its limit by valency three
(`GluingDatum.incidentEdges_card_le_three_of_changeMinimalAt`), the merge has
valency four, and an isomorphism preserves valency.  At a wall of valency two or
three that argument dies outright -- a non-merge vertex may have the *same*
valency as the merge -- and `map_merge` is the first line of every exhaustion
argument.

## The column route, and why it does not suffice

A natural route: the merge is the endpoint of the contracted occurrence
`frame.edgeOf column`; `Count.FrameColumnRigidity` proves a frame isomorphism
has identity column component at a wall crossing; so pinning might be free at
every valency.

Section 6 below proves the *positive* half of that route in the strongest form it
has: a geometric frame isomorphism whose column component carries `col` to
`col'` carries the wall occurrence of the first frame to the wall occurrence of
the second, hence its two endpoints to the two endpoints as an unordered pair
(`frameIso_targetEdge_edgeOf`, `frameIso_unorderedEnds`,
`frameIso_maps_wall_ends`).  That really is merge-pinning -- **for a
`GeometricSegmentWalls.FrameIso`**.

It is not the isomorphism the exhaustion argument quantifies over.  There the
isomorphism is a `Count.GeometricStar.LimitIso`, whose data is a
`GeometricDatumIso other.limit wall.limit` between the two *contracted* data:
the wall occurrence has been deleted from both targets, there is no `column`
component, and `Count.GeometricStar.StarMember` asks for exactly such a limit
isomorphism and nothing more.  Two members of one star are in general **not**
frame isomorphic to each other -- that is precisely what `cls_injective` proves
at `w4`, where three pairwise non-frame-isomorphic members share one limit -- so
the limit isomorphism the argument is handed need not come from any frame
isomorphism.  The column route pins the merge exactly in the case the exhaustion
argument is trying to rule out.

## What is proved here instead: excess pins the merge at every valency

The invariant that survives is the **dimension correction**
`GluingDatum.targetExcess v = ch(v) + val(v) - 3`, which is what "codimension
one" means and is what valency four was only ever a proxy for.

* §1 `targetChange_map`, `targetExcess_map` -- `targetExcess` is a geometric
  invariant: an arbitrary `GeometricDatumIso` preserves it.  Proved through
  `GluingDatum.targetChange_eq_card_formula`, so the only inputs are that
  relabelling a sheet partition does not change its number of blocks
  (`card_blocks_relabel`) and that the star of a vertex transports.
* §2 `targetChange_contractDatum_of_ne`, `targetExcess_contractDatum_of_ne` --
  contraction changes nothing away from the merged vertex: at `u ≠ a, b` the
  vertex partition, the star and every incident occurrence partition are carried
  over verbatim, so the excess is literally the old one.
* §3 `eq_merge_of_targetExcess_ne_zero` -- hence in the limit of a
  **change-minimal** datum the merged vertex is the *only* vertex that can carry
  nonzero excess.  No valency, no discreteness, no forest hypothesis.
* §4 `map_merge_of_excess` -- the valency-free replacement for
  `DiscreteContraction.map_merge_of_four_valent`, with `hFour` replaced by
  `hExcess : other.targetExcess vertex ≠ 0`.  The proof is the same four lines.
* §5 the wall-level form.  `IsWall w` is `w.limit.targetExcess (mergeVertex w) ≠
  0`; `map_merge` then has exactly `Count.W4WallExhaustion.map_merge`'s
  conclusion, with `hFour` replaced by `IsWall wall` and `wall` an explicit
  argument rather than a section variable, and is generic in target, degree,
  coordinate and **valency**.  Three ways to
  discharge `IsWall` are supplied, each from inputs available elsewhere in the library:
  `isWall_of_forest` (the source-topology hypothesis of Part I's `lemma-dangling-limit`,
  which gives
  excess exactly `1` via `W4Bridge.targetExcess_contractDatum_merge_eq_one` and
  is the route available at valency two and three), `isWall_of_discrete_four_valent`
  (the `w4` file's own two standing hypotheses, so §5 *recovers*
  `W4WallExhaustion.map_merge` -- see `map_merge_of_four_valent_discrete`), and
  `isWall_of_valid_four_valent`.  `isWall_of_targetExcess_eq_one` takes the
  `equation_c` field the local-case wall interfaces already carry.
  `isWall_of_limitIso` propagates the property to every member of the star.

## What is not proved here

* **`IsWall wall` is a hypothesis, not a theorem.**  Nothing here proves that a
  given wall of the Draisma--Vargas count schedule has nonvanishing excess at
  its merged vertex.  Three sufficient conditions are proved
  (`isWall_of_forest`, `isWall_of_discrete_four_valent`,
  `isWall_of_valid_four_valent`); each has its own input.  In particular
  `isWall_of_forest` assumes
  `ContractionRamification.ContractionForestAt w.frame.data (w.frame.edgeOf w.column)`,
  which is the source-topology statement of Part I's `lemma-dangling-limit` and is not
  derived here -- `LocalCases.W4Bridge` carries it as a hypothesis for the same reason.
  An argument at a `w2*` or `w3*` wall must supply it (or one of the other two inputs);
  this module does not.
* **Nothing is proved about the member's excess.**  `map_merge_of_excess` needs
  `hExcess` only at the *target* vertex; the member side uses nothing but
  `data.ChangeMinimal`, which is `FullDimensionalSourcePresentation.changeMinimal`.
  No statement is made that the member's own merged vertex carries excess.
* **No exhaustion, no star, no cardinality, no multiplicity, no parity.**  This
  module supplies `map_merge` and nothing downstream of it.  It does not build a
  `Candidate`, does not lift a limit isomorphism to a frame isomorphism, and
  makes no statement about `Count.GeometricStar.Star` beyond §6's citation.
* **Nothing about the nine non-`w4` families.**  `w3Four`, `w3Shift`,
  `w3Nd3CoarseFine`, `w3Nd2CoarseFine`, `w2M11`, `w2M1k`, `w2Mkk`, `w2P` and
  `w2R1` are untouched: this module supplies the merge pinning they share, it does not
  exhaust any of them.
* **The column route does not supply `map_merge`.**  §6's theorems are stated as
  positives; what fails is only that a `LimitIso` supplies the `FrameIso` they need.
* `Count.W4WallExhaustion.mergeVertex`, `Count.GeometricStar.LimitIso` and
  `GeometricSegmentWalls.FrameIso` are used exactly as they stand; none is
  weakened or further quotiented.

## Consumers

The exhaustion arguments at the nine non-`w4` wall families (for instance
`M11WallExhaustion.pinned_of_isWall`).
-/

namespace DraismaVargas.Count.MergePinning

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction ContractionRamification
open WallStar (Regrowth Nondegenerate)
open SegmentWalls (Frame)
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 1.  `targetExcess` is a geometric invariant -/

section Invariance

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}

/-- Relabelling a sheet partition does not change how many blocks it has: the
canonical representatives are transported by the permutation. -/
theorem card_blocks_relabel (partition : SheetPartition degree)
    (permutation : Equiv.Perm (Fin degree)) :
    Fintype.card (partition.relabel permutation).Blocks
      = Fintype.card partition.Blocks := by
  refine Fintype.card_congr (Equiv.subtypeEquiv permutation.symm fun sheet ↦ ?_)
  show permutation (partition.repr (permutation.symm sheet)) = sheet ↔
    partition.repr (permutation.symm sheet) = permutation.symm sheet
  constructor
  · intro h
    exact permutation.injective (by rw [h, Equiv.apply_symm_apply])
  · intro h
    rw [h, Equiv.apply_symm_apply]

/-- **The change `ch(v)` is a geometric invariant.**  Nothing but the number of
blocks above the vertex and above each incident occurrence, and the valency,
enters `GluingDatum.targetChange_eq_card_formula`, and all three transport. -/
theorem targetChange_map (iso : GeometricDatumIso first second) (vertex : target₁.V) :
    second.targetChange (iso.targetVertex vertex) = first.targetChange vertex := by
  classical
  rw [GluingDatum.targetChange_eq_card_formula, GluingDatum.targetChange_eq_card_formula]
  have hCard := iso.incidentEdges_card_map vertex
  have hVertex : Fintype.card (second.vertexPartition (iso.targetVertex vertex)).Blocks
      = Fintype.card (first.vertexPartition vertex).Blocks := by
    rw [iso.vertexPartition vertex, card_blocks_relabel]
  have hSum : (∑ edge ∈ GluingDatum.incidentEdges (iso.targetVertex vertex),
        (Fintype.card (second.edgePartition edge).Blocks : ℤ))
      = ∑ edge ∈ GluingDatum.incidentEdges vertex,
        (Fintype.card (first.edgePartition edge).Blocks : ℤ) := by
    refine (Finset.sum_bij (fun edge _ ↦ iso.targetEdge edge) ?_ ?_ ?_ ?_).symm
    · exact fun edge hEdge ↦ (iso.mem_incidentEdges_map vertex edge).mpr hEdge
    · exact fun _ _ _ _ h ↦ iso.targetEdge.injective h
    · intro edge hEdge
      refine ⟨iso.targetEdge.symm edge, ?_, iso.targetEdge.apply_symm_apply edge⟩
      refine (iso.mem_incidentEdges_map vertex _).mp ?_
      rwa [Equiv.apply_symm_apply]
    · intro edge _
      rw [iso.edgePartition edge, card_blocks_relabel]
  rw [hSum, hVertex, hCard]

/-- **The dimension correction `ch(v) + val(v) - 3` is a geometric invariant.**
This is the pinning invariant the rest of the file runs on. -/
theorem targetExcess_map (iso : GeometricDatumIso first second) (vertex : target₁.V) :
    second.targetExcess (iso.targetVertex vertex) = first.targetExcess vertex := by
  show second.targetChange (iso.targetVertex vertex)
      + ((GluingDatum.incidentEdges (iso.targetVertex vertex)).card : ℤ) - 3 = _
  rw [targetChange_map iso vertex, iso.incidentEdges_card_map vertex]
  rfl

end Invariance

/-! ## 2.  Contraction changes nothing away from the merged vertex -/

section Away

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-- **The change is untouched away from the merge.**  At `u ≠ a, b` the vertex
partition is the old one (`contractVertexPartition_of_ne`), the star is carried
across by `foldEdge`, and every surviving occurrence keeps its own partition
(`contractDatum_edgePartition_foldEdge`). -/
theorem targetChange_contractDatum_of_ne (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {u : target.V} (hub : u ≠ b) (hua : u ≠ a) :
    (contractDatum data hc hab hOne).targetChange
        (⟨u, hub⟩ : (GraphContraction.contract target hab hOne).V)
      = data.targetChange u := by
  classical
  have hvp : (contractDatum data hc hab hOne).vertexPartition
      (⟨u, hub⟩ : (GraphContraction.contract target hab hOne).V) = data.vertexPartition u :=
    contractVertexPartition_of_ne data a b (y := ⟨u, hub⟩) hua
  have hCard := card_incidentEdges_contract_of_ne hc hab hOne hub hua
  have hSum : (∑ edge ∈ GluingDatum.incidentEdges
        (⟨u, hub⟩ : (GraphContraction.contract target hab hOne).V),
        (Fintype.card ((contractDatum data hc hab hOne).edgePartition edge).Blocks : ℤ))
      = ∑ edge ∈ GluingDatum.incidentEdges u,
        (Fintype.card (data.edgePartition edge).Blocks : ℤ) := by
    refine (Finset.sum_bij
      (fun f hf ↦ foldEdge hc hab hOne ⟨f, ne_contracted_of_mem_incidentEdges hc hub hua hf⟩)
      (fun _ hf ↦ mem_incidentEdges_foldEdge hc hab hOne hub _ hf)
      (fun _ _ _ _ heq ↦ congrArg Subtype.val (foldEdge_injective hc hab hOne heq))
      (fun e he ↦ ⟨unfoldEdge hc hab hOne e,
        mem_incidentEdges_unfoldEdge hc hab hOne hub hua he,
        foldEdge_unfoldEdge hc hab hOne e _⟩) ?_).symm
    intro f _
    rw [contractDatum_edgePartition_foldEdge]
  rw [GluingDatum.targetChange_eq_card_formula (contractDatum data hc hab hOne)
      (⟨u, hub⟩ : (GraphContraction.contract target hab hOne).V),
    GluingDatum.targetChange_eq_card_formula data u, hSum, hvp, ← hCard]

/-- **The excess is untouched away from the merge.** -/
theorem targetExcess_contractDatum_of_ne (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {u : target.V} (hub : u ≠ b) (hua : u ≠ a) :
    (contractDatum data hc hab hOne).targetExcess
        (⟨u, hub⟩ : (GraphContraction.contract target hab hOne).V)
      = data.targetExcess u := by
  have hChange := targetChange_contractDatum_of_ne data hc hab hOne hub hua
  have hCard := card_incidentEdges_contract_of_ne hc hab hOne hub hua
  unfold GluingDatum.targetExcess
  rw [hChange, ← hCard]

/-! ## 3.  The merged vertex is the only vertex that can carry excess -/

/-- **Excess pins the merge, at every valency.**  The datum being contracted is
change-minimal -- this is `FullDimensionalSourcePresentation.changeMinimal`, the
same input the four-valent argument uses -- so every vertex of the limit other
than the merge inherits excess zero verbatim.  Hence any vertex of the limit with
nonzero excess *is* the merge.  Compare
`Count.DiscreteContraction.eq_merge_of_four_valent`, which reaches the same
conclusion from valency four and cannot be run at valency two or three. -/
theorem eq_merge_of_targetExcess_ne_zero (data : GluingDatum target degree)
    (hMinimal : data.ChangeMinimal)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (vertex : (GraphContraction.contract target hab hOne).V)
    (hExcess : (contractDatum data hc hab hOne).targetExcess vertex ≠ 0) :
    vertex = ⟨a, hab⟩ := by
  obtain ⟨u, hub⟩ := vertex
  apply Subtype.ext
  by_contra hua
  exact hExcess
    ((targetExcess_contractDatum_of_ne data hc hab hOne hub hua).trans (hMinimal u))

/-! ## 4.  The valency-free `map_merge` -/

variable {otherTarget : CFGraph}

/-- **The valency-free replacement for
`Count.DiscreteContraction.map_merge_of_four_valent`.**  An arbitrary geometric
limit isomorphism carries the merged vertex to any vertex of the target datum
carrying nonzero dimension correction.  The only hypothesis on the member is
change-minimality of its own source; nothing is assumed about the valency of
either vertex, so this runs at a divalent or trivalent wall exactly as it does at
a four-valent one. -/
theorem map_merge_of_excess (data : GluingDatum target degree)
    (hMinimal : data.ChangeMinimal)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (other : GluingDatum otherTarget degree)
    (iso : GeometricDatumIso (contractDatum data hc hab hOne) other)
    (vertex : otherTarget.V) (hExcess : other.targetExcess vertex ≠ 0) :
    iso.targetVertex ⟨a, hab⟩ = vertex := by
  have hE := targetExcess_map iso (iso.targetVertex.symm vertex)
  rw [Equiv.apply_symm_apply] at hE
  have hMerge := eq_merge_of_targetExcess_ne_zero data hMinimal hc hab hOne
    (iso.targetVertex.symm vertex) (by rw [← hE]; exact hExcess)
  exact (congrArg iso.targetVertex hMerge).symm.trans
    (iso.targetVertex.apply_symm_apply vertex)

/-- **Four-valency is one way to produce the excess hypothesis**, once validity
is known: Riemann--Hurwitz makes the change nonnegative, so the excess at a
four-valent vertex is at least one. -/
theorem targetExcess_ne_zero_of_four_valent (other : GluingDatum otherTarget degree)
    (hValid : other.Valid) (vertex : otherTarget.V)
    (hFour : (GluingDatum.incidentEdges vertex).card = 4) :
    other.targetExcess vertex ≠ 0 := by
  have hChange := other.targetChange_nonneg hValid vertex
  show other.targetChange vertex + ((GluingDatum.incidentEdges vertex).card : ℤ) - 3 ≠ 0
  rw [hFour]
  push_cast
  omega

/-- **`map_merge_of_four_valent`'s conclusion, through the excess route.**  The
only input beyond the four-valent lemma's own is validity of the target datum,
which for a limit is `ContractionRamification.valid_contractDatum`. -/
theorem map_merge_of_four_valent (data : GluingDatum target degree)
    (hMinimal : data.ChangeMinimal)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (other : GluingDatum otherTarget degree)
    (hValid : other.Valid)
    (iso : GeometricDatumIso (contractDatum data hc hab hOne) other)
    (vertex : otherTarget.V)
    (hFour : (GluingDatum.incidentEdges vertex).card = 4) :
    iso.targetVertex ⟨a, hab⟩ = vertex :=
  map_merge_of_excess data hMinimal hc hab hOne other iso vertex
    (targetExcess_ne_zero_of_four_valent other hValid vertex hFour)

end Away

/-! ## 5.  The wall-level form: a drop-in for `W4WallExhaustion.map_merge` -/

section Wall

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {hy : Nondegenerate y}

open W4WallExhaustion (mergeVertex)

/-- **What a wall is, in the only form merge-pinning needs**: the limit carries
nonvanishing dimension correction at the merged vertex.  This is Equation (C)
with the value forgotten, and it is strictly weaker than four-valency (given
validity) and available at every valency. -/
def IsWall (wall : Regrowth core y degree) : Prop :=
  wall.limit.targetExcess (mergeVertex wall) ≠ 0

/-- **Merge-pinning at an arbitrary wall.**  Statement-compatible with
`Count.W4WallExhaustion.map_merge`, with the valency hypothesis `hFour` replaced
by `IsWall wall`.  Generic in core, request, degree, coordinate **and
valency**. -/
theorem map_merge (other wall : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (hWall : IsWall wall) :
    iso.datum.targetVertex (mergeVertex other) = mergeVertex wall :=
  map_merge_of_excess other.frame.data other.frame.fullDim.changeMinimal rfl
    (fst_ne_snd (other.frame.edgeOf other.column))
    (other.frame.numEdges_edgeOf other.column) wall.limit iso.datum
    (mergeVertex wall) hWall

/-- **Equation (C) in the form the local-case interfaces already state it.**
`LocalCases.W4StableSource.AuxR0SourceInput`, `LocalCases.SecondEquation.…` and
`LocalCases.ThirdEquation.…` each carry a field
`equation_c : data.targetExcess wall = 1` for their wall datum; read at a
regrowth's own limit and merged vertex that field is exactly what `map_merge`
needs, with nothing else to prove. -/
theorem isWall_of_targetExcess_eq_one (wall : Regrowth core y degree)
    (hExcess : wall.limit.targetExcess (mergeVertex wall) = 1) : IsWall wall := by
  rw [IsWall, hExcess]
  exact one_ne_zero

/-- **Equation (C) at the wall, from the source-topology hypothesis.**  Under the
source-topology hypothesis `ContractionForestAt` the excess at the merged vertex
is exactly one, because the full-dimensional frame is change-minimal at both
endpoints and contraction creates exactly one unit of correction. -/
theorem targetExcess_mergeVertex_eq_one (wall : Regrowth core y degree)
    (hForest : ContractionForestAt wall.frame.data (wall.frame.edgeOf wall.column)) :
    wall.limit.targetExcess (mergeVertex wall) = 1 :=
  W4Bridge.targetExcess_contractDatum_merge_eq_one wall.frame.data rfl
    (fst_ne_snd (wall.frame.edgeOf wall.column))
    (wall.frame.numEdges_edgeOf wall.column) hForest wall.frame.fullDim.changeMinimal

/-- **The route available at valency two and three.** -/
theorem isWall_of_forest (wall : Regrowth core y degree)
    (hForest : ContractionForestAt wall.frame.data (wall.frame.edgeOf wall.column)) :
    IsWall wall :=
  isWall_of_targetExcess_eq_one wall (targetExcess_mergeVertex_eq_one wall hForest)

/-- **The `w4` file's own two standing hypotheses suffice.**  A discrete merged
partition is unramified (`W4WallExhaustion.targetChange_eq_zero_of_discrete`), so
at valency four the excess is `0 + 4 - 3 = 1`. -/
theorem isWall_of_discrete_four_valent (wall : Regrowth core y degree)
    (hFour : (GluingDatum.incidentEdges (mergeVertex wall)).card = 4)
    (hDiscrete : wall.limit.vertexPartition (mergeVertex wall)
      = SheetPartition.discrete degree) :
    IsWall wall := by
  show wall.limit.targetChange (mergeVertex wall)
      + ((GluingDatum.incidentEdges (mergeVertex wall)).card : ℤ) - 3 ≠ 0
  rw [W4WallExhaustion.targetChange_eq_zero_of_discrete wall.limit (mergeVertex wall) hDiscrete,
    hFour]
  decide

/-- **Validity plus four-valency also suffices**, with no discreteness. -/
theorem isWall_of_valid_four_valent (wall : Regrowth core y degree)
    (hValid : wall.limit.Valid)
    (hFour : (GluingDatum.incidentEdges (mergeVertex wall)).card = 4) :
    IsWall wall :=
  targetExcess_ne_zero_of_four_valent wall.limit hValid (mergeVertex wall) hFour

/-- **`Count.W4WallExhaustion.map_merge` is recovered**, under exactly the two
hypotheses that file already carries everywhere, and with no appeal to
`DiscreteContraction.map_merge_of_four_valent`. -/
theorem map_merge_of_four_valent_discrete (other wall : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall)
    (hFour : (GluingDatum.incidentEdges (mergeVertex wall)).card = 4)
    (hDiscrete : wall.limit.vertexPartition (mergeVertex wall)
      = SheetPartition.discrete degree) :
    iso.datum.targetVertex (mergeVertex other) = mergeVertex wall :=
  map_merge other wall iso (isWall_of_discrete_four_valent wall hFour hDiscrete)

/-- **Every member of a wall's star is itself a wall.**  The excess at the
member's merged vertex is the wall's, transported. -/
theorem isWall_of_limitIso (other wall : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (hWall : IsWall wall) : IsWall other := by
  have h := targetExcess_map iso.datum (mergeVertex other)
  rw [map_merge other wall iso hWall] at h
  rw [IsWall, ← h]
  exact hWall

/-- The inverse form of `map_merge`, for the direction an argument that starts at
the wall needs. -/
theorem map_merge_symm (other wall : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (hWall : IsWall wall) :
    iso.datum.targetVertex.symm (mergeVertex wall) = mergeVertex other :=
  (Equiv.symm_apply_eq _).mpr (map_merge other wall iso hWall).symm

/-! ### The two steps every exhaustion argument takes next

These are `W4WallExhaustion.limit_discrete` and
`DiscreteContraction.pullbackFourStar` with their valency hypothesis removed:
whatever local datum the wall carries at its merged vertex, an arbitrary member
carries it up to a sheet relabelling, and the wall's star of occurrences pulls
back to the member's. -/

/-- The merged vertex partition of an arbitrary member is the wall's, up to the
sheet relabelling the isomorphism carries. -/
theorem vertexPartition_mergeVertex (other wall : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (hWall : IsWall wall) :
    wall.limit.vertexPartition (mergeVertex wall)
      = (other.limit.vertexPartition (mergeVertex other)).relabel
        (iso.datum.vertexPerm (mergeVertex other)) := by
  have h := iso.datum.vertexPartition (mergeVertex other)
  rwa [map_merge other wall iso hWall] at h

/-- Discreteness of the wall's merged partition is inherited by every member --
`W4WallExhaustion.limit_discrete` without the valency hypothesis. -/
theorem limit_discrete (other wall : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (hWall : IsWall wall)
    (hDiscrete : wall.limit.vertexPartition (mergeVertex wall)
      = SheetPartition.discrete degree) :
    other.limit.vertexPartition (mergeVertex other) = SheetPartition.discrete degree := by
  apply DiscreteContraction.eq_discrete_of_relabel _ (iso.datum.vertexPerm (mergeVertex other))
  exact ((vertexPartition_mergeVertex other wall iso hWall).symm.trans hDiscrete)

/-- The valency of the merged vertex is a wall invariant, so the member's merged
vertex has the wall's valency whatever that valency is. -/
theorem card_incidentEdges_mergeVertex (other wall : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (hWall : IsWall wall) :
    (GluingDatum.incidentEdges (mergeVertex other)).card
      = (GluingDatum.incidentEdges (mergeVertex wall)).card := by
  have h := iso.datum.incidentEdges_card_map (mergeVertex other)
  rw [map_merge other wall iso hWall] at h
  exact h.symm

end Wall

/-! ## 6.  The column route: what it does give, and where it stops

Everything in this section is true.  What it is not is a source of `map_merge`:
its hypothesis is a `GeometricSegmentWalls.FrameIso`, i.e. an isomorphism of the
two **uncontracted** frames, and the exhaustion argument only ever has a
`GeometricStar.LimitIso`, i.e. an isomorphism of the two **contracted** data, and
two star members of one wall can admit a `LimitIso` and no `FrameIso` (an explicit
example is not part of this library). -/

section Column

variable {n p degree : ℕ} {core : Core n p} {k l : Frame core degree}

/-- A frame isomorphism carries the occurrence a column names to the occurrence
its column image names. -/
theorem frameIso_targetEdge_edgeOf (fi : GeometricSegmentWalls.FrameIso k l) (col : Fin p) :
    fi.datum.targetEdge (k.edgeOf col) = l.edgeOf (fi.column col) := by
  show fi.datum.targetEdge (k.fullDim.labelling.targetEdge col)
    = l.fullDim.labelling.targetEdge (fi.column col)
  rw [GeometricSegmentWalls.FrameIso.column, Equiv.trans_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply]

/-- Hence it carries the two endpoints of the wall occurrence to the two
endpoints of the image wall occurrence, as an unordered pair.  **This is the
merge-pinning the column route offers**, and it is available at every valency --
for a frame isomorphism. -/
theorem frameIso_unorderedEnds (fi : GeometricSegmentWalls.FrameIso k l) (col : Fin p) :
    UnorderedEnds fi.datum.targetVertex
      ((k.edgeOf col : k.target.V × k.target.V))
      ((l.edgeOf (fi.column col) : l.target.V × l.target.V)) := by
  have h := fi.datum.ends (k.edgeOf col)
  rwa [frameIso_targetEdge_edgeOf fi col] at h

/-- The explicit two cases of the previous statement: the endpoints correspond,
possibly after a swap. -/
theorem frameIso_maps_wall_ends (fi : GeometricSegmentWalls.FrameIso k l) (col : Fin p) :
    ((l.edgeOf (fi.column col) : l.target.V × l.target.V).1
        = fi.datum.targetVertex (k.edgeOf col : k.target.V × k.target.V).1 ∧
      (l.edgeOf (fi.column col) : l.target.V × l.target.V).2
        = fi.datum.targetVertex (k.edgeOf col : k.target.V × k.target.V).2) ∨
    ((l.edgeOf (fi.column col) : l.target.V × l.target.V).1
        = fi.datum.targetVertex (k.edgeOf col : k.target.V × k.target.V).2 ∧
      (l.edgeOf (fi.column col) : l.target.V × l.target.V).2
        = fi.datum.targetVertex (k.edgeOf col : k.target.V × k.target.V).1) := by
  rcases frameIso_unorderedEnds fi col with h | h
  · exact Or.inl ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · exact Or.inr ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- At a wall crossing the column component is the identity
(`ConeSide.WallCrossing.frameIso_column_eq_id`), so the wall occurrence is
carried to the wall occurrence on the nose. -/
theorem wallCrossing_targetEdge_edgeOf (w : ConeSide.WallCrossing core degree)
    (fi : GeometricSegmentWalls.FrameIso w.first w.second) :
    fi.datum.targetEdge (w.first.edgeOf w.column) = w.second.edgeOf w.column := by
  rw [frameIso_targetEdge_edgeOf fi w.column,
    ConeSide.WallCrossing.frameIso_column_eq_id w fi]
  rfl

end Column

end DraismaVargas.Count.MergePinning
