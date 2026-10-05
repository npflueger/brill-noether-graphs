module

public import DraismaVargas.LocalCases.InteriorBridgesTrivalent
public import DraismaVargas.LocalCases.InteriorBridgesDivalent

@[expose] public section

/-!
# All ten interior tag bridges, composed

`InteriorProgress.wallBridge_of_tagBridges` dispatches the ten-way interior
classification into tracked routed walls from ten per-tag bridges.  Six are
proved in `InteriorProgress` itself, the two trivalent ones in
`InteriorBridgesTrivalent` and the two divalent ones in
`InteriorBridgesDivalent`.  This module only composes them:

* `wallBridge` -- the tracked routed wall at one chart,
  `InteriorProgress.WallBridge`, with **no** hypothesis at all;
* `interior_of_admissible` -- the `interior` hypothesis of
  `OuterWalk.coneEntry_of_reaches` from the march's three metric facts
  (`0 < baseStart`, `0 ≤ baseFinish`, `0 ≤ restartTime`) and the genericity
  hypothesis alone.  `OuterWalkInterior.interior'_of_bridges` is the same thing
  with the three facts and the genericity read off the restated binder, so it
  needs nothing beyond the bridges; with `wallBridge`,
  `OuterWalkInterior.interior'_unconditional` needs nothing at all.
-/

namespace DraismaVargas.LocalCases.InteriorBridgesAll

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.InteriorProgress
open DraismaVargas.LocalCases.SemanticAtlasMarch
open DraismaVargas.LocalCases.TrackedWallProgress
open DraismaVargas.LocalCases.TrackedWallProgressMore
open DraismaVargas.Infrastructure.RationalAffineWall

variable {degree : ℕ} {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- **Routed walls at one chart, unconditionally.**  Every one of the ten interior tags
has a bridge from the classification to a tracked routed wall. -/
theorem wallBridge {chart : Matrix coordinate coordinate ℚ} {graph : CubicDartGraph D V}
    {label : D → coordinate} : WallBridge degree coordinate chart graph label :=
  InteriorBridgesTrivalent.wallBridge_of_divalent InteriorBridgesDivalent.w2Bridge_m1k
    InteriorBridgesDivalent.w2Bridge_mkk

/-- **The walk's `interior` from the march's metric facts and genericity alone.** -/
noncomputable def interior_of_admissible {label : D → coordinate} {G : CubicDartGraph D V}
    (metric : ∀ (K : CubicDartGraph D V), CubicDartGraph.Reaches G K →
      ∀ (baseStart baseFinish : coordinate → ℚ)
        (current : TrackedState degree K label
          (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
          baseStart baseFinish),
        ¬ current.Terminal →
        (∀ i, 0 < baseStart i) ∧ (∀ i, 0 ≤ baseFinish i) ∧
          0 ≤ current.toMatrixState.restartTime)
    (hA02Generic : ∀ (K : CubicDartGraph D V), CubicDartGraph.Reaches G K →
      ∀ (baseStart baseFinish : coordinate → ℚ)
        (current : TrackedState degree K label
          (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
          baseStart baseFinish),
        SimpleNegativeCrossings current.toMatrixState.currentStart
          current.toMatrixState.currentFinish) :
    ∀ (K : CubicDartGraph D V), CubicDartGraph.Reaches G K →
      ∀ (baseStart baseFinish : coordinate → ℚ)
        (current : TrackedState degree K label
          (MatrixAtlas.atlasMatrix (coordinate := coordinate) (degree := degree))
          baseStart baseFinish),
        ¬ current.Terminal → TrackedProgress current :=
  interior_of_bridges (fun _ _ _ _ _ _ ↦ wallBridge) metric hA02Generic

end DraismaVargas.LocalCases.InteriorBridgesAll
