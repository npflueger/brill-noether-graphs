import DraismaVargas.Infrastructure.GluingRealization
import Utilities.Subdivision.SubdivisionSeparator

/-!
# Target-tree potentials for integral Draisma--Vargas realizations

The semantic lowering in `GluingRealization` accepts exact target potentials.
This module constructs them uniformly from the ordinary chip-firing theorem on
the positive integral subdivision of a connected genus-zero target.

The key local fact is elementary but worth isolating: if the principal divisor
of a firing script vanishes at every interior vertex of a subdivided edge, its
unit-step differences are constant on that edge.  Hence the restriction of
the script to core vertices has an exact integral slope.
-/

namespace DraismaVargas.Infrastructure

open Finset
open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph

namespace SubdivisionGraph.Spec

variable {n p : ℕ} (spec : Spec n p)

/-- Difference of an arbitrary firing script across one oriented unit step. -/
def scriptStep (script : firing_script spec.graph) (edge : Fin p)
    (offset : Fin (spec.length edge)) : ℤ :=
  script (spec.stepRight edge offset) - script (spec.stepLeft edge offset)

/-- At an interior subdivision vertex, the principal coefficient of an
arbitrary script is its next unit-step difference minus its previous one. -/
theorem prin_script_interior_eq_stepDifference
    (script : firing_script spec.graph) (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) :
    prin spec.graph script (spec.interiorVertex edge offset) =
      scriptStep spec script edge (spec.nextStep edge offset) -
        scriptStep spec script edge (spec.previousStep edge offset) := by
  rw [spec.prin_eq_sum_step_differences]
  let next : spec.Step := ⟨edge, spec.nextStep edge offset⟩
  let previous : spec.Step := ⟨edge, spec.previousStep edge offset⟩
  let leftValue : spec.Step → ℤ := fun step ↦
    if spec.stepLeft step.1 step.2 = spec.interiorVertex edge offset then
      script (spec.stepRight step.1 step.2) -
        script (spec.stepLeft step.1 step.2)
    else 0
  let rightValue : spec.Step → ℤ := fun step ↦
    if spec.stepRight step.1 step.2 = spec.interiorVertex edge offset then
      -(script (spec.stepRight step.1 step.2) -
        script (spec.stepLeft step.1 step.2))
    else 0
  rw [Finset.sum_add_distrib]
  have hLeft : (∑ step : spec.Step, leftValue step) = leftValue next := by
    apply Fintype.sum_eq_single next
    intro step hne
    by_cases hEqual : spec.stepLeft step.1 step.2 =
        spec.interiorVertex edge offset
    · exact (hne ((spec.stepLeft_eq_interiorVertex_iff step edge offset).mp
        hEqual)).elim
    · simp [leftValue, hEqual]
  have hRight : (∑ step : spec.Step, rightValue step) = rightValue previous := by
    apply Fintype.sum_eq_single previous
    intro step hne
    by_cases hEqual : spec.stepRight step.1 step.2 =
        spec.interiorVertex edge offset
    · exact (hne ((spec.stepRight_eq_interiorVertex_iff step edge offset).mp
        hEqual)).elim
    · simp [rightValue, hEqual]
  change (∑ step : spec.Step, leftValue step) +
      (∑ step : spec.Step, rightValue step) = _
  rw [hLeft, hRight]
  simp [leftValue, rightValue, next, previous, scriptStep]
  ring

/-- If a script has zero principal coefficient at every subdivision-interior
vertex, its difference is constant across all unit steps of each core edge. -/
theorem scriptStep_eq_first_of_prin_interior_zero
    (script : firing_script spec.graph)
    (hInterior : ∀ edge offset,
      prin spec.graph script (spec.interiorVertex edge offset) = 0)
    (edge : Fin p) (offset : Fin (spec.length edge)) :
    scriptStep spec script edge offset =
      scriptStep spec script edge ⟨0, spec.length_pos edge⟩ := by
  have hAux : ∀ (i : ℕ) (hi : i < spec.length edge),
      scriptStep spec script edge ⟨i, hi⟩ =
        scriptStep spec script edge ⟨0, spec.length_pos edge⟩ := by
    intro i
    induction i with
    | zero =>
        intro hi
        apply congrArg (scriptStep spec script edge)
        apply Fin.ext
        rfl
    | succ i ih =>
        intro hi
        have hiInterior : i < spec.length edge - 1 := by omega
        let interior : Fin (spec.length edge - 1) := ⟨i, hiInterior⟩
        have hDifference :=
          prin_script_interior_eq_stepDifference spec script edge interior
        rw [hInterior edge interior] at hDifference
        have hAdjacent :
            scriptStep spec script edge (spec.nextStep edge interior) =
              scriptStep spec script edge (spec.previousStep edge interior) := by
          omega
        calc
          scriptStep spec script edge ⟨i + 1, hi⟩ =
              scriptStep spec script edge (spec.nextStep edge interior) := by
            apply congrArg (scriptStep spec script edge)
            apply Fin.ext
            rfl
          _ = scriptStep spec script edge (spec.previousStep edge interior) :=
            hAdjacent
          _ = scriptStep spec script edge ⟨i, by omega⟩ := by
            apply congrArg (scriptStep spec script edge)
            apply Fin.ext
            rfl
          _ = scriptStep spec script edge ⟨0, spec.length_pos edge⟩ :=
            ih (by omega)
  exact hAux offset.val offset.isLt

/-- A script harmonic at all edge-interior vertices is affine along every
subdivided core edge. -/
theorem script_pathVertex_eq_tail_add_mul_firstStep
    (script : firing_script spec.graph)
    (hInterior : ∀ edge offset,
      prin spec.graph script (spec.interiorVertex edge offset) = 0)
    (edge : Fin p) (position : spec.PathPosition edge) :
    script (spec.pathVertex edge position) =
      script (spec.coreVertex (spec.core.tail edge)) +
        (position.val : ℤ) *
          scriptStep spec script edge ⟨0, spec.length_pos edge⟩ := by
  have hAux : ∀ (i : ℕ) (hi : i < spec.length edge + 1),
      script (spec.pathVertex edge ⟨i, hi⟩) =
        script (spec.coreVertex (spec.core.tail edge)) +
          (i : ℤ) *
            scriptStep spec script edge ⟨0, spec.length_pos edge⟩ := by
    intro i
    induction i with
    | zero =>
        intro hi
        rw [spec.pathVertex_zero]
        ring
    | succ i ih =>
        intro hi
        let offset : Fin (spec.length edge) := ⟨i, by omega⟩
        have hStep :=
          scriptStep_eq_first_of_prin_interior_zero spec script hInterior edge offset
        have hDifference :
            script (spec.pathVertex edge ⟨i + 1, hi⟩) -
                script (spec.pathVertex edge ⟨i, by omega⟩) =
              scriptStep spec script edge offset := by
          rw [show spec.pathVertex edge ⟨i + 1, hi⟩ =
              spec.pathVertex edge (spec.stepRightPosition edge offset) by
            apply congrArg (spec.pathVertex edge)
            apply Fin.ext
            rfl]
          rw [show spec.pathVertex edge ⟨i, by omega⟩ =
              spec.pathVertex edge (spec.stepLeftPosition edge offset) by
            apply congrArg (spec.pathVertex edge)
            apply Fin.ext
            rfl]
          rw [spec.pathVertex_stepRightPosition,
            spec.pathVertex_stepLeftPosition]
          rfl
        have hPrevious := ih (by omega)
        calc
          script (spec.pathVertex edge ⟨i + 1, hi⟩) =
              script (spec.pathVertex edge ⟨i, by omega⟩) +
                scriptStep spec script edge offset := by omega
          _ = (script (spec.coreVertex (spec.core.tail edge)) +
                (i : ℤ) *
                  scriptStep spec script edge ⟨0, spec.length_pos edge⟩) +
                scriptStep spec script edge ⟨0, spec.length_pos edge⟩ := by
              rw [hPrevious, hStep]
          _ = script (spec.coreVertex (spec.core.tail edge)) +
                (↑(i + 1) : ℤ) *
                  scriptStep spec script edge ⟨0, spec.length_pos edge⟩ := by
              push_cast
              ring
  exact hAux position.val position.isLt

/-- Restricting such a script to core vertices gives an exact integral slope
times the full subdivided edge length. -/
theorem coreRise_restrict_eq_firstStep_mul_length
    (script : firing_script spec.graph)
    (hInterior : ∀ edge offset,
      prin spec.graph script (spec.interiorVertex edge offset) = 0)
    (edge : Fin p) :
    spec.coreRise (fun vertex ↦ script (spec.coreVertex vertex)) edge =
      scriptStep spec script edge ⟨0, spec.length_pos edge⟩ *
        (spec.length edge : ℤ) := by
  have hPath := script_pathVertex_eq_tail_add_mul_firstStep spec script hInterior
    edge ⟨spec.length edge, by omega⟩
  rw [spec.pathVertex_length] at hPath
  unfold Spec.coreRise
  change script (spec.coreVertex (spec.core.head edge)) -
      script (spec.coreVertex (spec.core.tail edge)) = _
  rw [hPath]
  ring

/-- At a core vertex, a script harmonic on every edge interior has signed
incidence equal to the first (hence constant) step on each core edge. -/
theorem prin_script_core_eq_firstStep_incidence
    (script : firing_script spec.graph)
    (hInterior : ∀ edge offset,
      prin spec.graph script (spec.interiorVertex edge offset) = 0)
    (vertex : Fin n) :
    prin spec.graph script (spec.coreVertex vertex) =
      ∑ edge : Fin p,
        ((if spec.core.tail edge = vertex then
            scriptStep spec script edge ⟨0, spec.length_pos edge⟩
          else 0) +
          (if spec.core.head edge = vertex then
            -scriptStep spec script edge ⟨0, spec.length_pos edge⟩
          else 0)) := by
  rw [spec.prin_eq_sum_step_differences, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro edge _
  rw [Finset.sum_add_distrib]
  have hLeft :
      (∑ offset : Fin (spec.length edge),
        if spec.stepLeft edge offset = spec.coreVertex vertex then
          scriptStep spec script edge offset else 0) =
        if spec.core.tail edge = vertex then
          scriptStep spec script edge ⟨0, spec.length_pos edge⟩ else 0 := by
    by_cases hTail : spec.core.tail edge = vertex
    · rw [if_pos hTail]
      let first : Fin (spec.length edge) := ⟨0, spec.length_pos edge⟩
      refine (Fintype.sum_eq_single first ?_).trans ?_
      · intro offset hne
        rw [if_neg]
        intro hLeft
        have hZero := (spec.stepLeft_eq_coreVertex_iff edge offset vertex).mp hLeft
        apply hne
        apply Fin.ext
        exact hZero.1
      · rw [if_pos]
        rw [spec.stepLeft_zero, hTail]
    · rw [if_neg hTail]
      apply Finset.sum_eq_zero
      intro offset _
      rw [if_neg]
      intro hLeft
      exact hTail ((spec.stepLeft_eq_coreVertex_iff edge offset vertex).mp hLeft).2
  have hRight :
      (∑ offset : Fin (spec.length edge),
        if spec.stepRight edge offset = spec.coreVertex vertex then
          -scriptStep spec script edge offset else 0) =
        if spec.core.head edge = vertex then
          -scriptStep spec script edge ⟨0, spec.length_pos edge⟩ else 0 := by
    by_cases hHead : spec.core.head edge = vertex
    · rw [if_pos hHead]
      let last : Fin (spec.length edge) :=
        ⟨spec.length edge - 1, by have := spec.length_pos edge; omega⟩
      refine (Fintype.sum_eq_single last ?_).trans ?_
      · intro offset hne
        rw [if_neg]
        intro hRight
        have hLast :=
          (spec.stepRight_eq_coreVertex_iff edge offset vertex).mp hRight
        apply hne
        apply Fin.ext
        dsimp [last]
        omega
      · rw [if_pos]
        · rw [scriptStep_eq_first_of_prin_interior_zero spec script hInterior]
        · simp [last, hHead]
    · rw [if_neg hHead]
      apply Finset.sum_eq_zero
      intro offset _
      rw [if_neg]
      intro hRight
      exact hHead ((spec.stepRight_eq_coreVertex_iff edge offset vertex).mp hRight).2
  change
    (∑ offset : Fin (spec.length edge),
        if spec.stepLeft edge offset = spec.coreVertex vertex then
          scriptStep spec script edge offset else 0) +
      (∑ offset : Fin (spec.length edge),
        if spec.stepRight edge offset = spec.coreVertex vertex then
          -scriptStep spec script edge offset else 0) = _
  rw [hLeft, hRight]

end SubdivisionGraph.Spec

namespace GluingDatum.IntegralRealization

variable {target : CFGraph} {degree : ℕ}
variable {data : GluingDatum target degree}

/-- The realized target subdivision is connected whenever its underlying
target graph is connected. -/
theorem targetSpec_connected (realization : data.IntegralRealization)
    (hConnected : graph_connected target) :
    graph_connected realization.targetSpec.graph := by
  apply realization.targetSpec.graph_connected_of_coreConnected
  exact unitPresentationCore_connected_of_graph_connected target hConnected

/-- Subdivision by the realized positive lengths preserves the target's
cyclomatic genus. -/
@[simp] theorem targetSpec_genus (realization : data.IntegralRealization) :
    genus realization.targetSpec.graph = genus target := by
  rw [realization.targetSpec.genus_graph]
  simp [genus]

/-- The core vertex of the realized target subdivision corresponding to an
original target vertex. -/
noncomputable def targetCoreVertex (realization : data.IntegralRealization)
    (vertex : target.V) : realization.targetSpec.graph.V :=
  realization.targetSpec.coreVertex
    (Utilities.Certificate.UnitSubdivisionPresentation.vertexEquiv target vertex)

/-- Connected genus zero supplies a firing script whose principal divisor
moves one chip from `root` to `anchor` on the realized target subdivision. -/
theorem exists_targetTreeScript (realization : data.IntegralRealization)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (root anchor : target.V) :
    ∃ script : firing_script realization.targetSpec.graph,
      one_chip (realization.targetCoreVertex anchor) -
          one_chip (realization.targetCoreVertex root) =
        prin realization.targetSpec.graph script := by
  apply (principal_iff_eq_prin realization.targetSpec.graph _).mp
  exact MarkedGraphs.IndexedHarmonicData.targetOneChipEquivalent_of_connected_genus_zero
    realization.targetSpec.graph
    (realization.targetSpec_connected hConnected)
    (by rw [targetSpec_genus realization]; exact hGenus)
    (realization.targetCoreVertex root)
    (realization.targetCoreVertex anchor)

/-- A chosen chip-moving firing script on the realized target tree.  Its
properties, rather than this noncomputable choice, form the downstream API. -/
noncomputable def targetTreeScript (realization : data.IntegralRealization)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (root anchor : target.V) : firing_script realization.targetSpec.graph :=
  Classical.choose
    (realization.exists_targetTreeScript hConnected hGenus root anchor)

/-- The chosen target-tree script has the advertised principal divisor. -/
theorem targetTreeScript_prin (realization : data.IntegralRealization)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (root anchor : target.V) :
    one_chip (realization.targetCoreVertex anchor) -
        one_chip (realization.targetCoreVertex root) =
      prin realization.targetSpec.graph
        (realization.targetTreeScript hConnected hGenus root anchor) :=
  Classical.choose_spec
    (realization.exists_targetTreeScript hConnected hGenus root anchor)

/-- The chip-moving script is harmonic at every non-core vertex because its
principal divisor is supported at the two chosen core vertices. -/
theorem targetTreeScript_prin_interior
    (realization : data.IntegralRealization)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (root anchor : target.V)
    (edge : Fin target.edges.card)
    (offset : Fin (realization.targetSpec.length edge - 1)) :
    prin realization.targetSpec.graph
        (realization.targetTreeScript hConnected hGenus root anchor)
        (realization.targetSpec.interiorVertex edge offset) = 0 := by
  have hAtInterior := congrFun
    (realization.targetTreeScript_prin hConnected hGenus root anchor)
    (realization.targetSpec.interiorVertex edge offset)
  simpa [one_chip, targetCoreVertex,
    Utilities.Certificate.SubdivisionGraph.Spec.coreVertex,
    Utilities.Certificate.SubdivisionGraph.Spec.interiorVertex] using
      hAtInterior.symm

/-- Restriction of the chosen chip-moving script to the original target
vertices. -/
noncomputable def targetTreePotential
    (realization : data.IntegralRealization)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (root anchor vertex : target.V) : ℤ :=
  realization.targetTreeScript hConnected hGenus root anchor
    (realization.targetCoreVertex vertex)

/-- The constant unit-step difference of the chosen script along one exact
target-edge occurrence. -/
noncomputable def targetTreeSlope
    (realization : data.IntegralRealization)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (root anchor : target.V) (edge : target.edges) : ℤ :=
  SubdivisionGraph.Spec.scriptStep realization.targetSpec
    (realization.targetTreeScript hConnected hGenus root anchor)
    (Utilities.Certificate.UnitSubdivisionPresentation.edgeEquiv target edge)
    ⟨0, realization.targetSpec.length_pos _⟩

/-- The target-tree potential has an exact integral slope across every
realized target-edge occurrence. -/
theorem targetTreePotential_rise
    (realization : data.IntegralRealization)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (root anchor : target.V) (edge : target.edges) :
    realization.targetTreePotential hConnected hGenus root anchor edge.1.2 -
        realization.targetTreePotential hConnected hGenus root anchor edge.1.1 =
      realization.targetTreeSlope hConnected hGenus root anchor edge *
        (realization.targetLength edge : ℤ) := by
  let slot :=
    Utilities.Certificate.UnitSubdivisionPresentation.edgeEquiv target edge
  have hRise := SubdivisionGraph.Spec.coreRise_restrict_eq_firstStep_mul_length
    realization.targetSpec
    (realization.targetTreeScript hConnected hGenus root anchor)
    (realization.targetTreeScript_prin_interior hConnected hGenus root anchor)
    slot
  unfold Utilities.Certificate.SubdivisionGraph.Spec.coreRise at hRise
  have hTail : realization.targetSpec.core.tail slot =
      Utilities.Certificate.UnitSubdivisionPresentation.vertexEquiv target edge.1.1 := by
    simp [slot, GluingDatum.IntegralRealization.targetSpec]
  have hHead : realization.targetSpec.core.head slot =
      Utilities.Certificate.UnitSubdivisionPresentation.vertexEquiv target edge.1.2 := by
    simp [slot, GluingDatum.IntegralRealization.targetSpec]
  rw [hHead, hTail] at hRise
  change
    realization.targetTreeScript hConnected hGenus root anchor
        (realization.targetCoreVertex edge.1.2) -
      realization.targetTreeScript hConnected hGenus root anchor
        (realization.targetCoreVertex edge.1.1) = _
  simpa [slot, targetCoreVertex, targetTreeSlope,
    GluingDatum.IntegralRealization.targetSpec] using hRise

/-- Signed incidence of the extracted occurrence slopes is exactly the
one-chip difference between `anchor` and `root`. -/
theorem targetTreeSlope_incidence
    (realization : data.IntegralRealization)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (root anchor vertex : target.V) :
    targetEdgeIncidence
        (realization.targetTreeSlope hConnected hGenus root anchor) vertex =
      (if vertex = anchor then 1 else 0) -
        (if vertex = root then 1 else 0) := by
  have hCore :=
    SubdivisionGraph.Spec.prin_script_core_eq_firstStep_incidence
      realization.targetSpec
      (realization.targetTreeScript hConnected hGenus root anchor)
      (realization.targetTreeScript_prin_interior
        hConnected hGenus root anchor)
      (Utilities.Certificate.UnitSubdivisionPresentation.vertexEquiv target vertex)
  have hReindex :
      targetEdgeIncidence
          (realization.targetTreeSlope hConnected hGenus root anchor) vertex =
        ∑ slot : Fin target.edges.card,
          ((if realization.targetSpec.core.tail slot =
                Utilities.Certificate.UnitSubdivisionPresentation.vertexEquiv
                  target vertex then
              SubdivisionGraph.Spec.scriptStep realization.targetSpec
                (realization.targetTreeScript hConnected hGenus root anchor)
                slot ⟨0, realization.targetSpec.length_pos slot⟩
            else 0) +
            (if realization.targetSpec.core.head slot =
                Utilities.Certificate.UnitSubdivisionPresentation.vertexEquiv
                  target vertex then
              -SubdivisionGraph.Spec.scriptStep realization.targetSpec
                (realization.targetTreeScript hConnected hGenus root anchor)
                slot ⟨0, realization.targetSpec.length_pos slot⟩
            else 0)) := by
    unfold targetEdgeIncidence
    apply Fintype.sum_equiv
      (Utilities.Certificate.UnitSubdivisionPresentation.edgeEquiv target)
    intro edge
    have hTail : realization.targetSpec.core.tail
          (Utilities.Certificate.UnitSubdivisionPresentation.edgeEquiv target edge) =
        Utilities.Certificate.UnitSubdivisionPresentation.vertexEquiv
          target edge.1.1 := by
      simp [GluingDatum.IntegralRealization.targetSpec]
    have hHead : realization.targetSpec.core.head
          (Utilities.Certificate.UnitSubdivisionPresentation.edgeEquiv target edge) =
        Utilities.Certificate.UnitSubdivisionPresentation.vertexEquiv
          target edge.1.2 := by
      simp [GluingDatum.IntegralRealization.targetSpec]
    by_cases hAtTail : edge.1.1 = vertex <;>
      by_cases hAtHead : edge.1.2 = vertex <;>
      simp [targetTreeSlope, hTail, hHead, hAtTail, hAtHead]
  calc
    targetEdgeIncidence
        (realization.targetTreeSlope hConnected hGenus root anchor) vertex =
        _ := hReindex
    _ = prin realization.targetSpec.graph
          (realization.targetTreeScript hConnected hGenus root anchor)
          (realization.targetCoreVertex vertex) := by
      exact hCore.symm
    _ = (if vertex = anchor then 1 else 0) -
          (if vertex = root then 1 else 0) := by
      have hAtVertex := congrFun
        (realization.targetTreeScript_prin hConnected hGenus root anchor)
        (realization.targetCoreVertex vertex)
      simpa [one_chip, targetCoreVertex,
        Utilities.Certificate.SubdivisionGraph.Spec.coreVertex] using
          hAtVertex.symm

/-- End-to-end semantic lowering for any integral Draisma--Vargas realization
over a connected genus-zero target.  No explicit target potentials remain in the
interface: they are extracted uniformly from ordinary chip firing on the
realized target subdivision. -/
theorem rank_fibre_ge_one_of_connected_genus_zero_target
    (realization : data.IntegralRealization) (hSourceConnected : data.Connected)
    (hTargetConnected : graph_connected target) (hTargetGenus : genus target = 0)
    (root : target.V) :
    rank realization.sourceSpec.graph
      (Utilities.Subdivision.SubdivisionCoreSupport.coreDivisor
        realization.sourceSpec (realization.fibreWeight root)) ≥ 1 := by
  exact realization.rank_fibre_ge_one_of_targetPotentials hSourceConnected root
    (realization.targetTreePotential hTargetConnected hTargetGenus root)
    (realization.targetTreeSlope hTargetConnected hTargetGenus root)
    (realization.targetTreePotential_rise hTargetConnected hTargetGenus root)
    (realization.targetTreeSlope_incidence hTargetConnected hTargetGenus root)

/-- The same lowering in existential form: the realized source graph carries a
rank-one divisor of degree `degree` (`BNExists`), and the fibre divisor over
`root` is effective. -/
theorem bnExists_and_effective_of_connected_genus_zero_target
    (realization : data.IntegralRealization) (hSourceConnected : data.Connected)
    (hTargetConnected : graph_connected target) (hTargetGenus : genus target = 0)
    (root : target.V) :
    BNExists realization.sourceSpec.graph 1 degree ∧
      _root_.effective
        (Utilities.Subdivision.SubdivisionCoreSupport.coreDivisor
          realization.sourceSpec (realization.fibreWeight root)) := by
  exact realization.bnExists_and_effective_of_targetPotentials
    hSourceConnected root degree (realization.sum_fibreWeight_eq_degree root)
    (realization.targetTreePotential hTargetConnected hTargetGenus root)
    (realization.targetTreeSlope hTargetConnected hTargetGenus root)
    (realization.targetTreePotential_rise hTargetConnected hTargetGenus root)
    (realization.targetTreeSlope_incidence hTargetConnected hTargetGenus root)

end GluingDatum.IntegralRealization

end DraismaVargas.Infrastructure
