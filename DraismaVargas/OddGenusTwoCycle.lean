import DraismaVargas.OddGenusRetraction
import Utilities.Pseudocore.PseudocorePresentation
import Utilities.Subdivision.CoreVertexCut
import Utilities.Subdivision.SubdivisionConnectivity

/-!
# A concrete genus-one pendant extension

Attach one new core vertex to a chosen old core vertex by two parallel slots.
The new vertex is bivalent, so these two paths represent the loop attachment
used in the odd-to-even Draisma--Vargas reduction while the subdivision core
itself remains loopless.

This file constructs the extension and proves its topology uniformly: it is
connected whenever the old core is connected, its genus is exactly one
larger, and the old core is one side of a valid articulation cut at every
positive regular scale.  An occurrence-level equivalence identifies that
induced side with the original scaled subdivision, completing the concrete
`RegularPendantExtension` and the odd-to-even reduction.
-/

namespace DraismaVargas.OddGenusTwoCycle

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ExplicitPotential
open Utilities.Certificate.SubdivisionGraph

variable {n p : ℕ}

/-- Embed an old core vertex before the new final vertex. -/
def oldVertex (vertex : Fin n) : Fin (n + 1) :=
  Fin.castSucc vertex

/-- The new bivalent marker vertex. -/
def markerVertex : Fin (n + 1) :=
  Fin.last n

/-- Embed an old edge slot before the two new final slots. -/
def oldEdge (edge : Fin p) : Fin (p + 2) :=
  ⟨edge.val, by omega⟩

/-- The first of the two parallel marker slots. -/
def firstMarkerEdge : Fin (p + 2) :=
  ⟨p, by omega⟩

/-- The second of the two parallel marker slots. -/
def secondMarkerEdge : Fin (p + 2) :=
  ⟨p + 1, by omega⟩

/-- Append two parallel slots from `root` to a new bivalent marker. -/
def core (source : Spec n p) (root : Fin n) : Core (n + 1) (p + 2) where
  tail := fun edge =>
    if hOld : edge.val < p then
      oldVertex (source.core.tail ⟨edge.val, hOld⟩)
    else oldVertex root
  head := fun edge =>
    if hOld : edge.val < p then
      oldVertex (source.core.head ⟨edge.val, hOld⟩)
    else markerVertex

@[simp] theorem core_tail_old (source : Spec n p) (root : Fin n)
    (edge : Fin p) :
    (core source root).tail (oldEdge edge) = oldVertex (source.core.tail edge) := by
  simp [core, oldEdge]

@[simp] theorem core_head_old (source : Spec n p) (root : Fin n)
    (edge : Fin p) :
    (core source root).head (oldEdge edge) = oldVertex (source.core.head edge) := by
  simp [core, oldEdge]

@[simp] theorem core_tail_firstMarkerEdge
    (source : Spec n p) (root : Fin n) :
    (core source root).tail firstMarkerEdge = oldVertex root := by
  simp [core, firstMarkerEdge]

@[simp] theorem core_head_firstMarkerEdge
    (source : Spec n p) (root : Fin n) :
    (core source root).head firstMarkerEdge = markerVertex := by
  simp [core, firstMarkerEdge, markerVertex]

@[simp] theorem core_tail_secondMarkerEdge
    (source : Spec n p) (root : Fin n) :
    (core source root).tail secondMarkerEdge = oldVertex root := by
  simp [core, secondMarkerEdge]

@[simp] theorem core_head_secondMarkerEdge
    (source : Spec n p) (root : Fin n) :
    (core source root).head secondMarkerEdge = markerVertex := by
  simp [core, secondMarkerEdge, markerVertex]

/-- Give both new marker slots unit length while retaining every old metric
length. -/
def extension (source : Spec n p) (root : Fin n) : Spec (n + 1) (p + 2) where
  core := core source root
  length := fun edge =>
    if hOld : edge.val < p then source.length ⟨edge.val, hOld⟩ else 1
  core_nonempty := by omega
  core_loopless := by
    intro edge
    by_cases hOld : edge.val < p
    · simp only [core, hOld, dite_true]
      intro hEqual
      apply source.core_loopless ⟨edge.val, hOld⟩
      exact Fin.castSucc_inj.mp hEqual
    · simp [core, hOld, oldVertex, markerVertex]
  length_pos := by
    intro edge
    by_cases hOld : edge.val < p
    · simpa [hOld] using source.length_pos ⟨edge.val, hOld⟩
    · simp [hOld]

@[simp] theorem extension_length_old (source : Spec n p) (root : Fin n)
    (edge : Fin p) :
    (extension source root).length (oldEdge edge) = source.length edge := by
  simp [extension, oldEdge]

@[simp] theorem extension_length_firstMarkerEdge
    (source : Spec n p) (root : Fin n) :
    (extension source root).length firstMarkerEdge = 1 := by
  simp [extension, firstMarkerEdge]

@[simp] theorem extension_length_secondMarkerEdge
    (source : Spec n p) (root : Fin n) :
    (extension source root).length secondMarkerEdge = 1 := by
  simp [extension, secondMarkerEdge]

/-- The two parallel marker slots raise the cyclomatic genus by exactly one. -/
theorem genus_extension_graph (source : Spec n p) (root : Fin n) :
    genus (extension source root).graph = genus source.graph + 1 := by
  rw [Spec.genus_graph, Spec.genus_graph]
  push_cast
  ring

/-- The same genus increment in the natural subtraction vocabulary of the
headline theorem. -/
theorem genusIndex_extension (_source : Spec n p)
    (hVertices : n ≤ p + 1) :
    (p + 2) + 1 - (n + 1) = (p + 1 - n) + 1 := by
  omega

/-- Core connectedness survives the pendant two-cycle attachment. -/
theorem core_connected (source : Spec n p) (root : Fin n)
    (hConnected : source.core.Connected) :
    (extension source root).core.Connected := by
  intro side hSplit
  by_cases hOldSplit : ∃ v w : Fin n,
      oldVertex v ∈ side ∧ oldVertex w ∉ side
  · obtain ⟨v, w, hv, hw⟩ := hOldSplit
    let oldSide : Finset (Fin n) :=
      Finset.univ.filter fun z => oldVertex z ∈ side
    obtain ⟨edge, hEdge⟩ := hConnected oldSide ⟨v, w, by simpa [oldSide] using hv,
      by simpa [oldSide] using hw⟩
    simp only [oldSide, Finset.mem_filter, Finset.mem_univ, true_and] at hEdge
    refine ⟨oldEdge edge, ?_⟩
    change
      (core source root).tail (oldEdge edge) ∈ side ∧
          (core source root).head (oldEdge edge) ∉ side ∨
        (core source root).head (oldEdge edge) ∈ side ∧
          (core source root).tail (oldEdge edge) ∉ side
    simpa only [core_tail_old, core_head_old] using hEdge
  · by_cases hRoot : oldVertex root ∈ side
    · obtain ⟨inside, outside, hInside, hOutside⟩ := hSplit
      have hOutsideVal : outside.val = n := by
        by_contra hNe
        have hLt : outside.val < n := by omega
        let oldOutside : Fin n := ⟨outside.val, hLt⟩
        have hEq : oldVertex oldOutside = outside := by
          apply Fin.ext
          rfl
        exact hOldSplit ⟨root, oldOutside, hRoot, by simpa [hEq] using hOutside⟩
      have hOutsideEq : outside = markerVertex := by
        apply Fin.ext
        simpa [markerVertex] using hOutsideVal
      have hMarkerOutside : markerVertex ∉ side := by
        simpa [hOutsideEq] using hOutside
      refine ⟨firstMarkerEdge, Or.inl ?_⟩
      change
        (core source root).tail firstMarkerEdge ∈ side ∧
          (core source root).head firstMarkerEdge ∉ side
      simpa only [core_tail_firstMarkerEdge, core_head_firstMarkerEdge] using
        And.intro hRoot hMarkerOutside
    · obtain ⟨inside, outside, hInside, hOutside⟩ := hSplit
      have hInsideVal : inside.val = n := by
        by_contra hNe
        have hLt : inside.val < n := by omega
        let oldInside : Fin n := ⟨inside.val, hLt⟩
        have hEq : oldVertex oldInside = inside := by
          apply Fin.ext
          rfl
        exact hOldSplit ⟨oldInside, root, by simpa [hEq] using hInside, hRoot⟩
      have hInsideEq : inside = markerVertex := by
        apply Fin.ext
        simpa [markerVertex] using hInsideVal
      have hMarkerInside : markerVertex ∈ side := by
        simpa [hInsideEq] using hInside
      refine ⟨firstMarkerEdge, Or.inr ?_⟩
      change
        (core source root).head firstMarkerEdge ∈ side ∧
          (core source root).tail firstMarkerEdge ∉ side
      simpa only [core_tail_firstMarkerEdge, core_head_firstMarkerEdge] using
        And.intro hMarkerInside hRoot

/-- Every positive subdivision of the two-cycle extension is connected. -/
theorem graph_connected (source : Spec n p) (root : Fin n)
    (hConnected : source.core.Connected) (k : ℕ) (hk : 0 < k) :
    graph_connected ((extension source root).scale k hk).graph := by
  apply ((extension source root).scale k hk).graph_connected_of_coreConnected
  exact core_connected source root hConnected

/-- The old core vertices, including the attachment root, form the retained
side of the articulation cut. -/
noncomputable def cutData (source : Spec n p) (root : Fin n) :
    CoreVertexCut.Data (extension source root).core where
  glue := oldVertex root
  left := Finset.univ.filter fun vertex => vertex.val < n

/-- The only extension slots leaving the old side start at the articulation,
so the displayed core cut is valid. -/
theorem cutData_valid (source : Spec n p) (root : Fin n) :
    (cutData source root).Valid := by
  constructor
  · simp [cutData, oldVertex]
  · intro edge
    by_cases hOld : edge.val < p
    · simp [CoreVertexCut.Data.Crosses, cutData, extension, core, hOld, oldVertex]
    · simp [CoreVertexCut.Data.Crosses, cutData, extension, core, hOld, oldVertex,
        markerVertex]

/-- The same passive cut data, typed directly over a scaled extension core.
Keeping this wrapper avoids relying on semireducible definitional equality of
`Spec.scale` while proving the retained-factor equivalence. -/
noncomputable def scaledCutData (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k) :
    CoreVertexCut.Data ((extension source root).scale k hk).core where
  glue := oldVertex root
  left := Finset.univ.filter fun vertex => vertex.val < n

theorem scaledCutData_valid (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k) :
    (scaledCutData source root k hk).Valid := by
  constructor
  · simp [scaledCutData, oldVertex]
  · intro edge
    by_cases hOld : edge.val < p
    · simp [CoreVertexCut.Data.Crosses, scaledCutData, extension, core, hOld,
        oldVertex]
    · simp [CoreVertexCut.Data.Crosses, scaledCutData, extension, core, hOld,
        oldVertex, markerVertex]

/-- The articulation cut lifted uniformly to the `k`-th regular subdivision. -/
noncomputable def cut (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k) :
    OneVertexCut ((extension source root).scale k hk).graph :=
  (scaledCutData source root k hk).toOneVertexCut
    ((extension source root).scale k hk)
      (scaledCutData_valid source root k hk)

/-! ## Identification of the retained factor -/

@[simp] theorem scale_length_old (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k) (edge : Fin p) :
    ((extension source root).scale k hk).length (oldEdge edge) =
      (source.scale k hk).length edge := by
  simp

/-- Embed every vertex of the scaled old subdivision into the corresponding
old core vertex or old path interior of the scaled extension. -/
def ambientVertex (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k) :
    (source.scale k hk).Vertex →
      ((extension source root).scale k hk).Vertex
  | Sum.inl vertex => Sum.inl (oldVertex vertex)
  | Sum.inr ⟨edge, offset⟩ =>
      Sum.inr ⟨oldEdge edge, ⟨offset.val, by simpa using offset.isLt⟩⟩

/-- Every embedded old vertex belongs to the retained side of the extension
cut. -/
theorem ambientVertex_mem_left (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k) (vertex : (source.scale k hk).Vertex) :
    ambientVertex source root k hk vertex ∈
      CoreVertexCut.Data.leftVertices ((extension source root).scale k hk)
        (scaledCutData source root k hk) := by
  cases vertex with
  | inl vertex =>
      simp only [ambientVertex]
      exact ((scaledCutData source root k hk).mem_leftVertices_core
        ((extension source root).scale k hk) (oldVertex vertex)).mpr (by
          simp [scaledCutData, oldVertex])
  | inr interior =>
      rcases interior with ⟨edge, offset⟩
      simp only [ambientVertex]
      exact ((scaledCutData source root k hk).mem_leftVertices_interior
        ((extension source root).scale k hk) (oldEdge edge)
          ⟨offset.val, by simpa using offset.isLt⟩).mpr (by
            simp [scaledCutData, extension, oldVertex])

/-- The old subdivision vertex as a vertex of the induced retained factor. -/
noncomputable def leftVertex (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k) (vertex : (source.scale k hk).Vertex) :
    (cut source root k hk).leftGraph.V :=
  ⟨ambientVertex source root k hk vertex,
    ambientVertex_mem_left source root k hk vertex⟩

theorem leftVertex_injective (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k) :
    Function.Injective (leftVertex source root k hk) := by
  intro first second hEqual
  have hValue := congrArg Subtype.val hEqual
  cases first with
  | inl first =>
      cases second with
      | inl second =>
          have hCore : first = second :=
            Fin.castSucc_inj.mp (Sum.inl.inj hValue)
          subst second
          rfl
      | inr second => simp [leftVertex, ambientVertex] at hValue
  | inr first =>
      cases second with
      | inl second => simp [leftVertex, ambientVertex] at hValue
      | inr second =>
          rcases first with ⟨firstEdge, firstOffset⟩
          rcases second with ⟨secondEdge, secondOffset⟩
          have hSigma := Sum.inr.inj hValue
          have hEdge : firstEdge = secondEdge := by
            apply Fin.ext
            exact congrArg (fun value => value.1.val) hSigma
          subst secondEdge
          have hOffset : firstOffset = secondOffset := by
            apply Fin.ext
            exact congrArg (fun value => value.2.val) hSigma
          subst secondOffset
          rfl

theorem leftVertex_surjective (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k) :
    Function.Surjective (leftVertex source root k hk) := by
  intro vertex
  have hMember := vertex.property
  change vertex.val ∈
    CoreVertexCut.Data.leftVertices ((extension source root).scale k hk)
      (scaledCutData source root k hk) at hMember
  cases hValue : vertex.val with
  | inl extendedCoreVertex =>
      have hLt : extendedCoreVertex.val < n := by
        rw [hValue] at hMember
        have hLeft := ((scaledCutData source root k hk).mem_leftVertices_core
          ((extension source root).scale k hk) extendedCoreVertex).mp (by
            simpa only [SubdivisionGraph.Spec.coreVertex] using hMember)
        simpa [scaledCutData] using hLeft
      let sourceCoreVertex : Fin n := ⟨extendedCoreVertex.val, hLt⟩
      refine ⟨Sum.inl sourceCoreVertex, ?_⟩
      apply Subtype.ext
      rw [hValue]
      apply congrArg Sum.inl
      apply Fin.ext
      rfl
  | inr extendedInterior =>
      rcases extendedInterior with ⟨extendedEdge, extendedOffset⟩
      rw [hValue] at hMember
      have hLeft :
          ((extension source root).scale k hk).core.tail extendedEdge ∈
              (scaledCutData source root k hk).left ∧
            ((extension source root).scale k hk).core.head extendedEdge ∈
              (scaledCutData source root k hk).left :=
        ((scaledCutData source root k hk).mem_leftVertices_interior
          ((extension source root).scale k hk) extendedEdge extendedOffset).mp (by
            simpa only [SubdivisionGraph.Spec.interiorVertex] using hMember)
      have hOld : extendedEdge.val < p := by
        by_contra hNotOld
        have hMarkerLeft : markerVertex ∈
            (scaledCutData source root k hk).left := by
          have := hLeft.2
          simpa [extension, core, hNotOld] using this
        simp [scaledCutData, markerVertex] at hMarkerLeft
      let sourceEdge : Fin p := ⟨extendedEdge.val, hOld⟩
      have hLength :
          ((extension source root).scale k hk).length extendedEdge =
            (source.scale k hk).length sourceEdge := by
        simp [sourceEdge, extension, hOld]
      have hOffsetBound :
          extendedOffset.val < (source.scale k hk).length sourceEdge - 1 := by
        rw [← hLength]
        exact extendedOffset.isLt
      let sourceOffset : Fin ((source.scale k hk).length sourceEdge - 1) :=
        ⟨extendedOffset.val, hOffsetBound⟩
      refine ⟨Sum.inr ⟨sourceEdge, sourceOffset⟩, ?_⟩
      apply Subtype.ext
      rw [hValue]
      have hEdgeEq : oldEdge sourceEdge = extendedEdge := by
        apply Fin.ext
        rfl
      cases hEdgeEq
      congr 2

/-- The vertex equivalence underlying the retained-factor graph
identification. -/
noncomputable def leftVertexEquiv (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k) :
    (source.scale k hk).Vertex ≃ (cut source root k hk).leftGraph.V :=
  Equiv.ofBijective (leftVertex source root k hk)
    ⟨leftVertex_injective source root k hk,
      leftVertex_surjective source root k hk⟩

/-- Embed an old unit step into the same occurrence and offset of the scaled
extension. -/
def oldStep (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k) :
    (source.scale k hk).Step → ((extension source root).scale k hk).Step
  | ⟨edge, offset⟩ =>
      ⟨oldEdge edge, ⟨offset.val, by simpa using offset.isLt⟩⟩

theorem oldStep_injective (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k) :
    Function.Injective (oldStep source root k hk) := by
  rintro ⟨firstEdge, firstOffset⟩ ⟨secondEdge, secondOffset⟩ hEqual
  have hEdge : firstEdge = secondEdge := by
    apply Fin.ext
    exact congrArg (fun step => step.1.val) hEqual
  subst secondEdge
  have hOffset : firstOffset = secondOffset := by
    apply Fin.ext
    exact congrArg (fun step => step.2.val) hEqual
  subst secondOffset
  rfl

/-- Old unit-edge endpoints commute with the old-vertex embedding. -/
theorem unitEdge_oldStep (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k) (step : (source.scale k hk).Step) :
    ((extension source root).scale k hk).unitEdge
        (oldStep source root k hk step) =
      (ambientVertex source root k hk
          ((source.scale k hk).unitEdge step).1,
        ambientVertex source root k hk
          ((source.scale k hk).unitEdge step).2) := by
  rcases step with ⟨edge, offset⟩
  apply Prod.ext
  · change
      ((extension source root).scale k hk).stepLeft (oldEdge edge)
          ⟨offset.val, by simpa using offset.isLt⟩ =
        ambientVertex source root k hk
          ((source.scale k hk).stepLeft edge offset)
    by_cases hzero : offset.val = 0
    · simp [Spec.stepLeft, hzero, Spec.coreVertex,
        ambientVertex, extension, core, oldEdge, oldVertex]
    · simp [Spec.stepLeft, hzero, Spec.interiorVertex,
        ambientVertex, extension, core, oldEdge, oldVertex]
  · change
      ((extension source root).scale k hk).stepRight (oldEdge edge)
          ⟨offset.val, by simpa using offset.isLt⟩ =
        ambientVertex source root k hk
          ((source.scale k hk).stepRight edge offset)
    by_cases hlast : offset.val + 1 = (source.scale k hk).length edge
    · have hlastSource : offset.val + 1 = k * source.length edge := by
        simpa using hlast
      simp [Spec.stepRight, hlastSource, Spec.coreVertex, ambientVertex,
        extension, core, oldEdge, oldVertex]
    · have hlastSource : ¬ offset.val + 1 = k * source.length edge := by
        simpa using hlast
      simp [Spec.stepRight, hlastSource, Spec.interiorVertex,
        ambientVertex, extension, core, oldEdge, oldVertex]

/-- The embedded old-vertex map is injective before adding the membership
proof for the induced factor. -/
theorem ambientVertex_injective (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k) :
    Function.Injective (ambientVertex source root k hk) := by
  intro first second hEqual
  apply leftVertex_injective source root k hk
  apply Subtype.ext
  exact hEqual

/-- On either new marker slot, the right endpoint of every unit step lies
outside the retained old side. -/
theorem stepRight_not_mem_left_of_new
    (source : Spec n p) (root : Fin n) (k : ℕ) (hk : 0 < k)
    (edge : Fin (p + 2)) (hNew : ¬ edge.val < p)
    (offset : Fin (((extension source root).scale k hk).length edge)) :
    ((extension source root).scale k hk).stepRight edge offset ∉
      CoreVertexCut.Data.leftVertices ((extension source root).scale k hk)
        (scaledCutData source root k hk) := by
  rw [Spec.stepRight]
  split_ifs with hLast
  · intro hMember
    have hCore := ((scaledCutData source root k hk).mem_leftVertices_core
      ((extension source root).scale k hk) markerVertex).mp (by
        simpa [extension, core, hNew] using hMember)
    simp [scaledCutData, markerVertex] at hCore
  · intro hMember
    have hInterior :=
      ((scaledCutData source root k hk).mem_leftVertices_interior
        ((extension source root).scale k hk) edge
          ⟨offset.val, by have := offset.isLt; omega⟩).mp (by
            simpa using hMember)
    have hMarker := hInterior.2
    simp [scaledCutData, extension, core, hNew, markerVertex] at hMarker

/-- Any extension step whose two endpoints are embedded old vertices must be
an old edge occurrence. -/
theorem edge_old_of_unitEdge_between_ambient
    (source : Spec n p) (root : Fin n) (k : ℕ) (hk : 0 < k)
    (step : ((extension source root).scale k hk).Step)
    (first second : (source.scale k hk).Vertex)
    (hBetween :
      ((extension source root).scale k hk).unitEdge step =
          (ambientVertex source root k hk first,
            ambientVertex source root k hk second) ∨
        ((extension source root).scale k hk).unitEdge step =
          (ambientVertex source root k hk second,
            ambientVertex source root k hk first)) :
    step.1.val < p := by
  by_contra hNew
  have hOutside := stepRight_not_mem_left_of_new source root k hk
    step.1 hNew step.2
  apply hOutside
  rcases hBetween with hForward | hBackward
  · rw [show ((extension source root).scale k hk).stepRight step.1 step.2 =
        ambientVertex source root k hk second from congrArg Prod.snd hForward]
    exact ambientVertex_mem_left source root k hk second
  · rw [show ((extension source root).scale k hk).stepRight step.1 step.2 =
        ambientVertex source root k hk first from congrArg Prod.snd hBackward]
    exact ambientVertex_mem_left source root k hk first

/-- The unit steps of a subdivision occurrence whose unordered endpoints are
the displayed pair. -/
abbrev MatchingStep (spec : Spec n p) (first second : spec.Vertex) :=
  {step : spec.Step //
    spec.unitEdge step = (first, second) ∨
      spec.unitEdge step = (second, first)}

/-- Recover the source step occupying an old edge occurrence of the
extension. -/
def sourceStepOfOld (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k)
    (step : ((extension source root).scale k hk).Step)
    (hOld : step.1.val < p) : (source.scale k hk).Step :=
  ⟨⟨step.1.val, hOld⟩, ⟨step.2.val, by
    simpa [extension, hOld] using step.2.isLt⟩⟩

@[simp] theorem oldStep_sourceStepOfOld
    (source : Spec n p) (root : Fin n) (k : ℕ) (hk : 0 < k)
    (step : ((extension source root).scale k hk).Step)
    (hOld : step.1.val < p) :
    oldStep source root k hk (sourceStepOfOld source root k hk step hOld) =
      step := by
  rcases step with ⟨edge, offset⟩
  apply Sigma.ext
  · apply Fin.ext
    rfl
  · apply heq_of_eq
    apply Fin.ext
    rfl

@[simp] theorem sourceStepOfOld_oldStep
    (source : Spec n p) (root : Fin n) (k : ℕ) (hk : 0 < k)
    (step : (source.scale k hk).Step) :
    sourceStepOfOld source root k hk (oldStep source root k hk step)
        (by exact step.1.isLt) = step := by
  rcases step with ⟨edge, offset⟩
  apply Sigma.ext
  · apply Fin.ext
    rfl
  · apply heq_of_eq
    apply Fin.ext
    rfl

/-- Embed a source step between a fixed unordered pair into the matching step
of the extension. -/
def matchingOldStep (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k)
    (first second : (source.scale k hk).Vertex) :
    MatchingStep (source.scale k hk) first second →
      MatchingStep ((extension source root).scale k hk)
        (ambientVertex source root k hk first)
        (ambientVertex source root k hk second) := fun step =>
  ⟨oldStep source root k hk step.val, by
    rw [unitEdge_oldStep]
    rcases step.property with hForward | hBackward
    · left
      rw [hForward]
    · right
      rw [hBackward]⟩

theorem matchingOldStep_injective (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k)
    (first second : (source.scale k hk).Vertex) :
    Function.Injective
      (matchingOldStep source root k hk first second) := by
  intro firstStep secondStep hEqual
  apply Subtype.ext
  apply oldStep_injective source root k hk
  simpa only [matchingOldStep] using congrArg Subtype.val hEqual

theorem matchingOldStep_surjective (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k)
    (first second : (source.scale k hk).Vertex) :
    Function.Surjective
      (matchingOldStep source root k hk first second) := by
  intro extendedStep
  have hOld : extendedStep.val.1.val < p :=
    edge_old_of_unitEdge_between_ambient source root k hk extendedStep.val
      first second extendedStep.property
  let sourceStep :=
    sourceStepOfOld source root k hk extendedStep.val hOld
  have hStepEq : oldStep source root k hk sourceStep = extendedStep.val := by
    exact oldStep_sourceStepOfOld source root k hk extendedStep.val hOld
  have hExtendedBetween :
      ((extension source root).scale k hk).unitEdge
            (oldStep source root k hk sourceStep) =
          (ambientVertex source root k hk first,
            ambientVertex source root k hk second) ∨
        ((extension source root).scale k hk).unitEdge
            (oldStep source root k hk sourceStep) =
          (ambientVertex source root k hk second,
            ambientVertex source root k hk first) := by
    simpa only [hStepEq] using extendedStep.property
  have hSourceBetween :
      (source.scale k hk).unitEdge sourceStep = (first, second) ∨
        (source.scale k hk).unitEdge sourceStep = (second, first) := by
    rw [unitEdge_oldStep] at hExtendedBetween
    rcases hExtendedBetween with hForward | hBackward
    · left
      apply Prod.ext
      · apply ambientVertex_injective source root k hk
        exact congrArg Prod.fst hForward
      · apply ambientVertex_injective source root k hk
        exact congrArg Prod.snd hForward
    · right
      apply Prod.ext
      · apply ambientVertex_injective source root k hk
        exact congrArg Prod.fst hBackward
      · apply ambientVertex_injective source root k hk
        exact congrArg Prod.snd hBackward
  refine ⟨⟨sourceStep, hSourceBetween⟩, ?_⟩
  apply Subtype.ext
  simpa only [matchingOldStep] using hStepEq

/-- Matching unit steps on the old side correspond occurrence-for-occurrence,
including parallel old slots. -/
noncomputable def matchingStepEquiv (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k)
    (first second : (source.scale k hk).Vertex) :
    MatchingStep (source.scale k hk) first second ≃
      MatchingStep ((extension source root).scale k hk)
        (ambientVertex source root k hk first)
        (ambientVertex source root k hk second) :=
  Equiv.ofBijective (matchingOldStep source root k hk first second)
    ⟨matchingOldStep_injective source root k hk first second,
      matchingOldStep_surjective source root k hk first second⟩

/-- The ambient extension has exactly the same multiplicity between embedded
old vertices as the source subdivision. -/
theorem num_edges_ambientVertex (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k)
    (first second : (source.scale k hk).Vertex) :
    num_edges ((extension source root).scale k hk).graph
        (ambientVertex source root k hk first)
        (ambientVertex source root k hk second) =
      num_edges (source.scale k hk).graph first second := by
  classical
  rw [((extension source root).scale k hk).num_edges_eq_card_filter_steps,
    (source.scale k hk).num_edges_eq_card_filter_steps]
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact (Fintype.card_congr
    (matchingStepEquiv source root k hk first second)).symm

@[simp] theorem leftVertexEquiv_apply (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k) (vertex : (source.scale k hk).Vertex) :
    leftVertexEquiv source root k hk vertex =
      leftVertex source root k hk vertex := rfl

/-- The retained factor of the scaled pendant extension is Laplacian-equivalent
to the correspondingly scaled source subdivision. -/
noncomputable def leftLaplacianEquiv (source : Spec n p) (root : Fin n)
    (k : ℕ) (hk : 0 < k) :
    LaplacianEquiv (source.scale k hk).graph
      (cut source root k hk).leftGraph where
  toEquiv := leftVertexEquiv source root k hk
  num_edges_eq := by
    intro first second
    calc
      num_edges (cut source root k hk).leftGraph
          ((leftVertexEquiv source root k hk) first)
          ((leftVertexEquiv source root k hk) second) =
        num_edges ((extension source root).scale k hk).graph
          ((leftVertexEquiv source root k hk first).val)
          ((leftVertexEquiv source root k hk second).val) :=
            num_edges_inducedSubgraph
              ((extension source root).scale k hk).graph
              (cut source root k hk).left
              (cut source root k hk).left_nonempty
              (leftVertexEquiv source root k hk first)
              (leftVertexEquiv source root k hk second)
      _ = num_edges (source.scale k hk).graph first second := by
        change num_edges ((extension source root).scale k hk).graph
            (ambientVertex source root k hk first)
            (ambientVertex source root k hk second) =
          num_edges (source.scale k hk).graph first second
        exact num_edges_ambientVertex source root k hk first second

/-- The explicit two-cycle attachment supplies every field of the abstract
scale-compatible pendant-extension interface. -/
noncomputable def regularPendantExtension (source : Spec n p) (root : Fin n)
    (hConnected : _root_.graph_connected source.graph) :
    DraismaVargas.RegularPendantExtension source (extension source root) where
  connected := fun k hk => graph_connected source root
    (Utilities.Certificate.PseudocorePresentation.core_connected_of_graph_connected
      source hConnected) k hk
  cut := cut source root
  leftEquiv := leftLaplacianEquiv source root

/-- Concrete odd-to-even reduction: the even-genus bound on the two-cycle
extension retracts to the required odd-genus bound on the source metric. -/
theorem odd_regularSubdivisionGonality_le_of_twoCycle
    (source : Spec n p) (root : Fin n)
    (hConnected : _root_.graph_connected source.graph)
    (hOdd : Odd (p + 1 - n))
    (hEven : (extension source root).regularSubdivisionGonality ≤
      ((p + 2) + 2 - (n + 1)) / 2 + 1) :
    source.regularSubdivisionGonality ≤ (p + 2 - n) / 2 + 1 := by
  apply DraismaVargas.odd_regularSubdivisionGonality_le_of_regularPendantExtension
    hConnected hOdd
      (genusIndex_extension source
        (core_vertices_le_edges_add_one source hConnected))
      (regularPendantExtension source root hConnected)
  exact hEven

end DraismaVargas.OddGenusTwoCycle
