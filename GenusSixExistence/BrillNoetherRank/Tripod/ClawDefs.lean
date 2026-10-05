import DraismaVargasCount.EvenGenusParity
import GenusSixExistence.BrillNoetherRank.Tripod.Gadget

/-!
# The claw and glued predicates over the tripod gadget

The definitions shared by the dichotomy, the gluing bijection and the realisation, in the
namespace `GenusSixExistence.Tripod.Classification`:

* `TripodFrame.IsClaw` (`φ(c) ∉ φ(G)`) and `TripodFrame.IsGlued` (every leg starts up a leaf
  edge), on frames, members and classes, with their invariance under isomorphism;
* `Admissible`, the admissible requests of §6.3;
* `markedSpec` and `marksDivisor`, the marked core as a subdivision specification and its marks.

Prose: `Research/genus-six-brill-noether-rank.md`, §3.4 (Claw members, and the parity argument)
and §6.3 (Admissible requests, and the parity of the claw classes); section and statement
numbers in this file refer to that note.
-/

namespace GenusSixExistence.Tripod.Classification

open DraismaVargas.Count
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open Gadget

variable {n p degree : ℕ} {core : Core n p} {s : MarkSlots p}

/-- A **leaf edge** of a target graph: one of its two ends has valency one. -/
def IsLeafEdge (T : CFGraph) (t : T.edges) : Prop :=
  vertex_degree T (t : T.V × T.V).1 = 1 ∨ vertex_degree T (t : T.V × T.V).2 = 1

/-! ## 1.  The two classes, on frames -/

namespace TripodFrame

variable (κ : Frame (tripodCore core s) degree)

/-- The target vertex `φ(c)` under the centre of the tripod. -/
def centreTarget : κ.target.V := (κ.ident.vertex.symm (centre n)).1.1.1

/-- The source vertex of mark `k`. -/
def markSource (k : Fin 3) : κ.data.SourceVertex := (κ.ident.vertex.symm (tripodMark n k)).1

/-- **`T̂ = φ(G)`**, as a set of target vertices: the endpoints of the target edges under the
non-dangling source edges of the G-slots. -/
def gImage : Set κ.target.V :=
  {t | ∃ e : NonDanglingEdge κ.data, IsGSlot (κ.ident.row e.stablePath) ∧
    (((e.1.1.1 : κ.target.edges) : κ.target.V × κ.target.V).1 = t ∨
      ((e.1.1.1 : κ.target.edges) : κ.target.V × κ.target.V).2 = t)}

/-- **A claw frame** (Theorem 4.7(b), §3.4): `φ(c) ∉ φ(G)`. At long legs this is `k₀ = 0`
(Corollary 4.10). -/
def IsClaw : Prop := centreTarget κ ∉ gImage κ

/-- **A glued frame** (§3.3): at every mark, the leg starts up a leaf edge of
the target. At long legs this is `k₀ = 1` (Corollary 4.10 with §4.8). -/
def IsGlued : Prop :=
  ∀ k : Fin 3, ∃ e : NonDanglingEdge κ.data, κ.ident.row e.stablePath = legSlot p k ∧
    Incident κ.data e.1 (markSource κ k) ∧ IsLeafEdge κ.target e.1.1.1

end TripodFrame

/-! ## 2.  On members and on classes -/

/-- A member is a claw member when its frame is a claw frame. -/
def MemberIsClaw {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
    (mem : FibreMember (tripodCore core s) y degree) : Prop :=
  TripodFrame.IsClaw (Frame.of mem)

/-- A member is glued when its frame is glued. -/
def MemberIsGlued {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
    (mem : FibreMember (tripodCore core s) y degree) : Prop :=
  TripodFrame.IsGlued (Frame.of mem)

/-- A class is a claw class when it has a claw representative. -/
def ClassIsClaw {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
    (c : GeometricFibre (tripodCore core s) y degree) : Prop :=
  ∃ mem, GeometricFibre.cls mem = c ∧ MemberIsClaw mem

/-- A class is glued when it has a glued representative. -/
def ClassIsGlued {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
    (c : GeometricFibre (tripodCore core s) y degree) : Prop :=
  ∃ mem, GeometricFibre.cls mem = c ∧ MemberIsGlued mem

/-! ### Transport along an isomorphism over the core

`iso.datum` relabels the target (`targetVertex`, `targetEdge`, compatible with the unordered
ends) and the source (`sourceVertexEquiv`, `sourceEdgeEquiv`); `overCore_vertex` and
`overCore_row` say that the induced dictionaries `branchVertexEquiv` and `stablePathEquiv`
(`GeometricStableTransport`) fix the core identification. So everything the two predicates read
off a frame moves with the relabelling. -/

/-- A target relabelling of gluing data is a graph isomorphism, so it preserves leaf edges. -/
theorem isLeafEdge_map {target₁ target₂ : CFGraph} {first : GluingDatum target₁ degree}
    {second : GluingDatum target₂ degree} (iso : GeometricDatumIso first second)
    (t : target₁.edges) : IsLeafEdge target₂ (iso.targetEdge t) ↔ IsLeafEdge target₁ t := by
  have hdeg : ∀ v, vertex_degree target₂ (iso.targetVertex v) = vertex_degree target₁ v :=
    iso.targetLaplacianEquiv.vertex_degree_eq
  unfold IsLeafEdge
  rcases iso.ends t with h | h <;> rw [h] <;> simp only [hdeg]
  exact or_comm

section Transport

variable {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
  {first second : FibreMember (tripodCore core s) y degree} (iso : GeometricMemberIso first second)

include iso in
/-- The branch vertex over a core vertex moves along the induced branch dictionary. -/
theorem ident_vertex_symm_of_iso (v : Fin (n + 1 + 1 + 1 + 1)) :
    second.ident.vertex.symm v =
      iso.datum.branchVertexEquiv first.fullDim.valid.1 (first.ident.vertex.symm v) := by
  rw [Equiv.symm_apply_eq, iso.overCore_vertex, Equiv.apply_symm_apply]

include iso in
theorem centreTarget_of_iso :
    TripodFrame.centreTarget (Frame.of second) =
      iso.datum.targetVertex (TripodFrame.centreTarget (Frame.of first)) := by
  show (second.ident.vertex.symm (centre n)).1.1.1 = _
  rw [ident_vertex_symm_of_iso iso]
  rfl

include iso in
theorem markSource_of_iso (k : Fin 3) :
    TripodFrame.markSource (Frame.of second) k =
      iso.datum.sourceVertexEquiv (TripodFrame.markSource (Frame.of first) k) := by
  show (second.ident.vertex.symm (tripodMark n k)).1 = _
  rw [ident_vertex_symm_of_iso iso]
  rfl

include iso in
/-- A non-dangling source edge keeps its core row under the source relabelling. -/
theorem row_of_iso (e : NonDanglingEdge first.data) :
    second.ident.row (iso.datum.nonDanglingEdgeEquiv first.fullDim.valid.1 e).stablePath =
      first.ident.row e.stablePath :=
  iso.overCore_row e.stablePath

include iso in
theorem mem_gImage_of_iso {t : first.target.V} (ht : t ∈ TripodFrame.gImage (Frame.of first)) :
    iso.datum.targetVertex t ∈ TripodFrame.gImage (Frame.of second) := by
  obtain ⟨e, hG, he⟩ := ht
  refine ⟨iso.datum.nonDanglingEdgeEquiv first.fullDim.valid.1 e, ?_, ?_⟩
  · exact (congrArg IsGSlot (row_of_iso iso e)).mpr hG
  · exact (iso.datum.target_incident_map_iff e.1.1.1 t).mpr he

include iso in
theorem mem_gImage_iff_of_iso (t : first.target.V) :
    iso.datum.targetVertex t ∈ TripodFrame.gImage (Frame.of second) ↔
      t ∈ TripodFrame.gImage (Frame.of first) := by
  refine ⟨fun h ↦ ?_, mem_gImage_of_iso iso⟩
  have hBack := mem_gImage_of_iso iso.symm h
  have hInv : iso.symm.datum.targetVertex (iso.datum.targetVertex t) = t :=
    iso.datum.targetVertex.symm_apply_apply t
  rwa [hInv] at hBack

include iso in
theorem memberIsGlued_of_iso (h : MemberIsGlued first) : MemberIsGlued second := by
  intro k
  obtain ⟨e, hRow, hInc, hLeaf⟩ := h k
  refine ⟨iso.datum.nonDanglingEdgeEquiv first.fullDim.valid.1 e, ?_, ?_, ?_⟩
  · exact (row_of_iso iso e).trans hRow
  · show Incident second.data (iso.datum.sourceEdgeEquiv e.1)
      (TripodFrame.markSource (Frame.of second) k)
    rw [markSource_of_iso iso]
    exact (iso.datum.incident_map_iff e.1 _).mpr hInc
  · exact (isLeafEdge_map iso.datum e.1.1.1).mpr hLeaf

end Transport

/-- Claw-ness is invariant under isomorphism over the core. -/
theorem memberIsClaw_iff_of_iso {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
    {first second : FibreMember (tripodCore core s) y degree}
    (iso : GeometricMemberIso first second) : MemberIsClaw first ↔ MemberIsClaw second := by
  unfold MemberIsClaw TripodFrame.IsClaw
  rw [centreTarget_of_iso iso]
  exact not_congr (mem_gImage_iff_of_iso iso _).symm

/-- Glued-ness is invariant under isomorphism over the core. -/
theorem memberIsGlued_iff_of_iso {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
    {first second : FibreMember (tripodCore core s) y degree}
    (iso : GeometricMemberIso first second) : MemberIsGlued first ↔ MemberIsGlued second :=
  ⟨memberIsGlued_of_iso iso, memberIsGlued_of_iso iso.symm⟩

theorem classIsClaw_cls {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
    (mem : FibreMember (tripodCore core s) y degree) :
    ClassIsClaw (GeometricFibre.cls mem) ↔ MemberIsClaw mem := by
  constructor
  · rintro ⟨mem', h, hClaw⟩
    obtain ⟨iso⟩ := GeometricFibre.cls_eq_cls_iff.mp h
    exact (memberIsClaw_iff_of_iso iso).mp hClaw
  · exact fun h ↦ ⟨mem, rfl, h⟩

theorem classIsGlued_cls {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
    (mem : FibreMember (tripodCore core s) y degree) :
    ClassIsGlued (GeometricFibre.cls mem) ↔ MemberIsGlued mem := by
  constructor
  · rintro ⟨mem', h, hGlued⟩
    obtain ⟨iso⟩ := GeometricFibre.cls_eq_cls_iff.mp h
    exact (memberIsGlued_iff_of_iso iso).mp hGlued
  · exact fun h ↦ ⟨mem, rfl, h⟩

/-! ## Admissible requests -/

/-- **Admissible requests** (§6.3): positive; general for `Γ̃` in degree five and, at the
base request, for `G̃` in degree four; avoiding every functional of `B`; with long legs. A
functional is its coefficient vector, `w ↦ ∑ i, w i * y i`. -/
def Admissible (core : Core n p) (s : MarkSlots p) (B : Finset (Fin (p + 1 + 1 + 1 + 3) → ℚ))
    (y : Fin (p + 1 + 1 + 1 + 3) → ℚ) : Prop :=
  (∀ i, 0 < y i) ∧
    StepSupplyReduction.GeneralRequest (tripodCore core s) (3 + 2) y ∧
    StepSupplyReduction.GeneralRequest core (2 + 2) (baseRequest s y) ∧
    (∀ w ∈ B, ∑ i, w i * y i ≠ 0) ∧
    LongLegs s y

/-! ## The marked core as a specification -/

/-- The marked core with positive integral slot lengths, as a subdivision specification. -/
def markedSpec (core : Core n p) (s : MarkSlots p) (hloop : ∀ i, core.tail i ≠ core.head i)
    (ℓ : Fin (p + 1 + 1 + 1) → ℕ) (hℓ : ∀ i, 0 < ℓ i) : Spec (n + 1 + 1 + 1) (p + 1 + 1 + 1) :=
  Spec.ofCore (markedCore core s) (by omega) (markedCore_loopless core s hloop) ℓ hℓ

/-- The divisor `p + q + r` of the three marks. -/
def marksDivisor (S : Spec (n + 1 + 1 + 1) (p + 1 + 1 + 1)) : CFDiv S.graph :=
  ∑ k : Fin 3, one_chip (S.coreVertex (markVertex n k))

end GenusSixExistence.Tripod.Classification
