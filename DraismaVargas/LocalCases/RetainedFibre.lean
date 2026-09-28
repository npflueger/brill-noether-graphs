import DraismaVargas.LocalCases.RetainedTraversal

/-!
# The requested core vertices on the terminal face: fibres and markers

**Source.**  Draisma--Vargas Part I, the proof of the main theorem (a
non-trivalent requested type presented as a point of the closed cone of a
trivalent one, with zero length exactly on the collapsed edges).  On a terminal
face the class of a requested core vertex is to be computed at any model vertex
over it,
`vertexClass (Sum.inl w) := classOf (vertexAt (any model vertex over w))`, and
this is well defined because the rows of the expansion forest are zero rows.
That statement is the theorem proved here; the argument is not in either paper.

## What is proved

The retained core model has to send the core vertices of the **requested**
specification `spec₀` into the terminal face's contraction classes and cut
points, while the dictionary it is given places the core vertices of the
**cubic model** `D.bigSpec spec₀ hN hL`.  The expansion datum of the reduction
to a cubic model relates the two
by `ExpansionData.fib : Fin N → Fin n₀`, which is a quotient map: a requested
core vertex is the image of a whole fibre of model core vertices, joined to one
another by contracted slots.

* §1 `coreClass` is the contraction class a model core vertex sits in.  A
  forest slot does not separate its two ends
  (`coreClass_tail_eq_head_of_mem_forest`): the row displaying it is contracted
  whole, so `RetainedTraversal.classOf_finish_eq_classOf_start_of_mem_forest`
  applies.

* §2 is the theorem: **the class depends only on the fibre**
  (`coreClass_eq_of_fib_eq`).  The proof is `ExpansionData.Conditions`' last
  clause -- a fibre that meets a finset and its complement is crossed by a
  *contracted* slot inside the fibre -- run at the finset of model vertices
  whose class is a fixed one.  Hence `requestedClass`, the class of a requested
  core vertex that is in the image of the fibre map, with
  `requestedClass_eq` saying it may be computed at any preimage.

* §3 the markers: the requested core vertex in the middle of a `double` slot is
  **not** in the image of the fibre map (`not_exists_fib_eq_marker`, from
  `ExpansionData.MarkerIsolated`), and no other requested slot ends there
  (`eq_of_head_eq_marker`).  `isMarker_or_exists_fib` proves the converse
  direction from `ExpansionData.Conditions` alone, so `IsMarker` and "in the
  image of `fib`" **partition** the requested core vertices
  (`not_isMarker_of_exists_fib` makes the two exclusive).  That is exactly what
  lets a retained core model define its vertex map by cases with no junk value:
  the non-markers go to the contraction class §2 computes, and the markers to
  the **new** split vertices produced by `RetainedCut.cutChain`.

* §4 locates the markers metrically: `RetainedCut.cutOffsetAt` at the datum the
  reduction produces is the scaled length of the first requested slot the retained cubic
  slot carries (`cutOffsetAt_double`), i.e. exactly the marker's position along
  the row, and on a `single` slot it is the whole row total
  (`cutOffsetAt_single`), so nothing is cut there.

## What is NOT proved -- the hypotheses that remain explicit

1. **No vertex map is built.**  §1--§4 are the well-definedness, exhaustiveness
   and location facts a `RefinementCore.CoreModel`'s `vertexModel` needs; the
   map itself, its injectivity and the genus count (`Exhausts` at a general
   forest) are built elsewhere: the map in `RetainedVertexModel`, its
   injectivity in `RetainedClassInjectivity`, the genus count in
   `RetainedExhausts`.  In particular
   nothing here says *which* new split vertex of `RetainedCut.cutSpec` a marker
   goes to -- that needs the straddle analysis of
   `RetainedCut.positiveSegments_pieces` at the marker's own row.
2. **Nothing about an aligned marker.**  When the marker's metric position is a
   partial sum of the cleared occurrence lengths, no kept slot is cut and the
   marker's image is a contraction class after all, not a new split vertex.  The
   case split is `RetainedCut.positiveSegments_pieces`' `if`, and is left to the
   consumer.
3. Everything `RetainedRelabeling.CutRelabeling` keeps inside its binder.

## Consumers

The retained core model behind `RetainedRelabeling.CutRelabeling`
(`RetainedVertexModel`).
-/

namespace DraismaVargas.LocalCases.RetainedFibre

noncomputable section

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Subdivision.CoreExpansion
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.OrientedTraversal
open DraismaVargas.LocalCases.RequestedExpandedEndpoints
open DraismaVargas.LocalCases.RetainedCut
open DraismaVargas.LocalCases.TraversalPresentation

variable {target : CFGraph} {degree : ℕ}
  {gluing : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree gluing wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ}
  {strong : StrongPresentation candidate.datum coordinate}
  {face : ClearedFace candidate strong.toPresentation coordinates}
  {n₀ p₀ N Q : ℕ} {D : ExpansionData n₀ p₀ N Q} {spec₀ : Spec n₀ p₀}
  {hN : 0 < N} {hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e}
  {iface : InputInterface (D.bigSpec spec₀ hN hL) strong.toPresentation coordinates
    (expansionForest D)}

/-! ## 1.  The class of a model core vertex -/

/-- The contraction class of the terminal face at which the dictionary places a
core vertex of the cubic model. -/
def coreClass (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface)
    (topology : ClearedFace.SourceContractionTopology face) (v : Fin N) :
    topology.degSpec.Class :=
  classOf topology (dict.vertexAt v)

/-- **A forest slot does not separate its two ends.**  Its row is contracted
whole inside the face. -/
theorem coreClass_tail_eq_head_of_mem_forest
    (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface)
    (topology : ClearedFace.SourceContractionTopology face)
    {e : Fin Q} (he : e ∈ expansionForest D) :
    coreClass dict topology (D.bigCore.tail e) =
      coreClass dict topology (D.bigCore.head e) := by
  show classOf topology (dict.vertexAt ((D.bigSpec spec₀ hN hL).core.tail e)) =
    classOf topology (dict.vertexAt ((D.bigSpec spec₀ hN hL).core.head e))
  rw [dict.tail_eq e, dict.head_eq e]
  exact (RetainedTraversal.classOf_finish_eq_classOf_start_of_mem_forest
    (iface := iface) topology he).symm

/-! ## 2.  The class depends only on the fibre -/

/-- **The class of a model core vertex depends only on its fibre.**

`ExpansionData.Conditions`' last clause says a fibre that meets a finset and
its complement is crossed by a *contracted* slot lying inside the fibre.  Run
at the finset of model core vertices sharing a fixed class, and §1, that is a
contradiction: a contracted slot has both ends in one class.  So
`vertexClass (Sum.inl w) := classOf (vertexAt (any model vertex over w))` is
well defined. -/
theorem coreClass_eq_of_fib_eq (hCond : D.Conditions spec₀.core)
    (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface)
    (topology : ClearedFace.SourceContractionTopology face)
    {v v' : Fin N} (h : D.fib v = D.fib v') :
    coreClass dict topology v = coreClass dict topology v' := by
  classical
  by_contra hne
  set T : Finset (Fin N) :=
    Finset.univ.filter fun u ↦ coreClass dict topology u = coreClass dict topology v with hT
  have hvT : v ∈ T := by simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
  have hv'T : v' ∉ T := by
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun hc ↦ hne hc.symm
  obtain ⟨e, hkind, -, hcross⟩ :=
    ExpansionData.fibre_of_conditions hCond (D.fib v) T ⟨v, hvT, rfl⟩ ⟨v', hv'T, h.symm⟩
  have heF : e ∈ expansionForest D := (mem_expansionForest D e).mpr hkind
  have hcls := coreClass_tail_eq_head_of_mem_forest dict topology heF
  rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine h2 ?_
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at h1 ⊢
    rw [← hcls]
    exact h1
  · refine h2 ?_
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at h1 ⊢
    rw [hcls]
    exact h1

/-- The contraction class of a requested core vertex that is in the image of
the fibre map. -/
def requestedClass (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface)
    (topology : ClearedFace.SourceContractionTopology face)
    {w : Fin n₀} (hw : ∃ v : Fin N, D.fib v = w) : topology.degSpec.Class :=
  coreClass dict topology hw.choose

/-- **and it may be computed at any preimage.** -/
theorem requestedClass_eq (hCond : D.Conditions spec₀.core)
    (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface)
    (topology : ClearedFace.SourceContractionTopology face)
    {w : Fin n₀} (hw : ∃ v : Fin N, D.fib v = w) {v : Fin N} (hv : D.fib v = w) :
    requestedClass dict topology hw = coreClass dict topology v :=
  coreClass_eq_of_fib_eq hCond dict topology (by rw [hw.choose_spec, hv])

/-! ## 3.  The markers are outside the image of the fibre map -/

/-- **A marker is not the image of any model core vertex.**  This is
`ExpansionData.MarkerIsolated`, read at a `double` slot: the vertex by which
the reduced core displays a loop looplessly is a genuine new bivalent point
of the requested core, and §2 says nothing about it. -/
theorem not_exists_fib_eq_marker (hCond : D.Conditions spec₀.core)
    {e : Fin Q} {j₁ j₂ : Fin p₀} (hk : D.kind e = SlotKind.double j₁ j₂) (v : Fin N) :
    D.fib v ≠ spec₀.core.head j₁ :=
  (ExpansionData.marker_of_conditions hCond e j₁ j₂ hk).1 v

/-- **and no other requested slot ends at it.** -/
theorem eq_of_head_eq_marker (hCond : D.Conditions spec₀.core)
    {e : Fin Q} {j₁ j₂ : Fin p₀} (hk : D.kind e = SlotKind.double j₁ j₂)
    {j : Fin p₀} (hj : spec₀.core.head j = spec₀.core.head j₁) : j = j₁ :=
  (ExpansionData.marker_of_conditions hCond e j₁ j₂ hk).2 j hj

/-- **The marker really is the joint of the two requested slots in series.** -/
theorem head_eq_tail_of_double (hCond : D.Conditions spec₀.core)
    {e : Fin Q} {j₁ j₂ : Fin p₀} (hk : D.kind e = SlotKind.double j₁ j₂) :
    spec₀.core.head j₁ = spec₀.core.tail j₂ :=
  ((ExpansionData.compatible_of_conditions hCond e).2.2 j₁ j₂ hk).2.1

/-- **A requested core vertex is a marker** when it is the middle point of a
`double` slot: the bivalent vertex by which the reduced core displays a loop
of the underlying metric graph looplessly. -/
def IsMarker (D : ExpansionData n₀ p₀ N Q) (C : ExplicitPotential.Core n₀ p₀)
    (w : Fin n₀) : Prop :=
  ∃ (e : Fin Q) (j₁ j₂ : Fin p₀), D.kind e = SlotKind.double j₁ j₂ ∧ C.head j₁ = w

/-- **The dichotomy: every requested core vertex is a marker or the image of a
model core vertex.**

`ExpansionData.Conditions` is enough.  Every requested core vertex is an end of
some requested slot `j` (clause 6); the slot's owner is not contracted
(`SlotClaimed`), so it is a `single` or a `double`, and `SlotCompatible` names
both of its endpoint fibres.  On a `single` both ends of `j` are images; on a
`double j₁ j₂` the outer ends `C.tail j₁` and `C.head j₂` are images while the
joint `C.head j₁ = C.tail j₂` is the marker.

With `not_isMarker_of_exists_fib` the two cases are mutually exclusive, so this
is a genuine partition of `Fin n₀` -- exactly what a retained core model's
vertex map needs in order to be defined by cases without a junk value. -/
theorem isMarker_or_exists_fib (hCond : D.Conditions spec₀.core) (w : Fin n₀) :
    IsMarker D spec₀.core w ∨ ∃ v : Fin N, D.fib v = w := by
  obtain ⟨j, hj⟩ := ExpansionData.incident_of_conditions hCond w
  obtain ⟨hne, hsingle, hdouble⟩ := ExpansionData.claimed_of_conditions hCond j
  obtain ⟨-, hcsingle, hcdouble⟩ :=
    ExpansionData.compatible_of_conditions hCond (D.owner j)
  cases hk : D.kind (D.owner j) with
  | contracted => exact absurd hk hne
  | single j' =>
      obtain ⟨-, rfl⟩ := hsingle j' hk
      obtain ⟨htail, hhead⟩ := hcsingle j' hk
      rcases hj with hj | hj
      · exact Or.inr ⟨D.bigCore.tail (D.owner j'), by rw [htail, hj]⟩
      · exact Or.inr ⟨D.bigCore.head (D.owner j'), by rw [hhead, hj]⟩
  | double j₁ j₂ =>
      obtain ⟨htail, hjoint, hhead⟩ := hcdouble j₁ j₂ hk
      rcases hdouble j₁ j₂ hk with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · rcases hj with hj | hj
        · exact Or.inr ⟨D.bigCore.tail (D.owner j₁), by rw [htail, hj]⟩
        · exact Or.inl ⟨D.owner j₁, j₁, j₂, hk, hj⟩
      · rcases hj with hj | hj
        · exact Or.inl ⟨D.owner j₂, j₁, j₂, hk, by rw [hjoint, hj]⟩
        · exact Or.inr ⟨D.bigCore.head (D.owner j₂), by rw [hhead, hj]⟩

/-- **and the two cases exclude one another.** -/
theorem not_isMarker_of_exists_fib (hCond : D.Conditions spec₀.core) {w : Fin n₀}
    (hw : ∃ v : Fin N, D.fib v = w) : ¬ IsMarker D spec₀.core w := by
  rintro ⟨e, j₁, j₂, hk, rfl⟩
  obtain ⟨v, hv⟩ := hw
  exact not_exists_fib_eq_marker hCond hk v hv

/-! ## 4.  Where the marker sits along its row -/

/-- **On a `single` slot the cut is at the end of the row**, so nothing is
cut: `RetainedCut.cutList` at the row total leaves every occurrence whole. -/
theorem cutOffsetAt_single (hCond : D.Conditions spec₀.core)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    {e : {x : Fin Q // x ∉ expansionForest D}} {j : Fin p₀}
    (hk : D.kind ↑e = SlotKind.single j) :
    cutOffsetAt face (RetainedIndexProducer.retainedIndex hCond hN hL) ↑e =
      face.scale * spec₀.length j := by
  rw [cutOffsetAt_coe, Retained.blockTotals,
    RetainedIndexProducer.retainedIndex_carried, hk]
  rfl

/-- **and on a `double` slot it is the marker's metric position**: the scaled
length of the first requested slot the retained cubic slot carries. -/
theorem cutOffsetAt_double (hCond : D.Conditions spec₀.core)
    (face : ClearedFace candidate strong.toPresentation coordinates)
    {e : {x : Fin Q // x ∉ expansionForest D}} {j₁ j₂ : Fin p₀}
    (hk : D.kind ↑e = SlotKind.double j₁ j₂) :
    cutOffsetAt face (RetainedIndexProducer.retainedIndex hCond hN hL) ↑e =
      face.scale * spec₀.length j₁ := by
  rw [cutOffsetAt_coe, Retained.blockTotals,
    RetainedIndexProducer.retainedIndex_carried, hk]
  rfl

/-! ## 5.  Non-vacuity

No structure is introduced.  `coreClass` and `requestedClass` are functions
into `DegSpec.Class`, and the datum they are computed on is the one the
reduction produces: `RetainedIndexProducer.bananaRetainedIndex` runs the producer at the
four-fold banana with a nonempty expansion forest, and
`RetainedIndexProducer.exists_conditions_not_markerFree` exhibits a datum with
a `double` slot, i.e. a genuine marker for §3 to be about. -/

theorem exists_conditions_with_marker :
    ∃ (D : ExpansionData 3 4 2 3), D.Conditions StableModelReduction.wedgeCore ∧
      ∃ (e : Fin 3) (j₁ j₂ : Fin 4), D.kind e = SlotKind.double j₁ j₂ :=
  RetainedRelabeling.exists_kind_double

end

end DraismaVargas.LocalCases.RetainedFibre
