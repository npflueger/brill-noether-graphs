module

public import DraismaVargas.LocalCases.W4IncomingClassUnion
public import DraismaVargas.LocalCases.W4IncomingSideCensus

@[expose] public section

/-!
# Incoming W4 endpoint relations from the literal active fibre

At either old target endpoint there is at most one active block in a fixed
merged fibre. All remaining endpoint blocks are singleton by local r0 and
dangling-no-glue. Thus the active block determines the entire endpoint
partition relation on that merged block, including its inactive sheets.
These are exact relation identities to consume after the actual side census,
not assumed whole-cover matching or choices of stored representatives.

**Wall arity.**  `AnyWall.eq_of_rel_of_inactive` and
`AnyWall.endpoint_rel_iff_eq_of_no_active` need no wall hypothesis at all --
they rest only on `W4IncomingClassUnion.AnyWall.inactive_endpoint_block` -- so
they hold at a wall of any arity.  `AnyWall.endpoint_rel_iff_of_active` needs
zero target change at both original endpoints, through the pruned-fibre census.
The four-valent forms keep the names the four-valent callers use.
-/

namespace DraismaVargas.LocalCases.W4IncomingBlockRelations

open DraismaVargas.Infrastructure GraphContraction GluingContraction
open ContractionRamification W4StableSource StableLocalProperties
open FullContractionFibre PrunedFibreValency PrunedFibreTree FullDimensionalSource
open W4IncomingClassUnion W4IncomingSideCensus

variable {target : CFGraph} {degree : ℕ}

section AnyWallRelations

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (hChangeZero : ∀ place : target.V, place = a ∨ place = b → data.targetChange place = 0)

namespace AnyWall

include fd hc hab hOne hChangeZero

omit hc hab hOne hChangeZero in
/-- An inactive endpoint cannot identify two distinct sheets.  No wall
hypothesis enters: the singleton class comes from
`W4IncomingClassUnion.AnyWall.inactive_endpoint_block`. -/
theorem eq_of_rel_of_inactive (place : target.V)
    (first second : Fin degree)
    (hInactive : nonDanglingValency data (data.sourceEndpoint place first) = 0)
    (hRel : (data.vertexPartition place).Rel first second) : first = second := by
  have hMem := (SheetPartition.mem_block_iff _ _ _).mpr hRel
  rw [W4IncomingClassUnion.AnyWall.inactive_endpoint_block data fd place first hInactive,
    Finset.mem_singleton] at hMem
  exact hMem.symm

omit hChangeZero in
/-- A side with no active endpoint has the discrete relation on the whole
merged block, not merely on its surviving flags. -/
theorem endpoint_rel_iff_eq_of_no_active (block : (mergedPartition data a b).Blocks)
    (place : target.V) (hPlace : place = a ∨ place = b)
    (hNone : ∀ point ∈ activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block), point.1.1 ≠ place)
    (first second : Fin degree)
    (hFirst : first ∈ (mergedPartition data a b).block block.1) :
    (data.vertexPartition place).Rel first second ↔ first = second := by
  constructor
  · intro hRel
    apply eq_of_rel_of_inactive data fd place first second _ hRel
    by_contra hActive
    have hMem := (mem_activeFibreVertices data hc hab hOne _ _).mpr
      ⟨(mem_fibreVertices data hc hab hOne _ _).mp
        (endpoint_mem_fibre data hc hab hOne block place hPlace first hFirst), hActive⟩
    exact hNone (data.sourceEndpoint place first) hMem rfl
  · rintro rfl
    rfl

/-- When a side has an actual active endpoint, its whole restricted relation
is the single active sheet block plus singleton classes elsewhere. The
uniqueness of that active endpoint is derived from the pruned-fibre census. -/
theorem endpoint_rel_iff_of_active (block : (mergedPartition data a b).Blocks)
    (place : target.V) (hPlace : place = a ∨ place = b)
    (point : data.SourceVertex)
    (hPoint : point ∈ activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block))
    (hTarget : point.1.1 = place)
    (first second : Fin degree)
    (hFirst : first ∈ (mergedPartition data a b).block block.1) :
    (data.vertexPartition place).Rel first second ↔
      first = second ∨ ((data.vertexPartition place).Rel point.1.2 first ∧
        (data.vertexPartition place).Rel point.1.2 second) := by
  constructor
  · intro hRel
    by_cases hZero : nonDanglingValency data (data.sourceEndpoint place first) = 0
    · exact Or.inl (eq_of_rel_of_inactive data fd place first second hZero hRel)
    · have hActive := (mem_activeFibreVertices data hc hab hOne _ _).mpr
        ⟨(mem_fibreVertices data hc hab hOne _ _).mp
          (endpoint_mem_fibre data hc hab hOne block place hPlace first hFirst), hZero⟩
      have hEqual := W4IncomingSideCensus.AnyWall.eq_of_same_side data fd hc hab hOne hChangeZero
        (mergedVertex data hc hab hOne block) (data.sourceEndpoint place first)
        point hActive hPoint hTarget.symm
      have hFirstRel := ((data.sourceEndpoint_eq_iff place first point).mp hEqual).2.symm
      exact Or.inr ⟨hFirstRel, hFirstRel.trans hRel⟩
  · rintro (rfl | ⟨hFirstRel, hSecondRel⟩)
    · rfl
    · exact hFirstRel.symm.trans hSecondRel

end AnyWall

end AnyWallRelations

section IncomingStarForms

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

include fd hc hab hOne

/-- The four-valent form of `AnyWall.endpoint_rel_iff_eq_of_no_active`.  The
star appears in the signature for the four-valent callers only; the statement
does not use it. -/
theorem endpoint_rel_iff_eq_of_no_active
    (_star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)
    (block : (mergedPartition data a b).Blocks)
    (place : target.V) (hPlace : place = a ∨ place = b)
    (hNone : ∀ point ∈ activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block), point.1.1 ≠ place)
    (first second : Fin degree)
    (hFirst : first ∈ (mergedPartition data a b).block block.1) :
    (data.vertexPartition place).Rel first second ↔ first = second :=
  AnyWall.endpoint_rel_iff_eq_of_no_active data fd hc hab hOne block place hPlace hNone
    first second hFirst

end IncomingStarForms

section Incoming

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)

include fd hc hab hOne star

/-- An inactive endpoint cannot identify two distinct sheets.  This is the
four-valent reading of `AnyWall.eq_of_rel_of_inactive`, which needs no wall
hypothesis at all. -/
theorem eq_of_rel_of_inactive (place : target.V) (hPlace : place = a ∨ place = b)
    (first second : Fin degree)
    (hInactive : nonDanglingValency data (data.sourceEndpoint place first) = 0)
    (hRel : (data.vertexPartition place).Rel first second) : first = second := by
  have hMem := (SheetPartition.mem_block_iff _ _ _).mpr hRel
  rw [inactive_endpoint_block data fd hc hab hOne star place hPlace first hInactive,
    Finset.mem_singleton] at hMem
  exact hMem.symm

/-- The four-valent form of `AnyWall.endpoint_rel_iff_of_active`. -/
theorem endpoint_rel_iff_of_active (block : (mergedPartition data a b).Blocks)
    (place : target.V) (hPlace : place = a ∨ place = b)
    (point : data.SourceVertex)
    (hPoint : point ∈ activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block))
    (hTarget : point.1.1 = place)
    (first second : Fin degree)
    (hFirst : first ∈ (mergedPartition data a b).block block.1) :
    (data.vertexPartition place).Rel first second ↔
      first = second ∨ ((data.vertexPartition place).Rel point.1.2 first ∧
        (data.vertexPartition place).Rel point.1.2 second) :=
  AnyWall.endpoint_rel_iff_of_active data fd hc hab hOne
    (W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star)
    block place hPlace point hPoint hTarget first second hFirst

end Incoming

end DraismaVargas.LocalCases.W4IncomingBlockRelations
