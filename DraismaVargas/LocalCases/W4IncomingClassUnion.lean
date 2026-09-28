import DraismaVargas.LocalCases.W4IncomingPrunedFibre

/-!
# The literal non-dangling sheet union in an incoming W4 fibre

Source: Draisma--Vargas Part I, the non-dangling union lemma
(`lemma-class-union`), at a wall of Case {w4} (abbreviated W4). If both
endpoint blocks of a sheet were dangling, zero ramification and dangling-
no-glue would make both singleton. Their join class is then singleton too,
and no active vertex could lie in that fibre. Every sheet therefore belongs
to an active endpoint block. This is equality of sheet sets, not merely the
already checked connectedness of the pruned fibre.

**No wall hypothesis is needed here at all.**  Zero local ramification at an
inactive endpoint does not need the four-valent star: a source vertex all of
whose incident occurrences are dangling is unramified by
`StableLocalProperties.localRamification_eq_zero_of_forall_isDangling`, which
needs only the full-dimensional presentation.  Every statement of this module
is therefore available at a wall of any arity, in the `AnyWall` namespace, with
no extra hypothesis; the four-valent forms keep the star in their signatures
for their four-valent callers.  `W3Nd2IncomingSheetClasses` and
`W3Nd3IncomingCensus` consume the `AnyWall` forms directly at a trivalent wall.
-/

namespace DraismaVargas.LocalCases.W4IncomingClassUnion

open DraismaVargas.Infrastructure GraphContraction GluingContraction
open ContractionRamification ContractionFibre W4StableSource StableLocalProperties
open FullContractionFibre PrunedFibreValency PrunedFibreTree FullDimensionalSource

/-- A sheet singleton in both endpoint partitions is singleton in their join. -/
theorem eq_of_join_rel_of_singletons {d : ℕ} (left right : SheetPartition d)
    (sheet other : Fin d) (hLeft : left.block sheet = {sheet})
    (hRight : right.block sheet = {sheet})
    (hJoin : (SheetPartition.join left right).Rel sheet other) : sheet = other := by
  have hChain := (join_rel_iff_altChain left right sheet other).mp hJoin
  clear hJoin
  induction hChain with
  | refl => rfl
  | @tail previous last _ hStep ih =>
    subst previous
    rcases hStep with hLeftRel | hRightRel
    · have hMem := (left.mem_block_iff sheet last).mpr hLeftRel
      rw [hLeft, Finset.mem_singleton] at hMem
      exact hMem.symm
    · have hMem := (right.mem_block_iff sheet last).mpr hRightRel
      rw [hRight, Finset.mem_singleton] at hMem
      exact hMem.symm

section AnyWallUnion

variable {target : CFGraph} {degree : ℕ}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

/-- The endpoint of a sheet in the merged block belongs to that literal fibre. -/
theorem endpoint_mem_fibre (block : (mergedPartition data a b).Blocks)
    (place : target.V) (hPlace : place = a ∨ place = b) (sheet : Fin degree)
    (hSheet : sheet ∈ (mergedPartition data a b).block block.1) :
    data.sourceEndpoint place sheet ∈
      fibreVertices data hc hab hOne (mergedVertex data hc hab hOne block) := by
  apply (mem_fibreVertices_mergedVertex_iff data hc hab hOne block _).mpr
  refine ⟨hPlace, ?_⟩
  have hRel : (mergedPartition data a b).Rel block.1 sheet :=
    (SheetPartition.mem_block_iff _ _ _).mp hSheet
  have hRefines : (data.vertexPartition place).Refines (mergedPartition data a b) := by
    rcases hPlace with hAt | hAt
    · rw [hAt]
      exact vertexPartition_refines_mergedPartition data a b
    · rw [hAt]
      exact vertexPartition_refines_mergedPartition_right data a b
  have hRepr := hRel.trans (hRefines.rel ((data.vertexPartition place).rel_repr_right sheet))
  exact hRepr.symm.trans block.2

/-- Each literal source block in the fibre is contained in its merged block. -/
theorem block_subset_of_mem_fibre (block : (mergedPartition data a b).Blocks)
    (point : data.SourceVertex)
    (hPoint : point ∈ fibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)) :
    (data.vertexPartition point.1.1).block point.1.2 ⊆
      (mergedPartition data a b).block block.1 := by
  have hFibre := (mem_fibreVertices_mergedVertex_iff data hc hab hOne block point).mp hPoint
  have hRefines : (data.vertexPartition point.1.1).Refines (mergedPartition data a b) := by
    rcases hFibre.1 with hAt | hAt
    · rw [hAt]
      exact vertexPartition_refines_mergedPartition data a b
    · rw [hAt]
      exact vertexPartition_refines_mergedPartition_right data a b
  intro sheet hSheet
  apply (SheetPartition.mem_block_iff _ _ _).mpr
  exact (block.2.trans hFibre.2.symm).trans
    (hRefines.rel ((SheetPartition.mem_block_iff _ _ _).mp hSheet))

namespace AnyWall

include fd hc hab hOne

omit hc hab hOne in
/-- An inactive endpoint block is literally a singleton sheet set.

No wall hypothesis of any kind enters: a source vertex all of whose incident
occurrences are dangling is unramified by `lemma-dangling-rphi`
(`StableLocalProperties.localRamification_eq_zero_of_forall_isDangling`), which
needs only the full-dimensional presentation.  (At a four-valent wall the same
vanishing can also be read off the endpoint's target change.) -/
theorem inactive_endpoint_block (place : target.V) (sheet : Fin degree)
    (hZero : nonDanglingValency data (data.sourceEndpoint place sheet) = 0) :
    (data.vertexPartition place).block sheet = {sheet} := by
  classical
  have hDangling : ∀ edge : IncidentSourceEdge data (data.sourceEndpoint place sheet),
      IsDangling data edge.1 := by
    intro edge
    by_contra hSurvives
    have hCard := card_filter_not_isDangling_eq_nonDanglingValency data
      (data.sourceEndpoint place sheet)
    rw [hZero, Finset.card_eq_zero] at hCard
    have hMem : edge ∈ (Finset.univ : Finset (IncidentSourceEdge data
        (data.sourceEndpoint place sheet))).filter (fun e ↦ ¬ IsDangling data e.1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSurvives⟩
    rw [hCard] at hMem
    exact absurd hMem (Finset.notMem_empty _)
  have hRam := localRamification_eq_zero_of_forall_isDangling data fd.valid
    fd.changeMinimal fd.labelling fd.det_ne_zero _ hDangling
  have hCard := NonDanglingValency.blockCard_eq_one_of_nonDanglingValency_eq_zero
    data fd.danglingEdgeNoGlue (data.sourceEndpoint place sheet) hRam hZero
  have hCard' : (data.vertexPartition place).blockCard sheet = 1 :=
    (congrArg Finset.card ((data.vertexPartition place).block_eq_of_rel
      ((data.vertexPartition place).rel_repr_right sheet))).trans hCard
  exact (data.vertexPartition place).block_eq_singleton_of_blockCard_eq_one sheet hCard'

/-- Every sheet in a nonempty active fibre has an active endpoint.
The active vertex is not supplied for that sheet; it is deduced from the join. -/
theorem endpoint_active (block : (mergedPartition data a b).Blocks)
    (hNonempty : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)).Nonempty)
    (sheet : Fin degree) (hSheet : sheet ∈ (mergedPartition data a b).block block.1) :
    nonDanglingValency data (data.sourceEndpoint a sheet) ≠ 0 ∨
      nonDanglingValency data (data.sourceEndpoint b sheet) ≠ 0 := by
  by_contra hBoth
  push Not at hBoth
  have hLeft := inactive_endpoint_block data fd a sheet hBoth.1
  have hRight := inactive_endpoint_block data fd b sheet hBoth.2
  obtain ⟨point, hPoint⟩ := hNonempty
  obtain ⟨hMap, hActive⟩ := (mem_activeFibreVertices data hc hab hOne _ point).mp hPoint
  have hFibre := (mem_fibreVertices_mergedVertex_iff data hc hab hOne block point).mp
    ((mem_fibreVertices data hc hab hOne _ point).mpr hMap)
  have hPointRel : (mergedPartition data a b).Rel block.1 point.1.2 :=
    block.2.trans hFibre.2.symm
  have hSheetRel := (SheetPartition.mem_block_iff _ _ _).mp hSheet
  have hEqual := eq_of_join_rel_of_singletons (data.vertexPartition a)
    (data.vertexPartition b) sheet point.1.2 hLeft hRight (hSheetRel.symm.trans hPointRel)
  have hSelf := data.sourceEndpoint_self point
  rcases hFibre.1 with hAt | hAt
  · rw [hAt, ← hEqual] at hSelf
    exact hActive (hSelf ▸ hBoth.1)
  · rw [hAt, ← hEqual] at hSelf
    exact hActive (hSelf ▸ hBoth.2)

/-- Source non-dangling union: equality of the actual finite sheet sets. -/
theorem block_eq_active_union (block : (mergedPartition data a b).Blocks)
    (hNonempty : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)).Nonempty) :
    (mergedPartition data a b).block block.1 =
      (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)).biUnion
        (fun point ↦ (data.vertexPartition point.1.1).block point.1.2) := by
  classical
  ext sheet
  constructor
  · intro hSheet
    have hActive := endpoint_active data fd hc hab hOne block hNonempty sheet hSheet
    rcases hActive with hLeft | hRight
    · refine Finset.mem_biUnion.mpr ⟨data.sourceEndpoint a sheet, ?_, ?_⟩
      · apply (mem_activeFibreVertices data hc hab hOne _ _).mpr
        exact ⟨(mem_fibreVertices data hc hab hOne _ _).mp
          (endpoint_mem_fibre data hc hab hOne block a (Or.inl rfl) sheet hSheet), hLeft⟩
      · exact (SheetPartition.mem_block_iff _ _ _).mpr
          ((data.vertexPartition a).rel_repr_left sheet)
    · refine Finset.mem_biUnion.mpr ⟨data.sourceEndpoint b sheet, ?_, ?_⟩
      · apply (mem_activeFibreVertices data hc hab hOne _ _).mpr
        exact ⟨(mem_fibreVertices data hc hab hOne _ _).mp
          (endpoint_mem_fibre data hc hab hOne block b (Or.inr rfl) sheet hSheet), hRight⟩
      · exact (SheetPartition.mem_block_iff _ _ _).mpr
          ((data.vertexPartition b).rel_repr_left sheet)
  · intro hSheet
    obtain ⟨point, hPoint, hSheet⟩ := Finset.mem_biUnion.mp hSheet
    exact block_subset_of_mem_fibre data hc hab hOne block point
      ((mem_fibreVertices data hc hab hOne _ _).mpr
        ((mem_activeFibreVertices data hc hab hOne _ point).mp hPoint).1) hSheet

/-- The wall's nonzero surviving valency supplies the nonempty active fibre. -/
theorem block_eq_active_union_of_nonzero
    (hCompat : WallDegeneration.DanglingCompatible data hc hab hOne)
    (block : (mergedPartition data a b).Blocks)
    (hNonzero : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) ≠ 0) :
    (mergedPartition data a b).block block.1 =
      (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)).biUnion
        (fun point ↦ (data.vertexPartition point.1.1).block point.1.2) :=
  block_eq_active_union data fd hc hab hOne block
    (activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero data hc hab hOne
      hCompat _ hNonzero)

/-- The singleton alternative of the actual census identifies the whole
merged sheet class with its single surviving endpoint class. -/
theorem block_eq_of_active_singleton (block : (mergedPartition data a b).Blocks)
    (point : data.SourceVertex)
    (hActive : activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block) = {point}) :
    (mergedPartition data a b).block block.1 =
      (data.vertexPartition point.1.1).block point.1.2 := by
  classical
  have hNonempty : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)).Nonempty := by
    rw [hActive]
    exact Finset.singleton_nonempty point
  simpa only [hActive, Finset.singleton_biUnion] using
    block_eq_active_union data fd hc hab hOne block hNonempty

/-- The one-edge alternative identifies the merged sheet class with the
union of its two actual endpoint classes, allowing their inclusion relation
to be consumed by the r0-nd2 block equality. -/
theorem block_eq_union_of_active_pair (block : (mergedPartition data a b).Blocks)
    (first second : data.SourceVertex)
    (hActive : activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block) = {first, second}) :
    (mergedPartition data a b).block block.1 =
      (data.vertexPartition first.1.1).block first.1.2 ∪
        (data.vertexPartition second.1.1).block second.1.2 := by
  classical
  have hNonempty : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)).Nonempty := by
    rw [hActive]
    exact Finset.insert_nonempty first _
  simpa only [hActive, Finset.biUnion_insert, Finset.singleton_biUnion] using
    block_eq_active_union data fd hc hab hOne block hNonempty

end AnyWall

end AnyWallUnion

section Incoming

variable {target : CFGraph} {degree : ℕ}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)

include fd hc hab hOne star

/-- An inactive endpoint block is literally a singleton sheet set.

This is the four-valent reading of `AnyWall.inactive_endpoint_block`: the wall
supplies the vanishing local ramification through the endpoint's target change.
The `AnyWall` form needs no wall hypothesis at all; this form serves the
four-valent callers that pass the star. -/
theorem inactive_endpoint_block (place : target.V) (hPlace : place = a ∨ place = b)
    (sheet : Fin degree)
    (hZero : nonDanglingValency data (data.sourceEndpoint place sheet) = 0) :
    (data.vertexPartition place).block sheet = {sheet} := by
  have hCard := NonDanglingValency.blockCard_eq_one_of_nonDanglingValency_eq_zero
    data fd.danglingEdgeNoGlue (data.sourceEndpoint place sheet)
    (W4IncomingCensus.localRamification_eq_zero_at_endpoint data fd hc hab hOne star
      (data.sourceEndpoint place sheet) hPlace) hZero
  have hCard' : (data.vertexPartition place).blockCard sheet = 1 :=
    (congrArg Finset.card ((data.vertexPartition place).block_eq_of_rel
      ((data.vertexPartition place).rel_repr_right sheet))).trans hCard
  exact (data.vertexPartition place).block_eq_singleton_of_blockCard_eq_one sheet hCard'

end Incoming

section IncomingStarForms

variable {target : CFGraph} {degree : ℕ}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

include fd hc hab hOne

/-- The four-valent form of `AnyWall.endpoint_active`.  The star is kept in
the signature for the four-valent callers only; the statement does not need
it. -/
theorem endpoint_active
    (_star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)
    (block : (mergedPartition data a b).Blocks)
    (hNonempty : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)).Nonempty)
    (sheet : Fin degree) (hSheet : sheet ∈ (mergedPartition data a b).block block.1) :
    nonDanglingValency data (data.sourceEndpoint a sheet) ≠ 0 ∨
      nonDanglingValency data (data.sourceEndpoint b sheet) ≠ 0 :=
  AnyWall.endpoint_active data fd hc hab hOne block hNonempty sheet hSheet

/-- The four-valent form of `AnyWall.block_eq_active_union`. -/
theorem block_eq_active_union
    (_star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)
    (block : (mergedPartition data a b).Blocks)
    (hNonempty : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)).Nonempty) :
    (mergedPartition data a b).block block.1 =
      (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)).biUnion
        (fun point ↦ (data.vertexPartition point.1.1).block point.1.2) :=
  AnyWall.block_eq_active_union data fd hc hab hOne block hNonempty

/-- The four-valent form of `AnyWall.block_eq_active_union_of_nonzero`. -/
theorem block_eq_active_union_of_nonzero
    (_star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)
    (hCompat : WallDegeneration.DanglingCompatible data hc hab hOne)
    (block : (mergedPartition data a b).Blocks)
    (hNonzero : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) ≠ 0) :
    (mergedPartition data a b).block block.1 =
      (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)).biUnion
        (fun point ↦ (data.vertexPartition point.1.1).block point.1.2) :=
  AnyWall.block_eq_active_union_of_nonzero data fd hc hab hOne hCompat block hNonzero

/-- The four-valent form of `AnyWall.block_eq_of_active_singleton`. -/
theorem block_eq_of_active_singleton
    (_star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)
    (block : (mergedPartition data a b).Blocks)
    (point : data.SourceVertex)
    (hActive : activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block) = {point}) :
    (mergedPartition data a b).block block.1 =
      (data.vertexPartition point.1.1).block point.1.2 :=
  AnyWall.block_eq_of_active_singleton data fd hc hab hOne block point hActive

/-- The four-valent form of `AnyWall.block_eq_union_of_active_pair`. -/
theorem block_eq_union_of_active_pair
    (_star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)
    (block : (mergedPartition data a b).Blocks)
    (first second : data.SourceVertex)
    (hActive : activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block) = {first, second}) :
    (mergedPartition data a b).block block.1 =
      (data.vertexPartition first.1.1).block first.1.2 ∪
        (data.vertexPartition second.1.1).block second.1.2 :=
  AnyWall.block_eq_union_of_active_pair data fd hc hab hOne block first second hActive

end IncomingStarForms

end DraismaVargas.LocalCases.W4IncomingClassUnion
