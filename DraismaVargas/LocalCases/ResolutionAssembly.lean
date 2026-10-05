module

public import DraismaVargas.LocalCases.ResolutionM11

@[expose] public section

/-!
# Assembling local resolutions across wall blocks

Draisma--Vargas chooses a local continuation independently on every sheet
block above a wall vertex. This file pastes those choices into one pair of
endpoint partitions and one new-edge partition. The central theorem proves
that blockwise joins remain a global join, so contraction of the assembled
new edge recovers the original wall partition.
-/

namespace DraismaVargas.LocalCases.ResolutionM11.LocalResolution

open DraismaVargas.Infrastructure

variable {d : ℕ}

/-- Endpoint partition obtained by pasting the left endpoint chosen on every
wall block. -/
def pasteLeft (wall : SheetPartition d) (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall) :
    SheetPartition d :=
  wall.paste (fun anchor ↦ (resolution anchor).left)
    (fun anchor ↦ (hContracts anchor).left_refines)

/-- Endpoint partition obtained by pasting the right endpoint chosen on every
wall block. -/
def pasteRight (wall : SheetPartition d) (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall) :
    SheetPartition d :=
  wall.paste (fun anchor ↦ (resolution anchor).right)
    (fun anchor ↦ (hContracts anchor).right_refines)

/-- New-edge partition obtained by pasting the new-edge choice on every wall
block. -/
def pasteNewEdge (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall) :
    SheetPartition d :=
  wall.paste (fun anchor ↦ (resolution anchor).newEdge)
    (fun anchor ↦ (resolution anchor).edge_refines_left.trans
      (hContracts anchor).left_refines)

theorem pasteLeft_refines (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall) :
    (pasteLeft wall resolution hContracts).Refines wall :=
  wall.paste_refines _ _

theorem pasteRight_refines (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall) :
    (pasteRight wall resolution hContracts).Refines wall :=
  wall.paste_refines _ _

theorem pasteNewEdge_refines_left (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall) :
    (pasteNewEdge wall resolution hContracts).Refines
      (pasteLeft wall resolution hContracts) := by
  intro first second hNew
  apply (wall.paste_rel_iff (fun anchor ↦ (resolution anchor).left)
    (fun anchor ↦ (hContracts anchor).left_refines) first second).mpr
  have hLocal := (wall.paste_rel_iff
    (fun anchor ↦ (resolution anchor).newEdge)
    (fun anchor ↦ (resolution anchor).edge_refines_left.trans
      (hContracts anchor).left_refines) first second).mp hNew
  exact (resolution (wall.repr first)).edge_refines_left.rel hLocal

theorem pasteNewEdge_refines_right (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall) :
    (pasteNewEdge wall resolution hContracts).Refines
      (pasteRight wall resolution hContracts) := by
  intro first second hNew
  apply (wall.paste_rel_iff (fun anchor ↦ (resolution anchor).right)
    (fun anchor ↦ (hContracts anchor).right_refines) first second).mpr
  have hLocal := (wall.paste_rel_iff
    (fun anchor ↦ (resolution anchor).newEdge)
    (fun anchor ↦ (resolution anchor).edge_refines_left.trans
      (hContracts anchor).left_refines) first second).mp hNew
  exact (resolution (wall.repr first)).edge_refines_right.rel hLocal

/-- Assemble independently selected block resolutions into one local
resolution on the complete sheet set. -/
def paste (wall : SheetPartition d) (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall) :
    LocalResolution d where
  left := pasteLeft wall resolution hContracts
  right := pasteRight wall resolution hContracts
  newEdge := pasteNewEdge wall resolution hContracts
  edge_refines_left := pasteNewEdge_refines_left wall resolution hContracts
  edge_refines_right := pasteNewEdge_refines_right wall resolution hContracts

/-- The blocks of the pasted left endpoint partition inside a wall block are
counted by the resolution chosen on that block.  This is the first of three
general statements about `LocalResolution.paste` used by the non-star local
resolution of Position II.b in `W3ShiftSourceCandidates`. -/
theorem pasteLeft_blockCountWithin (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (sheet : Fin d) :
    (paste wall resolution hContracts).left.blockCountWithin wall sheet =
      (resolution (wall.repr sheet)).left.blockCountWithin wall sheet := by
  classical
  unfold SheetPartition.blockCountWithin
  congr 1
  apply Finset.image_congr
  intro source hSource
  have hRel : wall.repr source = wall.repr sheet :=
    (((wall.mem_block_iff sheet source).mp hSource)).symm
  change (wall.paste (fun anchor ↦ (resolution anchor).left)
    (fun anchor ↦ (hContracts anchor).left_refines)).repr source = _
  rw [SheetPartition.paste_repr, hRel]

theorem pasteRight_blockCountWithin (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (sheet : Fin d) :
    (paste wall resolution hContracts).right.blockCountWithin wall sheet =
      (resolution (wall.repr sheet)).right.blockCountWithin wall sheet := by
  classical
  unfold SheetPartition.blockCountWithin
  congr 1
  apply Finset.image_congr
  intro source hSource
  have hRel : wall.repr source = wall.repr sheet :=
    (((wall.mem_block_iff sheet source).mp hSource)).symm
  change (wall.paste (fun anchor ↦ (resolution anchor).right)
    (fun anchor ↦ (hContracts anchor).right_refines)).repr source = _
  rw [SheetPartition.paste_repr, hRel]

theorem pasteNewEdge_blockCountWithin (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (sheet : Fin d) :
    (paste wall resolution hContracts).newEdge.blockCountWithin wall sheet =
      (resolution (wall.repr sheet)).newEdge.blockCountWithin wall sheet := by
  classical
  unfold SheetPartition.blockCountWithin
  congr 1
  apply Finset.image_congr
  intro source hSource
  have hRel : wall.repr source = wall.repr sheet :=
    (((wall.mem_block_iff sheet source).mp hSource)).symm
  change (wall.paste (fun anchor ↦ (resolution anchor).newEdge)
    (fun anchor ↦ ((resolution anchor).edge_refines_left.trans
      (hContracts anchor).left_refines))).repr source = _
  rw [SheetPartition.paste_repr, hRel]

/-- **The block level of the pasted trio.**  A block of an assembled endpoint
or new-edge partition is the corresponding block of the resolution chosen on
the wall block of that sheet.

These three sit one level below `pasteLeft_blockCountWithin` and one level
above `paste_left_blockCard`; without them every consumer has to reopen
`paste` by hand with `change`/`unfold`/`SheetPartition.paste_block`. -/
theorem pasteLeft_block (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (sheet : Fin d) :
    (paste wall resolution hContracts).left.block sheet =
      (resolution (wall.repr sheet)).left.block sheet := by
  change (pasteLeft wall resolution hContracts).block sheet = _
  unfold pasteLeft
  exact wall.paste_block _ _ sheet

theorem pasteRight_block (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (sheet : Fin d) :
    (paste wall resolution hContracts).right.block sheet =
      (resolution (wall.repr sheet)).right.block sheet := by
  change (pasteRight wall resolution hContracts).block sheet = _
  unfold pasteRight
  exact wall.paste_block _ _ sheet

theorem pasteNewEdge_block (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (sheet : Fin d) :
    (paste wall resolution hContracts).newEdge.block sheet =
      (resolution (wall.repr sheet)).newEdge.block sheet := by
  change (pasteNewEdge wall resolution hContracts).block sheet = _
  unfold pasteNewEdge
  exact wall.paste_block _ _ sheet

theorem paste_left_blockCard (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (sheet : Fin d) :
    (paste wall resolution hContracts).left.blockCard sheet =
      (resolution (wall.repr sheet)).left.blockCard sheet := by
  change (pasteLeft wall resolution hContracts).blockCard sheet = _
  unfold pasteLeft
  exact wall.paste_blockCard _ _ sheet

theorem paste_right_blockCard (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (sheet : Fin d) :
    (paste wall resolution hContracts).right.blockCard sheet =
      (resolution (wall.repr sheet)).right.blockCard sheet := by
  change (pasteRight wall resolution hContracts).blockCard sheet = _
  unfold pasteRight
  exact wall.paste_blockCard _ _ sheet

theorem paste_newEdge_blockCard (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (sheet : Fin d) :
    (paste wall resolution hContracts).newEdge.blockCard sheet =
      (resolution (wall.repr sheet)).newEdge.blockCard sheet := by
  change (pasteNewEdge wall resolution hContracts).blockCard sheet = _
  unfold pasteNewEdge
  exact wall.paste_blockCard _ _ sheet

theorem paste_newEdge_blockCountWithin_left (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (sheet : Fin d) :
    (paste wall resolution hContracts).newEdge.blockCountWithin
        (paste wall resolution hContracts).left sheet =
      (resolution (wall.repr sheet)).newEdge.blockCountWithin
        (resolution (wall.repr sheet)).left sheet := by
  change (pasteNewEdge wall resolution hContracts).blockCountWithin
      (pasteLeft wall resolution hContracts) sheet = _
  unfold pasteNewEdge pasteLeft
  exact wall.paste_blockCountWithin _ _ _ _ sheet

theorem paste_newEdge_blockCountWithin_right (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (sheet : Fin d) :
    (paste wall resolution hContracts).newEdge.blockCountWithin
        (paste wall resolution hContracts).right sheet =
      (resolution (wall.repr sheet)).newEdge.blockCountWithin
        (resolution (wall.repr sheet)).right sheet := by
  change (pasteNewEdge wall resolution hContracts).blockCountWithin
      (pasteRight wall resolution hContracts) sheet = _
  unfold pasteNewEdge pasteRight
  exact wall.paste_blockCountWithin _ _ _ _ sheet

theorem blockCountWithin_paste_left (wall fine : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (sheet : Fin d) :
    fine.blockCountWithin (paste wall resolution hContracts).left sheet =
      fine.blockCountWithin (resolution (wall.repr sheet)).left sheet := by
  change fine.blockCountWithin (pasteLeft wall resolution hContracts) sheet = _
  unfold pasteLeft
  exact wall.blockCountWithin_paste fine _ _ sheet

theorem blockCountWithin_paste_right (wall fine : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (sheet : Fin d) :
    fine.blockCountWithin (paste wall resolution hContracts).right sheet =
      fine.blockCountWithin (resolution (wall.repr sheet)).right sheet := by
  change fine.blockCountWithin (pasteRight wall resolution hContracts) sheet = _
  unfold pasteRight
  exact wall.blockCountWithin_paste fine _ _ sheet

private theorem sum_blockCountWithin_paste_left (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (incident : List (SheetPartition d)) (sheet : Fin d) :
    (incident.map (fun edge ↦
      (edge.blockCountWithin (paste wall resolution hContracts).left sheet :
        ℤ))).sum =
      (incident.map (fun edge ↦
        (edge.blockCountWithin (resolution (wall.repr sheet)).left sheet :
          ℤ))).sum := by
  induction incident with
  | nil => rfl
  | cons edge incident ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [blockCountWithin_paste_left, ih]

private theorem sum_blockCountWithin_paste_right (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (incident : List (SheetPartition d)) (sheet : Fin d) :
    (incident.map (fun edge ↦
      (edge.blockCountWithin (paste wall resolution hContracts).right sheet :
        ℤ))).sum =
      (incident.map (fun edge ↦
        (edge.blockCountWithin (resolution (wall.repr sheet)).right sheet :
          ℤ))).sum := by
  induction incident with
  | nil => rfl
  | cons edge incident ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [blockCountWithin_paste_right, ih]

/-- Block-restricted left-endpoint receipts for every canonical wall class
assemble to the full left-endpoint Riemann--Hurwitz condition. -/
theorem paste_left_riemannHurwitzAt (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (external : List (SheetPartition d))
    (hLocal : ∀ anchor, wall.repr anchor = anchor →
      RiemannHurwitzAtBlock wall (resolution anchor).left
        ((resolution anchor).newEdge :: external) anchor) :
    SheetPartition.RiemannHurwitzAt (paste wall resolution hContracts).left
      ((paste wall resolution hContracts).newEdge :: external) := by
  apply (riemannHurwitzAt_iff_forall_wallBlock wall
    (paste wall resolution hContracts).left
    ((paste wall resolution hContracts).newEdge :: external)).mpr
  intro anchor hAnchor sheet hSheet
  have hSelected : wall.repr sheet = anchor := by
    unfold SheetPartition.Rel at hSheet
    exact hSheet.symm.trans hAnchor
  have hReceipt := hLocal anchor hAnchor sheet hSheet
  simp only [List.map_cons, List.sum_cons, List.length_cons] at hReceipt ⊢
  rw [paste_newEdge_blockCountWithin_left,
    sum_blockCountWithin_paste_left, paste_left_blockCard, hSelected]
  exact hReceipt

/-- Block-restricted right-endpoint receipts for every canonical wall class
assemble to the full right-endpoint Riemann--Hurwitz condition. -/
theorem paste_right_riemannHurwitzAt (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (external : List (SheetPartition d))
    (hLocal : ∀ anchor, wall.repr anchor = anchor →
      RiemannHurwitzAtBlock wall (resolution anchor).right
        ((resolution anchor).newEdge :: external) anchor) :
    SheetPartition.RiemannHurwitzAt (paste wall resolution hContracts).right
      ((paste wall resolution hContracts).newEdge :: external) := by
  apply (riemannHurwitzAt_iff_forall_wallBlock wall
    (paste wall resolution hContracts).right
    ((paste wall resolution hContracts).newEdge :: external)).mpr
  intro anchor hAnchor sheet hSheet
  have hSelected : wall.repr sheet = anchor := by
    unfold SheetPartition.Rel at hSheet
    exact hSheet.symm.trans hAnchor
  have hReceipt := hLocal anchor hAnchor sheet hSheet
  simp only [List.map_cons, List.sum_cons, List.length_cons] at hReceipt ⊢
  rw [paste_newEdge_blockCountWithin_right,
    sum_blockCountWithin_paste_right, paste_right_blockCard, hSelected]
  exact hReceipt

private theorem lift_eqvGen_to_pasted
    (wall : SheetPartition d) (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (anchor : Fin d) {first second : Fin d}
    (hFirst : wall.repr first = anchor)
    (hGenerated : Relation.EqvGen
      (fun a b ↦ (resolution anchor).left.Rel a b ∨
        (resolution anchor).right.Rel a b) first second) :
    Relation.EqvGen
      (fun a b ↦ (pasteLeft wall resolution hContracts).Rel a b ∨
        (pasteRight wall resolution hContracts).Rel a b) first second := by
  induction hGenerated with
  | rel first second hRelation =>
      apply Relation.EqvGen.rel
      rcases hRelation with hLeft | hRight
      · left
        apply (wall.paste_rel_iff (fun block ↦ (resolution block).left)
          (fun block ↦ (hContracts block).left_refines) first second).mpr
        simpa [hFirst] using hLeft
      · right
        apply (wall.paste_rel_iff (fun block ↦ (resolution block).right)
          (fun block ↦ (hContracts block).right_refines) first second).mpr
        simpa [hFirst] using hRight
  | refl => exact Relation.EqvGen.refl _
  | symm first second hRelation ih =>
      apply Relation.EqvGen.symm
      apply ih
      have hWall : wall.Rel first second :=
        (hContracts anchor first second).mpr hRelation
      unfold SheetPartition.Rel at hWall
      exact hWall.trans hFirst
  | trans first middle second hFirstMiddle hMiddleSecond ihFirst ihSecond =>
      apply Relation.EqvGen.trans first middle second
      · exact ihFirst hFirst
      · apply ihSecond
        have hWall : wall.Rel first middle :=
          (hContracts anchor first middle).mpr hFirstMiddle
        unfold SheetPartition.Rel at hWall
        exact hWall.symm.trans hFirst

/-- Pasting blockwise resolutions that all contract to `wall` again contracts
to `wall`. The proof follows each generated local path inside its wall block;
no enumeration of sheets or blocks is used. -/
theorem paste_contracts (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall) :
    (paste wall resolution hContracts).ContractsTo wall := by
  intro first second
  constructor
  · intro hWall
    apply lift_eqvGen_to_pasted wall resolution hContracts (wall.repr first) rfl
    exact (hContracts (wall.repr first) first second).mp hWall
  · intro hGenerated
    induction hGenerated with
    | rel first second hRelation =>
        exact hRelation.elim
          (pasteLeft_refines wall resolution hContracts).rel
          (pasteRight_refines wall resolution hContracts).rel
    | refl => rfl
    | symm => apply Eq.symm; assumption
    | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- Complete blockwise assembly receipt: common contraction and both global
endpoint Riemann--Hurwitz inequalities. -/
theorem paste_contracts_and_riemannHurwitzAt (wall : SheetPartition d)
    (resolution : Fin d → LocalResolution d)
    (hContracts : ∀ anchor, (resolution anchor).ContractsTo wall)
    (leftExternal rightExternal : List (SheetPartition d))
    (hLeft : ∀ anchor, wall.repr anchor = anchor →
      RiemannHurwitzAtBlock wall (resolution anchor).left
        ((resolution anchor).newEdge :: leftExternal) anchor)
    (hRight : ∀ anchor, wall.repr anchor = anchor →
      RiemannHurwitzAtBlock wall (resolution anchor).right
        ((resolution anchor).newEdge :: rightExternal) anchor) :
    (paste wall resolution hContracts).ContractsTo wall ∧
      SheetPartition.RiemannHurwitzAt
        (paste wall resolution hContracts).left
        ((paste wall resolution hContracts).newEdge :: leftExternal) ∧
      SheetPartition.RiemannHurwitzAt
        (paste wall resolution hContracts).right
        ((paste wall resolution hContracts).newEdge :: rightExternal) := by
  exact ⟨paste_contracts wall resolution hContracts,
    paste_left_riemannHurwitzAt wall resolution hContracts leftExternal hLeft,
    paste_right_riemannHurwitzAt wall resolution hContracts rightExternal hRight⟩

end DraismaVargas.LocalCases.ResolutionM11.LocalResolution
