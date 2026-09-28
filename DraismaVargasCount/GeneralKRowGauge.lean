import DraismaVargasCount.GeneralKRowEquiv

/-!
# Transport across the general-`K` label gauge

Part of the valency-four limits of general `K` (Vargas, Part II, case `{v4-nd4}`,
`subsec-case-v4`), which feed the type changes at merged-vertex valency four (step 3 of
`Assembly`).

`GeneralKReceipts.LabelGauge.gaugedData` relabels the four star branches of a
wall datum by four block-preserving sheet permutations, in four branch swaps.
This file records what the row dictionary needs from that gauge:

* `isDangling_gauged_iff`: the old occurrence of the star label `l` through the
  sheet `gauge.perm l s` of the gauged datum is dangling exactly when the
  incoming occurrence through `s` is;
* `nonDanglingValency_gauged_wall`: the surviving valency of every wall-block
  vertex is unchanged;
* `gaugeIso`: the gauge as a `Transport.DatumIso` with the identity on the
  target, whence the stable-row equivalence and the natural matrix transport.

The `K = 0` counterparts are `NonTrivalentValencyFourRows.gauged_isDangling_iff`
and `NonTrivalentValencyFourRowEquivFinal.nonDanglingValency_gaugedBlock`, for a
single branch swap.

## What is NOT proved here

Nothing is claimed about sheets of the anchor block beyond the star-label
occurrences through them.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.GeneralKRowGauge

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.BlockPreservingBranchSwap
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.Count.GeneralKReceipts

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

/-- The sheet relabelling of one swap step. -/
noncomputable abbrev stepRelab (star : W4TargetPairings.FourStar target wall)
    (current : GluingDatum target degree) (label : Fin 4)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (current.vertexPartition wall).Rel (permutation sheet) sheet) :
    current.SheetRelabeling :=
  branchSwapOfPerm current wall
    (TargetSeparation.farEndpoint wall (star.edge label))
    (TargetSeparation.farEndpoint_ne (selectedEdge_incident (star := star) label))
    permutation hFix

section Step

variable (star : W4TargetPairings.FourStar target wall)
  (current : GluingDatum target degree) (label : Fin 4)
  (permutation : Equiv.Perm (Fin degree))
  (hFix : ∀ sheet, (current.vertexPartition wall).Rel (permutation sheet) sheet)

theorem step_vertexPermutation_wall :
    (stepRelab star current label permutation hFix).vertexPermutation wall =
      Equiv.refl (Fin degree) := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.vertexMoved wall _ _ wall) permutation = _
  rw [TargetBranchRegion.vertexMoved_wall]
  rfl

theorem step_edgePermutation (hConnected : graph_connected target)
    (hGenus : genus target = 0) (l : Fin 4) :
    (stepRelab star current label permutation hFix).edgePermutation (star.edge l) =
      if l = label then permutation else Equiv.refl (Fin degree) := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall _ _ (star.edge l)) permutation = _
  split_ifs with hl
  · subst hl
    rw [TargetSeparation.edgeMoved_self_eq_true (selectedEdge_incident (star := star) l)]
    rfl
  · rw [TargetSeparation.edgeMoved_eq_false hConnected hGenus
      (selectedEdge_incident (star := star) label) (selectedEdge_incident (star := star) l)
      (fun hEqual ↦ hl (star.edge_injective hEqual).symm)]
    rfl

theorem step_isDangling_iff (hConnected : graph_connected target)
    (hGenus : genus target = 0) (hConn : current.Connected) (l : Fin 4) (t : Fin degree) :
    IsDangling (swapStep star current label permutation hFix)
        ((swapStep star current label permutation hFix).sourceEdge (star.edge l)
          ((if l = label then permutation else Equiv.refl (Fin degree)) t)) ↔
      IsDangling current (current.sourceEdge (star.edge l) t) := by
  rw [← step_edgePermutation star current label permutation hFix hConnected hGenus l]
  have h := SheetRelabelPruning.sourceEdgeEquiv_sourceEdge
    (stepRelab star current label permutation hFix) (star.edge l) t
  have h2 := SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff
    (stepRelab star current label permutation hFix) hConn (current.sourceEdge (star.edge l) t)
  rw [h] at h2
  exact h2

theorem step_nonDanglingValency_wall (hConn : current.Connected) (s : Fin degree) :
    nonDanglingValency (swapStep star current label permutation hFix)
        ((swapStep star current label permutation hFix).sourceEndpoint wall s) =
      nonDanglingValency current (current.sourceEndpoint wall s) := by
  have h := SheetRelabelPruning.sourceVertexEquiv_sourceEndpoint
    (stepRelab star current label permutation hFix) wall s
  rw [step_vertexPermutation_wall] at h
  have h2 := SheetRelabelStable.nonDanglingValency_map
    (stepRelab star current label permutation hFix) hConn (current.sourceEndpoint wall s)
  rw [h] at h2
  exact h2

end Step

section Gauge

variable {data : GluingDatum target degree} {anchor : Fin degree}
  (star : W4TargetPairings.FourStar target wall) (gauge : LabelGauge data wall anchor)
  (hConnected : graph_connected target) (hGenus : genus target = 0) (hValid : data.Valid)

include hConnected hGenus hValid in
/-- **Dangling occurrences across the gauge**: through the sheet
`gauge.perm l s`, the gauged occurrence of the star label `l` is dangling
exactly when the incoming occurrence through `s` is. -/
theorem isDangling_gauged_iff (l : Fin 4) (s : Fin degree) :
    IsDangling (gauge.gaugedData star)
        ((gauge.gaugedData star).sourceEdge (star.edge l) (gauge.perm l s)) ↔
      IsDangling data (data.sourceEdge (star.edge l) s) := by
  have c0 : data.Connected := hValid.1
  have c1 : (gauge.stage1 star).Connected :=
    (swapStep_valid _ _ _ _ _ hValid).1
  have c2 : (gauge.stage2 star).Connected :=
    (swapStep_valid _ _ _ _ _ (swapStep_valid _ _ _ _ _ hValid)).1
  have c3 : (gauge.stage3 star).Connected :=
    (swapStep_valid _ _ _ _ _ (swapStep_valid _ _ _ _ _
      (swapStep_valid _ _ _ _ _ hValid))).1
  have h0 := fun t ↦ step_isDangling_iff star data 0 (gauge.perm 0) (gauge.fix 0)
    hConnected hGenus c0 l t
  have h1 := fun t ↦ step_isDangling_iff star (gauge.stage1 star) 1 (gauge.perm 1)
    (fun sheet ↦ by rw [LabelGauge.stage1_wall]; exact gauge.fix 1 sheet)
    hConnected hGenus c1 l t
  have h2 := fun t ↦ step_isDangling_iff star (gauge.stage2 star) 2 (gauge.perm 2)
    (fun sheet ↦ by rw [LabelGauge.stage2_wall]; exact gauge.fix 2 sheet)
    hConnected hGenus c2 l t
  have h3 := fun t ↦ step_isDangling_iff star (gauge.stage3 star) 3 (gauge.perm 3)
    (fun sheet ↦ by rw [LabelGauge.stage3_wall]; exact gauge.fix 3 sheet)
    hConnected hGenus c3 l t
  fin_cases l
  · simp only [Fin.zero_eta, Fin.isValue, if_true, Fin.reduceEq, if_false,
      Equiv.refl_apply] at h0 h1 h2 h3
    exact ((h3 _).trans ((h2 _).trans (h1 _))).trans (h0 s)
  · simp only [Fin.mk_one, Fin.isValue, if_true, Fin.reduceEq, if_false,
      Equiv.refl_apply] at h0 h1 h2 h3
    exact ((h3 _).trans (h2 _)).trans ((h1 s).trans (h0 s))
  · simp only [Fin.reduceFinMk, Fin.isValue, if_true, Fin.reduceEq, if_false,
      Equiv.refl_apply] at h0 h1 h2 h3
    exact (h3 _).trans ((h2 s).trans ((h1 s).trans (h0 s)))
  · simp only [Fin.reduceFinMk, Fin.isValue, if_true, Fin.reduceEq, if_false,
      Equiv.refl_apply] at h0 h1 h2 h3
    exact (h3 s).trans ((h2 s).trans ((h1 s).trans (h0 s)))

include hValid in
/-- **Surviving valency at the wall is unchanged by the gauge.** -/
theorem nonDanglingValency_gauged_wall (s : Fin degree) :
    nonDanglingValency (gauge.gaugedData star)
        ((gauge.gaugedData star).sourceEndpoint wall s) =
      nonDanglingValency data (data.sourceEndpoint wall s) := by
  have c0 : data.Connected := hValid.1
  have c1 : (gauge.stage1 star).Connected :=
    (swapStep_valid _ _ _ _ _ hValid).1
  have c2 : (gauge.stage2 star).Connected :=
    (swapStep_valid _ _ _ _ _ (swapStep_valid _ _ _ _ _ hValid)).1
  have c3 : (gauge.stage3 star).Connected :=
    (swapStep_valid _ _ _ _ _ (swapStep_valid _ _ _ _ _
      (swapStep_valid _ _ _ _ _ hValid))).1
  rw [show gauge.gaugedData star = swapStep star (gauge.stage3 star) 3 (gauge.perm 3)
      (fun sheet ↦ by rw [LabelGauge.stage3_wall]; exact gauge.fix 3 sheet) from rfl,
    step_nonDanglingValency_wall _ _ _ _ _ c3]
  rw [show gauge.stage3 star = swapStep star (gauge.stage2 star) 2 (gauge.perm 2)
      (fun sheet ↦ by rw [LabelGauge.stage2_wall]; exact gauge.fix 2 sheet) from rfl,
    step_nonDanglingValency_wall _ _ _ _ _ c2]
  rw [show gauge.stage2 star = swapStep star (gauge.stage1 star) 1 (gauge.perm 1)
      (fun sheet ↦ by rw [LabelGauge.stage1_wall]; exact gauge.fix 1 sheet) from rfl,
    step_nonDanglingValency_wall _ _ _ _ _ c1]
  rw [show gauge.stage1 star = swapStep star data 0 (gauge.perm 0) (gauge.fix 0) from rfl,
    step_nonDanglingValency_wall _ _ _ _ _ c0]

/-- **The gauge as an isomorphism of gluing data**, with the identity on the
target: the composite of the four branch swaps. -/
noncomputable def gaugeIso : Transport.DatumIso data (gauge.gaugedData star) :=
  ((Transport.DatumIso.ofSheetRelabeling (stepRelab star data 0 (gauge.perm 0) (gauge.fix 0)) :
      Transport.DatumIso data (gauge.stage1 star)).trans
    (Transport.DatumIso.ofSheetRelabeling (stepRelab star (gauge.stage1 star) 1 (gauge.perm 1)
      (fun sheet ↦ by rw [LabelGauge.stage1_wall]; exact gauge.fix 1 sheet)) :
      Transport.DatumIso (gauge.stage1 star) (gauge.stage2 star))).trans
  (((Transport.DatumIso.ofSheetRelabeling (stepRelab star (gauge.stage2 star) 2 (gauge.perm 2)
      (fun sheet ↦ by rw [LabelGauge.stage2_wall]; exact gauge.fix 2 sheet)) :
      Transport.DatumIso (gauge.stage2 star) (gauge.stage3 star))).trans
    (Transport.DatumIso.ofSheetRelabeling (stepRelab star (gauge.stage3 star) 3 (gauge.perm 3)
      (fun sheet ↦ by rw [LabelGauge.stage3_wall]; exact gauge.fix 3 sheet)) :
      Transport.DatumIso (gauge.stage3 star) (gauge.gaugedData star)))

@[simp] theorem gaugeIso_targetEdge (edge : target.edges) :
    (gaugeIso star gauge).targetEdge edge = edge := rfl

@[simp] theorem gaugeIso_targetVertex (vertex : target.V) :
    (gaugeIso star gauge).targetVertex vertex = vertex := rfl

end Gauge

end DraismaVargas.Count.GeneralKRowGauge
