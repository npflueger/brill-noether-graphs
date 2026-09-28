import DraismaVargas.LocalCases.LimitChainCore
import DraismaVargas.LocalCases.W2MkkSourceCandidates
import DraismaVargas.LocalCases.W2SourceTransport

/-!
# Transporting Figure 34's M-kk data across the branch swap

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w2-r2-nd3-M-kk}`, Figure 34 and
Equation (8).  Part I compares gluing data up to isomorphism, so the members of
one family may legitimately live over different representatives of a single
isomorphism class; for fixed gluing data this has to be made explicit, and this
file does so for Figure 34.

## Why a transport is needed at all

`W2MkkSourceCandidates.no_common_geometry` shows that **no** `w2Mkk` gluing
datum carries both detachment members of Figure 34: a datum's dangling `t₃`
occurrence pins one sheet, that sheet lies in exactly one of the two `t₂`
endpoint blocks `e₁`, `e₂` (`pinSheet_mem`, `not_first_and_second`), and the
block it lies in decides whether the datum admits `M⁽¹⁾` (Base II.2.1.M) or
`M⁽²⁾` (Base II.2.2.M) -- never both.  The member the incoming datum does not
carry therefore lives over a branch-swapped copy of it, and
`W2MkkSourceCandidates.branchSwap_moves_pinSheet` already shows the swap is
exactly the move that exchanges the two.

This file makes that copy usable: it transports the M-kk `Shape`, names the
swap as an explicit `GluingDatum.SheetRelabeling`, computes what the swap does
to the three sheets Figure 34 names, and -- the one genuinely new ingredient --
transports the **background column** `s` of the limit box across the induced
`LimitChainCore.Gauge`.

## What the gauge does and does not already give

`LimitChainCore.Gauge.ofSheetRelabeling` and `Gauge.matrix_gauge` carry the row
bijection and the *whole* natural stable-length matrix of the incoming datum
across an arbitrary relabelling of a connected datum.  They do **not** carry
`LimitChainCore.backgroundColumn`, which is not a matrix entry but the sum over
the occurrences of one old wall column that lie **outside** the distinguished
block `A₀`.  A gauge's occurrence bijection may move a sheet, so "outside `A₀`"
is not automatically preserved; `background_gauge` below isolates exactly the
extra hypothesis that is needed --

    every occurrence above the given target direction keeps its wall block --

and `swap_sheet_rel` discharges it for the branch swap from the relabelling's
own `compatible_left` / `compatible_right` together with
`W2SourceTransport.wallBranchSwap_vertexPermutation_wall_local`.  No hypothesis
beyond the two standing target hypotheses `graph_connected target`,
`genus target = 0` (which `W2MkkSourceCandidates.singleLabel_fixed` consumes)
and `data.Connected` (which every `SecondEquation.W2SourceInput` carries) is
used.

## A lemma that belongs to `LimitChainCore`

`background_gauge` mentions only `LimitChainCore.Gauge`,
`LimitChainCore.backgroundColumn` and `StableSourceMatrix.occurrences`, so it
belongs beside `Gauge.matrix_gauge` in `LimitChainCore`; it is proved here.
-/

namespace DraismaVargas.LocalCases.W2MkkTransport

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open StableSourceMatrix
open ResolutionM11 GlobalM11Arbitrary
open W2MkkSourceCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-! ## The M-kk shape transports

`W2SourceTransport.shape_relabel` does this for the M-1k refinement; the M-kk
one has different fields (`deleted_single`, `one_lt_first`, `one_lt_second`)
and is transported here.  Cardinality M travels verbatim because
`W2SourceTransport.incidentEquiv_target` is a `rfl`, and the two case
inequalities travel by `incidentEquiv_index`. -/

/-- **The M-kk refinement of a `w2-r2-nd3` profile transports along an
arbitrary compatible sheet relabelling.** -/
theorem shapeRelabel (shape : Shape profile) (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (swapped : WallBlock relabeling.apply wall)
    (hVal : swapped.1 = relabeling.vertexPermutation wall block.1) :
    Shape (W2SourceTransport.sourceProfile_relabel profile relabeling hConnected
      swapped hVal) where
  deleted_single := shape.deleted_single
  one_lt_first := by
    show 1 < relabeling.apply.sourceEdgeIndex
      (W2SourceTransport.incidentEquiv relabeling wall block swapped hVal profile.first).1
    rw [W2SourceTransport.incidentEquiv_index relabeling wall block swapped hVal]
    exact shape.one_lt_first
  one_lt_second := by
    show 1 < relabeling.apply.sourceEdgeIndex
      (W2SourceTransport.incidentEquiv relabeling wall block swapped hVal profile.second).1
    rw [W2SourceTransport.incidentEquiv_index relabeling wall block swapped hVal]
    exact shape.one_lt_second

/-! ## The branch swap that moves the pinned sheet -/

/-- **Figure 34's gauge move, named.**  The branch swap across the `t₂` branch
transposing the pinned sheet with a chosen sheet of the same wall block.  This
is the relabelling `W2MkkSourceCandidates.branchSwap_moves_pinSheet` studies. -/
noncomputable def swapRelabeling (profile : W2R2SourceProfile.SourceProfile data star block)
    (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    data.SheetRelabeling :=
  ResolutionM11.wallBranchSwap data wall
    (M11RemoteCandidates.branchRoot star profile.doubleLabel)
    (M11RemoteCandidates.branchRoot_ne star profile.doubleLabel)
    (pinSheet profile) other hOther

/-- The swap is the identity at the wall: `TargetBranchRegion` never puts the
wall in the moved branch. -/
theorem swap_vertexPermutation_wall (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    (swapRelabeling profile other hOther).vertexPermutation wall = Equiv.refl _ :=
  W2SourceTransport.wallBranchSwap_vertexPermutation_wall_local _ _ _ _ _

/-- Hence it leaves the wall's own sheet partition literally alone. -/
theorem swap_vertexPartition_wall (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    (swapRelabeling profile other hOther).apply.vertexPartition wall =
      data.vertexPartition wall :=
  W2SourceTransport.wallBranchSwap_vertexPartition_wall_local _ _ _ _ _

/-- The `t₂` direction is the one the swap is taken across, so it is moved. -/
theorem swap_edgePermutation_double (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    (swapRelabeling profile other hOther).edgePermutation
        (star.edge profile.doubleLabel) = Equiv.swap (pinSheet profile) other := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall
      (M11RemoteCandidates.branchRoot star profile.doubleLabel)
      (M11RemoteCandidates.branchRoot_ne star profile.doubleLabel)
      (star.edge profile.doubleLabel)) (Equiv.swap (pinSheet profile) other) = _
  rw [doubleLabel_moved profile]
  rfl

/-- **The `t₃` direction is fixed**, so the swap does not move the dangling
occurrence `e₄` and the case is still M-kk on the copy.  This is where the two
standing target hypotheses enter, exactly as in
`W2MkkSourceCandidates.singleLabel_fixed`. -/
theorem swap_edgePermutation_single (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    (swapRelabeling profile other hOther).edgePermutation
        (star.edge profile.singleLabel) = Equiv.refl _ := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall
      (M11RemoteCandidates.branchRoot star profile.doubleLabel)
      (M11RemoteCandidates.branchRoot_ne star profile.doubleLabel)
      (star.edge profile.singleLabel)) (Equiv.swap (pinSheet profile) other) = _
  rw [singleLabel_fixed hTargetConnected hGenus profile]
  rfl

/-! ## The transported wall block, input, profile and shape -/

/-- The gauge copy of the distinguished wall block: the same block, since the
swap is the identity at the wall. -/
noncomputable def swapBlock (profile : W2R2SourceProfile.SourceProfile data star block)
    (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    WallBlock (swapRelabeling profile other hOther).apply wall :=
  W2SourceTransport.wallBlockEquiv (swapRelabeling profile other hOther) wall block

@[simp] theorem swapBlock_val (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    (swapBlock profile other hOther).1 = block.1 := by
  show (swapRelabeling profile other hOther).vertexPermutation wall block.1 = block.1
  rw [swap_vertexPermutation_wall]
  rfl

/-- The transported `W2SourceInput` on the gauge copy. -/
theorem swapInput (input : W2SourceInput data star) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    W2SourceInput (swapRelabeling profile other hOther).apply star :=
  W2SourceTransport.input_relabel input (swapRelabeling profile other hOther)

/-- The transported occurrence profile on the gauge copy. -/
noncomputable def swapProfile (profile : W2R2SourceProfile.SourceProfile data star block)
    (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    W2R2SourceProfile.SourceProfile (swapRelabeling profile other hOther).apply star
      (swapBlock profile other hOther) :=
  W2SourceTransport.sourceProfile_relabel profile (swapRelabeling profile other hOther)
    hConnected (swapBlock profile other hOther) rfl

@[simp] theorem swapProfile_doubleLabel (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    (swapProfile profile hConnected other hOther).doubleLabel = profile.doubleLabel := rfl

@[simp] theorem swapProfile_singleLabel (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    (swapProfile profile hConnected other hOther).singleLabel = profile.singleLabel := rfl

/-- The transported M-kk shape on the gauge copy. -/
theorem swapShape (shape : Shape profile) (hConnected : data.Connected)
    (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    Shape (swapProfile profile hConnected other hOther) :=
  shapeRelabel shape (swapRelabeling profile other hOther) hConnected
    (swapBlock profile other hOther) rfl

/-! ## What the swap does to Figure 34's three sheets -/

/-- **The pinned sheet does not move.**  `e₄` lies above `t₃`, which the swap
fixes, so the copy is pinned at the same sheet and is still M-kk there. -/
theorem swapProfile_pinSheet (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    pinSheet (swapProfile profile hConnected other hOther) = pinSheet profile := by
  show (swapRelabeling profile other hOther).edgePermutation
      (profile.deleted.edge.1.1.1) (pinSheet profile) = pinSheet profile
  rw [shape.deleted_single, swap_edgePermutation_single hTargetConnected hGenus]
  rfl

/-- `e₁`'s canonical sheet moves by the transposition. -/
theorem swapProfile_firstSheet (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    firstSheet (swapProfile profile hConnected other hOther) =
      Equiv.swap (pinSheet profile) other (firstSheet profile) := by
  show (swapRelabeling profile other hOther).edgePermutation
      (profile.first.1.1.1) (firstSheet profile) = _
  rw [profile.first_target, swap_edgePermutation_double]

/-- `e₂`'s canonical sheet moves by the transposition. -/
theorem swapProfile_secondSheet (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    secondSheet (swapProfile profile hConnected other hOther) =
      Equiv.swap (pinSheet profile) other (secondSheet profile) := by
  show (swapRelabeling profile other hOther).edgePermutation
      (profile.second.1.1.1) (secondSheet profile) = _
  rw [profile.second_target, swap_edgePermutation_double]

/-- The pinned sheet and either endpoint sheet lie in one wall block, so their
transposition is a legal branch swap. -/
theorem secondSheet_together (profile : W2R2SourceProfile.SourceProfile data star block) :
    (data.vertexPartition wall).Rel (pinSheet profile) (secondSheet profile) :=
  (pinSheet_rel profile).symm.trans (secondSheet_rel profile)

theorem firstSheet_together (profile : W2R2SourceProfile.SourceProfile data star block) :
    (data.vertexPartition wall).Rel (pinSheet profile) (firstSheet profile) :=
  (pinSheet_rel profile).symm.trans (firstSheet_rel profile)

/-- **Swapping the pinned sheet with `e₂`'s canonical sheet puts the copy's pin
in the copy's `e₂` block**, whatever the incoming datum's own orientation was:
the transposition sends `e₂`'s sheet to the pin, and the pin does not move.  So
the copy admits `W2MkkSourceCandidates.SecondMember`, Base II.2.2.M. -/
theorem swapProfile_pin_second (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (hConnected : data.Connected) :
    (endpointPartition (swapProfile profile hConnected (secondSheet profile)
        (secondSheet_together profile))).Rel
      (secondSheet (swapProfile profile hConnected (secondSheet profile)
        (secondSheet_together profile)))
      (pinSheet (swapProfile profile hConnected (secondSheet profile)
        (secondSheet_together profile))) := by
  have hEq : secondSheet (swapProfile profile hConnected (secondSheet profile)
      (secondSheet_together profile)) =
      pinSheet (swapProfile profile hConnected (secondSheet profile)
        (secondSheet_together profile)) := by
    rw [swapProfile_secondSheet, Equiv.swap_apply_right,
      swapProfile_pinSheet shape hTargetConnected hGenus]
  rw [hEq]
  rfl

/-- The mirror statement: swapping with `e₁`'s canonical sheet puts the copy's
pin in the copy's `e₁` block, so the copy admits
`W2MkkSourceCandidates.FirstMember`, Base II.2.1.M. -/
theorem swapProfile_pin_first (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (hConnected : data.Connected) :
    (endpointPartition (swapProfile profile hConnected (firstSheet profile)
        (firstSheet_together profile))).Rel
      (firstSheet (swapProfile profile hConnected (firstSheet profile)
        (firstSheet_together profile)))
      (pinSheet (swapProfile profile hConnected (firstSheet profile)
        (firstSheet_together profile))) := by
  have hEq : firstSheet (swapProfile profile hConnected (firstSheet profile)
      (firstSheet_together profile)) =
      pinSheet (swapProfile profile hConnected (firstSheet profile)
        (firstSheet_together profile)) := by
    rw [swapProfile_firstSheet, Equiv.swap_apply_right,
      swapProfile_pinSheet shape hTargetConnected hGenus]
  rw [hEq]
  rfl

/-! ## The gauge -/

/-- **The swap is a `LimitChainCore.Gauge`**: it carries target occurrence,
dilation index, pruning, the stable quotient and the wall partition. -/
noncomputable def swapGauge (profile : W2R2SourceProfile.SourceProfile data star block)
    (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    LimitChainCore.Gauge data (swapRelabeling profile other hOther).apply wall :=
  LimitChainCore.Gauge.ofSheetRelabeling (swapRelabeling profile other hOther) hConnected
    (swap_vertexPartition_wall other hOther)

@[simp] theorem swapGauge_edge (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other)
    (edge : data.SourceEdge) :
    (swapGauge profile hConnected other hOther).edge edge =
      (swapRelabeling profile other hOther).sourceEdgeEquiv edge := rfl

/-- `k₁` is a gauge invariant. -/
theorem swapProfile_first_index (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    (swapRelabeling profile other hOther).apply.sourceEdgeIndex
        (swapProfile profile hConnected other hOther).first.1 =
      data.sourceEdgeIndex profile.first.1 :=
  W2SourceTransport.incidentEquiv_index _ _ _ _ _ _

/-- `k₂` is a gauge invariant. -/
theorem swapProfile_second_index (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    (swapRelabeling profile other hOther).apply.sourceEdgeIndex
        (swapProfile profile hConnected other hOther).second.1 =
      data.sourceEdgeIndex profile.second.1 :=
  W2SourceTransport.incidentEquiv_index _ _ _ _ _ _

/-! ## The background column transports

`LimitChainCore.Gauge.matrix_gauge` carries a matrix entry; the background half
`s` of a limit box is not one, and needs the extra hypothesis isolated here. -/

/-- **A gauge carries the background column `s`** as soon as its occurrence
bijection keeps the wall block of every occurrence above the given direction.
Promotion target: `LimitChainCore.lean`, beside `Gauge.matrix_gauge`. -/
theorem background_gauge {base : GluingDatum target degree}
    (gauge : LimitChainCore.Gauge data base wall) (anchor : Fin degree)
    (place : target.edges) (path : StablePath data)
    (hSheet : ∀ e : data.SourceEdge, e.1.1 = place →
      (data.vertexPartition wall).Rel (gauge.edge e).1.2 e.1.2) :
    LimitChainCore.backgroundColumn base wall anchor (gauge.row path) place =
      LimitChainCore.backgroundColumn data wall anchor path place := by
  classical
  have hImage : LimitChainCore.backgroundOccurrences base wall anchor (gauge.row path) place =
      (LimitChainCore.backgroundOccurrences data wall anchor path place).image gauge.edge := by
    ext item
    rw [LimitChainCore.mem_backgroundOccurrences, Finset.mem_image]
    constructor
    · rintro ⟨hOcc, hNot⟩
      rw [gauge.occurrences_gauge] at hOcc
      obtain ⟨pre, hPre, rfl⟩ := Finset.mem_image.mp hOcc
      have hTarget : pre.1.1 = place := ((mem_occurrences path place pre).mp hPre).2
      refine ⟨pre, (LimitChainCore.mem_backgroundOccurrences data wall anchor path place
        pre).mpr ⟨hPre, ?_⟩, rfl⟩
      intro hRel
      exact hNot (by rw [gauge.wall_eq]; exact hRel.trans (hSheet pre hTarget).symm)
    · rintro ⟨pre, hPre, rfl⟩
      obtain ⟨hOcc, hNot⟩ :=
        (LimitChainCore.mem_backgroundOccurrences data wall anchor path place pre).mp hPre
      have hTarget : pre.1.1 = place := ((mem_occurrences path place pre).mp hOcc).2
      refine ⟨?_, ?_⟩
      · rw [gauge.occurrences_gauge]
        exact Finset.mem_image_of_mem _ hOcc
      · rw [gauge.wall_eq]
        intro hRel
        exact hNot (hRel.trans (hSheet pre hTarget))
  unfold LimitChainCore.backgroundColumn
  rw [hImage, Finset.sum_image (fun _ _ _ _ hEqual ↦ gauge.edge.injective hEqual)]
  exact Finset.sum_congr rfl fun item _ ↦ by rw [gauge.index_eq]

/-- **The branch swap keeps the wall block of every occurrence above a wall
direction.**  This is the relabelling's own `compatible_left` /
`compatible_right` read at the wall, where its vertex permutation is the
identity. -/
theorem swap_sheet_rel (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) (label : Fin 2)
    (e : data.SourceEdge) (hTarget : e.1.1 = star.edge label) :
    (data.vertexPartition wall).Rel
      ((swapGauge profile hConnected other hOther).edge e).1.2 e.1.2 := by
  show (data.vertexPartition wall).Rel
    ((swapRelabeling profile other hOther).edgePermutation e.1.1 e.1.2) e.1.2
  have hPerm := swap_vertexPermutation_wall (profile := profile) other hOther
  rcases edge_incident star label with hSide | hSide
  · have hVertex : ((e.1.1 : target.V × target.V)).1 = wall := by rw [hTarget]; exact hSide
    have h := (swapRelabeling profile other hOther).compatible_left e.1.1 e.1.2
    rw [hVertex, hPerm] at h
    exact h
  · have hVertex : ((e.1.1 : target.V × target.V)).2 = wall := by rw [hTarget]; exact hSide
    have h := (swapRelabeling profile other hOther).compatible_right e.1.1 e.1.2
    rw [hVertex, hPerm] at h
    exact h

/-- **Figure 34's `s` is the same on the gauge copy**, read in the image row
and at the copy's own wall block. -/
theorem swap_backgroundColumn (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) (label : Fin 2)
    (path : StablePath data) :
    LimitChainCore.backgroundColumn (swapRelabeling profile other hOther).apply wall
        (swapBlock profile other hOther).1
        ((swapGauge profile hConnected other hOther).row path) (star.edge label) =
      LimitChainCore.backgroundColumn data wall block.1 path (star.edge label) := by
  rw [swapBlock_val]
  exact background_gauge _ _ _ _ (swap_sheet_rel hConnected other hOther label)

end DraismaVargas.LocalCases.W2MkkTransport
