module

public import DraismaVargas.LocalCases.LimitChainCore
public import DraismaVargas.LocalCases.W2SourceTransport

@[expose] public section

/-!
# Transporting Figure 33's M-1k data across the branch swap

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w2-r2-nd3-M-1k}`, Figure 33 and
Equation (7).  Part I compares gluing data up to isomorphism, so the members of
one family may legitimately live over different representatives of a single
isomorphism class; for fixed gluing data this has to be made explicit, and this
file does so for Figure 33 (the swapped-datum slot of `GlobalM1k`).

## Why a transport is needed at all

`W2M1kSourceCandidates.no_common_geometry` and `W2M1kSwapped.no_common_patterns`
show that **no** `w2M1k` gluing datum carries both `M⁽¹⁾` (Base I.a) and `M⁽²⁾`
(Base II.2.2.M).  Writing `p₀`, `p₁` for the unique index-one occurrence's sheet
in the two wall directions, `M⁽¹⁾` forces `p₀ = p₁`
(`firstPattern_forces_aligned`, and structurally `LeafPair.aligned`) and `M⁽²⁾`
forces `p₀ ≠ p₁` (`secondPattern_second_eq_pinSheet`, and structurally
`DividedData.pins_ne`).  Exactly one of the two lives over a given datum
(`exists_leafPair_or_dividedData`, `not_leafPair_and_dividedData`); the other
lives over a branch-swapped copy.

The two moves are mirror images and this file treats them uniformly.  The
relabelling is always `ResolutionM11.wallBranchSwap` across the `t₃` branch --
`W2M1kSwapped`'s own gauge move, whose root is
`M11RemoteCandidates.branchRoot star 1` -- transposing `p₀` with a chosen
partner sheet of the same wall block:

* from an **aligned** datum, swapping `p₀` with the leaf pair's second sheet
  separates the copy's two pinned sheets (`swapProfile_pins_ne`), so the copy
  carries `M⁽²⁾`;
* from a **separated** datum, swapping `p₀` with `p₁` aligns the copy
  (`swapProfile_aligned`), so the copy carries `M⁽¹⁾`.

Both are read off `W2M1kSwapped.branchSwap_separates_of_genus_zero` and
`branchSwap_aligns_of_genus_zero` -- which discharge the separation hypothesis
from `graph_connected target` and `genus target = 0` -- together with
`W2M1kSourceCandidates.eq_pinSheet_of_block_singleton`, the statement that on an
M-1k block the only sheet a direction isolates is its own pinned sheet.

## What the gauge does and does not already give

`W2SourceTransport` already transports the `W2SourceInput`, the
`W2R2SourceProfile.SourceProfile` and -- unlike the M-kk case, where a bespoke
`shapeRelabel` is needed -- the M-1k `Shape` itself
(`W2SourceTransport.shape_relabel`), so `swapShape` below is free.
`LimitChainCore.Gauge.ofSheetRelabeling` and `Gauge.matrix_gauge` carry the row
bijection and the *whole* natural stable-length matrix.

They do **not** carry `LimitChainCore.backgroundColumn`, which is not a matrix
entry but the sum over the occurrences of one old wall column that lie
**outside** the distinguished block `A₀`.  A gauge's occurrence bijection may
move a sheet, so "outside `A₀`" is not automatically preserved;
`background_gauge` below isolates exactly the extra hypothesis that is needed --

    every occurrence above the given target direction keeps its wall block --

and `swap_sheet_rel` discharges it for the branch swap from the relabelling's
own `compatible_left` / `compatible_right` together with
`W2SourceTransport.wallBranchSwap_vertexPermutation_wall_local`.  No hypothesis
beyond the two standing target hypotheses `graph_connected target`,
`genus target = 0` (which `W2M1kSwapped.separated` consumes) and
`data.Connected` (which every `SecondEquation.W2SourceInput` carries) is used.

## A duplicated lemma

`background_gauge` mentions only `LimitChainCore.Gauge`,
`LimitChainCore.backgroundColumn` and `StableSourceMatrix.occurrences`, so it
belongs beside `Gauge.matrix_gauge` in `LimitChainCore`.  It is proved verbatim a
second time here, `W2MkkTransport.background_gauge` being the first: that file
belongs to the M-kk case and an M-1k module does not import it, so the
duplication is deliberate.
-/

namespace DraismaVargas.LocalCases.W2M1kTransport

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open StableSourceMatrix
open ResolutionM11 GlobalM11Arbitrary
open W2M1kSourceCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-! ## The gauge move that exchanges the two Figure 33 orientations -/

/-- **Figure 33's gauge move, named.**  The branch swap across the `t₃` branch
transposing the first pinned sheet with a chosen sheet of the same wall block.
This is the relabelling `W2M1kSourceCandidates.branchSwap_aligns` and
`branchSwap_separates` study, and `W2M1kSwapped.swappedData` is its `apply`. -/
noncomputable def swapRelabeling (profile : W2R2SourceProfile.SourceProfile data star block)
    (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    data.SheetRelabeling :=
  ResolutionM11.wallBranchSwap data wall
    (M11RemoteCandidates.branchRoot star 1)
    (M11RemoteCandidates.branchRoot_ne star 1)
    (pinSheet profile 0) other hOther

/-- The swap is the identity at the wall: `TargetBranchRegion` never puts the
wall in the moved branch. -/
theorem swap_vertexPermutation_wall (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    (swapRelabeling profile other hOther).vertexPermutation wall = Equiv.refl _ :=
  W2SourceTransport.wallBranchSwap_vertexPermutation_wall_local _ _ _ _ _

/-- Hence it leaves the wall's own sheet partition literally alone. -/
theorem swap_vertexPartition_wall (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    (swapRelabeling profile other hOther).apply.vertexPartition wall =
      data.vertexPartition wall :=
  W2SourceTransport.wallBranchSwap_vertexPartition_wall_local _ _ _ _ _

/-! ## The transported wall block, input, profile and shape -/

/-- The gauge copy of the distinguished wall block: the same block, since the
swap is the identity at the wall. -/
noncomputable def swapBlock (profile : W2R2SourceProfile.SourceProfile data star block)
    (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    WallBlock (swapRelabeling profile other hOther).apply wall :=
  W2SourceTransport.wallBlockEquiv (swapRelabeling profile other hOther) wall block

@[simp] theorem swapBlock_val (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    (swapBlock profile other hOther).1 = block.1 := by
  show (swapRelabeling profile other hOther).vertexPermutation wall block.1 = block.1
  rw [swap_vertexPermutation_wall]
  rfl

/-- The transported `W2SourceInput` on the gauge copy. -/
theorem swapInput (input : W2SourceInput data star) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    W2SourceInput (swapRelabeling profile other hOther).apply star :=
  W2SourceTransport.input_relabel input (swapRelabeling profile other hOther)

/-- The transported occurrence profile on the gauge copy. -/
noncomputable def swapProfile (profile : W2R2SourceProfile.SourceProfile data star block)
    (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    W2R2SourceProfile.SourceProfile (swapRelabeling profile other hOther).apply star
      (swapBlock profile other hOther) :=
  W2SourceTransport.sourceProfile_relabel profile (swapRelabeling profile other hOther)
    hConnected (swapBlock profile other hOther) rfl

@[simp] theorem swapProfile_doubleLabel (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    (swapProfile profile hConnected other hOther).doubleLabel = profile.doubleLabel := rfl

@[simp] theorem swapProfile_singleLabel (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    (swapProfile profile hConnected other hOther).singleLabel = profile.singleLabel := rfl

/-- **The M-1k shape transports for free.**  Unlike M-kk, whose refinement
needed a bespoke `W2MkkTransport.shapeRelabel`, `W2SourceTransport.shape_relabel`
already lands in the M-1k `Shape`. -/
noncomputable def swapShape (shape : Shape profile) (hConnected : data.Connected)
    (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    Shape (swapProfile profile hConnected other hOther) :=
  W2SourceTransport.shape_relabel shape (swapRelabeling profile other hOther) hConnected
    (swapBlock profile other hOther) rfl

@[simp] theorem swapShape_k (shape : Shape profile) (hConnected : data.Connected)
    (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    (swapShape shape hConnected other hOther).k = shape.k := rfl

/-! ## The gauge -/

/-- **The swap is a `LimitChainCore.Gauge`**: it carries target occurrence,
dilation index, pruning, the stable quotient and the wall partition. -/
noncomputable def swapGauge (profile : W2R2SourceProfile.SourceProfile data star block)
    (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    LimitChainCore.Gauge data (swapRelabeling profile other hOther).apply wall :=
  LimitChainCore.Gauge.ofSheetRelabeling (swapRelabeling profile other hOther) hConnected
    (swap_vertexPartition_wall other hOther)

@[simp] theorem swapGauge_edge (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (edge : data.SourceEdge) :
    (swapGauge profile hConnected other hOther).edge edge =
      (swapRelabeling profile other hOther).sourceEdgeEquiv edge := rfl

/-- `k₁ = 1` is a gauge invariant. -/
theorem swapProfile_first_index (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    (swapRelabeling profile other hOther).apply.sourceEdgeIndex
        (swapProfile profile hConnected other hOther).first.1 =
      data.sourceEdgeIndex profile.first.1 :=
  W2SourceTransport.incidentEquiv_index _ _ _ _ _ _

/-- `k₂ = k` is a gauge invariant. -/
theorem swapProfile_second_index (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) :
    (swapRelabeling profile other hOther).apply.sourceEdgeIndex
        (swapProfile profile hConnected other hOther).second.1 =
      data.sourceEdgeIndex profile.second.1 :=
  W2SourceTransport.incidentEquiv_index _ _ _ _ _ _

/-! ## What the swap does to the two pinned sheets

Both orientation statements go through one reader: on an M-1k block the only
sheet a wall direction isolates is that direction's own pinned sheet. -/

/-- **Identifying a pinned sheet of the gauge copy.**  This is
`W2M1kSourceCandidates.eq_pinSheet_of_block_singleton` read on the copy, with
the copy's wall block and wall partition put back to the incoming datum's. -/
theorem eq_swapPinSheet (shape : Shape profile) (hConnected : data.Connected)
    (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (label : Fin 2) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet)
    (hSingleton : ((swapRelabeling profile other hOther).apply.edgePartition
      (star.edge label)).block sheet = {sheet}) :
    sheet = pinSheet (swapProfile profile hConnected other hOther) label := by
  refine eq_pinSheet_of_block_singleton (swapShape shape hConnected other hOther) label sheet
    ?_ hSingleton
  rw [swapBlock_val, swap_vertexPartition_wall]
  exact hRel

/-- **From aligned to separated.**  Swapping the first pinned sheet with any
other sheet of the block leaves the `t₂` direction alone and relabels the `t₃`
one, so on the copy the two directions isolate the two *distinct* sheets `p₀`
and `other`: the copy carries `W2M1kSourceCandidates.DividedData`, Base
II.2.2.M.  The alignment of the incoming datum is what makes the `t₃` direction
move `p₀` to `other` rather than somewhere else. -/
theorem swapProfile_pins_ne (shape : Shape profile) (hConnected : data.Connected)
    (hAligned : pinSheet profile 0 = pinSheet profile 1)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (hNe : pinSheet profile 0 ≠ other) :
    pinSheet (swapProfile profile hConnected other hOther) 0 ≠
      pinSheet (swapProfile profile hConnected other hOther) 1 := by
  obtain ⟨hZero, hOne, _⟩ := W2M1kSwapped.branchSwap_separates_of_genus_zero
    (star := star) shape hAligned other hOther hNe hTargetConnected hGenus
  have h₀ := eq_swapPinSheet shape hConnected other hOther 0 (pinSheet profile 0)
    (pinSheet_rel (profile := profile) 0) hZero
  have h₁ := eq_swapPinSheet shape hConnected other hOther 1 other
    ((pinSheet_rel (profile := profile) 0).trans hOther) hOne
  rw [← h₀, ← h₁]
  exact hNe

/-- **From separated to aligned.**  Swapping the two pinned sheets makes *both*
wall directions of the copy isolate `p₀`, so the copy carries
`W2M1kSourceCandidates.LeafPair`, Base I.a.  This is the same statement as
`W2SourceTransport.alignedProfile_aligned`, restated for the uniform
`swapRelabeling` of this file. -/
theorem swapProfile_aligned (shape : Shape profile) (hConnected : data.Connected)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0) :
    pinSheet (swapProfile profile hConnected (pinSheet profile 1)
        (W2SourceTransport.alignedTogether profile)) 0 =
      pinSheet (swapProfile profile hConnected (pinSheet profile 1)
        (W2SourceTransport.alignedTogether profile)) 1 := by
  have hBlock : ∀ label : Fin 2,
      ((swapRelabeling profile (pinSheet profile 1)
          (W2SourceTransport.alignedTogether profile)).apply.edgePartition
        (star.edge label)).block (pinSheet profile 0) = {pinSheet profile 0} := fun label ↦
    W2M1kSwapped.branchSwap_aligns_of_genus_zero (star := star) shape hTargetConnected
      hGenus label
  have h₀ := eq_swapPinSheet shape hConnected (pinSheet profile 1)
    (W2SourceTransport.alignedTogether profile) 0 (pinSheet profile 0)
    (pinSheet_rel (profile := profile) 0) (hBlock 0)
  have h₁ := eq_swapPinSheet shape hConnected (pinSheet profile 1)
    (W2SourceTransport.alignedTogether profile) 1 (pinSheet profile 0)
    (pinSheet_rel (profile := profile) 0) (hBlock 1)
  exact h₀.symm.trans h₁

/-! ## The copy is `W2M1kSwapped`'s own, and `W2SourceTransport`'s gauge is the aligning case -/

/-- **The aligning move is `W2SourceTransport.alignedRelabeling`**, the gauge of
`W2SourceTransport`: swapping the two pinned sheets is the `other := p₁` case of this file's
uniform move.  So `swapProfile_aligned` and
`W2SourceTransport.alignedProfile_aligned` speak about the same copy. -/
theorem swapRelabeling_pinSheet_one_eq_alignedRelabeling
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    swapRelabeling profile (pinSheet profile 1) (W2SourceTransport.alignedTogether profile) =
      W2SourceTransport.alignedRelabeling profile := rfl

/-- **The copy carrying the remote `M⁽²⁾` is literally
`W2M1kSwapped.swappedData` at the leaf member's own `GlobalM1k.Geometry`** --
the datum `GlobalM1k.swappedCandidates` puts its `SecondPattern.remoteCertified`
entry over. -/
theorem swapRelabeling_apply_eq_swappedData_leaf (shape : Shape profile)
    (pair : LeafPair profile) :
    (swapRelabeling profile pair.second pair.rel_second).apply =
      W2M1kSwapped.swappedData star (pair.geometry shape) := rfl

/-- **The copy carrying the remote `M⁽¹⁾` is `W2M1kSwapped.swappedData` at the
divided member's own `GlobalM1k.Geometry`.**  The mirror of the previous
statement, for the orientation in which the incoming datum is `M⁽²⁾`-shaped. -/
theorem swapRelabeling_apply_eq_swappedData_divided (shape : Shape profile)
    (divided : DividedData profile) :
    (swapRelabeling profile (pinSheet profile 1)
        (W2SourceTransport.alignedTogether profile)).apply =
      W2M1kSwapped.swappedData star (divided.geometry shape) := rfl

/-! ## The background column transports

`LimitChainCore.Gauge.matrix_gauge` carries a matrix entry; the background half
`s` of a limit box is not one, and needs the extra hypothesis isolated here. -/

/-- **A gauge carries the background column `s`** as soon as its occurrence
bijection keeps the wall block of every occurrence above the given direction.
Promotion target: `LimitChainCore.lean`, beside `Gauge.matrix_gauge`; the same
statement is `W2MkkTransport.background_gauge`, which an M-1k module must not
import. -/
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
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) (label : Fin 2)
    (e : data.SourceEdge) (hTarget : e.1.1 = star.edge label) :
    (data.vertexPartition wall).Rel
      ((swapGauge profile hConnected other hOther).edge e).1.2 e.1.2 := by
  show (data.vertexPartition wall).Rel
    ((swapRelabeling profile other hOther).edgePermutation e.1.1 e.1.2) e.1.2
  have hPerm := swap_vertexPermutation_wall (profile := profile) other hOther
  rcases W2M1kSwapped.star_incident star label with hSide | hSide
  · have hVertex : ((e.1.1 : target.V × target.V)).1 = wall := by rw [hTarget]; exact hSide
    have h := (swapRelabeling profile other hOther).compatible_left e.1.1 e.1.2
    rw [hVertex, hPerm] at h
    exact h
  · have hVertex : ((e.1.1 : target.V × target.V)).2 = wall := by rw [hTarget]; exact hSide
    have h := (swapRelabeling profile other hOther).compatible_right e.1.1 e.1.2
    rw [hVertex, hPerm] at h
    exact h

/-- **Figure 33's `s` is the same on the gauge copy**, read in the image row and
at whichever sheet of `A₀` anchors it. -/
theorem swap_backgroundColumn (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (anchor : Fin degree) (label : Fin 2) (path : StablePath data) :
    LimitChainCore.backgroundColumn (swapRelabeling profile other hOther).apply wall anchor
        ((swapGauge profile hConnected other hOther).row path) (star.edge label) =
      LimitChainCore.backgroundColumn data wall anchor path (star.edge label) :=
  background_gauge _ _ _ _ (swap_sheet_rel hConnected other hOther label)

end DraismaVargas.LocalCases.W2M1kTransport
