import DraismaVargas.LocalCases.W2M1kSourceCandidates

/-!
# The swapped Figure 33 bundle at an actual `w2M1k` profile

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w2-r2-nd3-M-1k}`,
Figure 33 and Equation (7).

`W2M1kSourceCandidates.no_common_geometry` is the negative: no single `w2M1k`
gluing datum carries both `M⁽¹⁾` and `M⁽²⁾` on the distinguished block, so
`GlobalM1k.exists_valid_positive_exit` has no instance at a real profile.
`GlobalM1k`'s `section Swapped` supplies the positive shape -- the second member
over the branch-swapped datum.  This file supplies the instantiation between the
two, at an actual `w2M1k` profile.

## The M-1k analogue of `GlobalMkk.PinnedProfile`

M-kk and M-1k fail to share a datum for **different reasons**, and the two
remedies are correspondingly different.

* In M-kk the detached sheet is *not a parameter*: `e₄` is the only index-one
  occurrence above `t₃`, so `GlobalMkk.PinnedProfile` can carry the `t₂`
  endpoint refinement and the `t₃` pinning as two conditions that speak about
  different directions and cannot clash.  It is inhabited unconditionally.
* In M-1k the obstruction is an opposition between two free choices.  Writing
  `p₀`, `p₁` for the unique index-one occurrence's sheet in the two wall
  directions, `M⁽¹⁾` (Base I.a) forces `p₀ = p₁` -- the source's own
  `k₁ = |A''| = k₄`, derived here as
  `W2M1kSourceCandidates.firstPattern_forces_aligned` -- while `M⁽²⁾`
  (Base II.2.2.M) forces `p₀ ≠ p₁`
  (`W2M1kSourceCandidates.secondPattern_second_eq_pinSheet`).

The subset of the pattern conditions that can be carried without the clash is
therefore **`M⁽¹⁾`'s alone**: `AlignedProfile` below carries the split
background of the leaf member together with the single exterior condition
*both wall directions isolate the distinguished sheet*, stated once per
direction (`leftPinned`, `rightPinned`).  That **is** `p₀ = p₁`.  `M⁽²⁾`'s
Base II.2.2.M distinctness is then not carried at all: it is **derived** from
alignment across the gauge move, because the branch swap that transposes
`geometry.first` with `geometry.second` across the `t₃` branch fixes the `t₂`
occurrence partition and relabels the `t₃` one, turning one isolated sheet into
two distinct ones.  `AlignedProfile.swapped_pins_ne` is that derivation on its
own, and `AlignedProfile.swappedSecondPattern` is the member it builds.  The two
conditions never meet over one datum, so there is nothing to clash.

What the file then produces, from one `AlignedProfile` and nothing else:
`AlignedProfile.firstPattern`, `AlignedProfile.swappedSecondPattern` and
`AlignedProfile.thirdPattern`, packaged as `SwappedBundle` with
`SwappedBundle.candidates` / `candidates_valid` and the Equation (7) exit
`SwappedBundle.exists_valid_positive_exit`, and at a real profile
`alignedProfileOfLeafPair` / `exists_alignedProfile` / `nonempty_swappedBundle`.

## What is *not* the same as M-kk

`AlignedProfile` is **not** unconditionally inhabited, and cannot be:
`nonempty_swappedBundle_iff_aligned` proves that the swapped Figure 33 bundle
exists over a given `w2M1k` datum **exactly when** `p₀ = p₁`, the forward
direction being `firstPattern_forces_aligned` itself.  Alignment is a genuine
condition on the datum, not a forced consequence of the shape, which is the one
structural difference from M-kk, where `GlobalMkk.PinnedProfile` is inhabited
unconditionally.

It is, however, a *gauge* condition and not an obstruction:
`exists_aligned_gauge` shows that **every** `w2M1k` profile, aligned or not,
has a branch-swapped datum -- valid whenever the original is -- on which both
wall directions isolate one and the same sheet.  Instantiating the non-aligned
case as well needs the transport of `SecondEquation.W2SourceInput` and
`W2R2SourceProfile.SourceProfile` along that swap, which is not done here;
`W2SourceTransport` supplies it (`W2SourceTransport.exists_gauge_swappedBundle`).

## The separation is discharged, not carried

`W2M1kSourceCandidates.branchSwapped_block_fixed`, `branchSwap_aligns` and
`branchSwap_separates` all carry `hSeparated`, because none of them has
`graph_connected target` or `genus target = 0` in scope.  This file does, so
`separated` discharges it once through
`Infrastructure.TargetSeparation.edgeMoved_eq_false` -- as
`GlobalMkk.PinnedProfile.rightExternal_fixed` does -- and
`branchSwapped_block_fixed_of_genus_zero`, `branchSwap_aligns_of_genus_zero`
and `branchSwap_separates_of_genus_zero` restate all three without it.

-/

namespace DraismaVargas.LocalCases.W2M1kSwapped

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W2R1Target SecondEquation
open GlobalM11Arbitrary BalancedGlobal
open W2M1kSourceCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {geometry : GlobalM1k.Geometry data wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-! ## The negative, kept -/

/-- **`no_common_geometry`, restated on the whole unswapped bundle.**  The
hypotheses are exactly the three patterns `GlobalM1k.candidates` and
`GlobalM1k.exists_valid_positive_exit` take over one `data` and one `Geometry`,
so this says in one line that *that* bundle is empty at an actual `w2M1k`
profile and that every positive result below has to be about the swapped one.
The proof is `no_common_geometry` verbatim -- confirming that the swapped
construction of `GlobalM1k` leaves the negative result intact. -/
theorem no_common_patterns (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall)
    (hRelFirst : (data.vertexPartition wall).Rel block.1 geometry.first)
    (first : GlobalM1k.FirstPattern geometry)
    (second : GlobalM1k.SecondPattern geometry)
    (_third : GlobalM1k.ThirdPattern geometry) : False :=
  no_common_geometry shape geometry hRelFirst first second

/-! ## The separation, discharged -/

/-- A labelled wall occurrence is incident to the wall, in the shape
`TargetSeparation` consumes. -/
theorem star_incident (star : TwoStar target wall) (label : Fin 2) :
    ((star.edge label : target.V × target.V).1 = wall ∨
      (star.edge label : target.V × target.V).2 = wall) := by
  simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
    true_and] using star.edge_mem_incidentEdges label

/-- The two labelled wall occurrences are distinct. -/
theorem star_edge_one_ne_zero (star : TwoStar target wall) :
    star.edge 1 ≠ star.edge 0 := fun hEq ↦
  (by decide : (1 : Fin 2) ≠ 0) (star.edge_injective hEq)

/-- **The carried hypothesis `hSeparated`, discharged.**  On a connected
genus-zero target the branch at the `t₃` occurrence does not move the `t₂`
occurrence.  This is `TargetSeparation.edgeMoved_eq_false`, applied at
`M11RemoteCandidates.branchRoot star 1`, which is
`TargetSeparation.farEndpoint wall (star.edge 1)` with the `TwoStar` packaging
put back on. -/
theorem separated (star : TwoStar target wall)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    TargetBranchRegion.edgeMoved wall (M11RemoteCandidates.branchRoot star 1)
        (M11RemoteCandidates.branchRoot_ne star 1) (star.edge 0) = false :=
  TargetSeparation.edgeMoved_eq_false hConnected hGenus (star_incident star 1)
    (star_incident star 0) (star_edge_one_ne_zero star)

/-- `W2M1kSourceCandidates.branchSwapped_block_fixed` with `hSeparated` gone. -/
theorem branchSwapped_block_fixed_of_genus_zero (shape : Shape profile)
    (p q : Fin degree) (hTogether : (data.vertexPartition wall).Rel p q)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ((SwappedDatum data wall (M11RemoteCandidates.branchRoot star 1)
        (M11RemoteCandidates.branchRoot_ne star 1) p q hTogether).edgePartition
      (star.edge 0)).block (pinSheet profile 0) = {pinSheet profile 0} :=
  branchSwapped_block_fixed shape p q hTogether (separated star hConnected hGenus)

/-- `W2M1kSourceCandidates.branchSwap_aligns` with `hSeparated` gone. -/
theorem branchSwap_aligns_of_genus_zero (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0) (label : Fin 2) :
    ((SwappedDatum data wall (M11RemoteCandidates.branchRoot star 1)
          (M11RemoteCandidates.branchRoot_ne star 1) (pinSheet profile 0)
          (pinSheet profile 1)
          ((pinSheet_rel 0).symm.trans (pinSheet_rel 1))).edgePartition
        (star.edge label)).block (pinSheet profile 0) = {pinSheet profile 0} :=
  branchSwap_aligns shape (separated star hConnected hGenus) label

/-- `W2M1kSourceCandidates.branchSwap_separates` with `hSeparated` gone. -/
theorem branchSwap_separates_of_genus_zero (shape : Shape profile)
    (hAligned : pinSheet profile 0 = pinSheet profile 1) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (hNe : pinSheet profile 0 ≠ other)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ((SwappedDatum data wall (M11RemoteCandidates.branchRoot star 1)
          (M11RemoteCandidates.branchRoot_ne star 1) (pinSheet profile 0) other
          hOther).edgePartition (star.edge 0)).block (pinSheet profile 0) =
        {pinSheet profile 0} ∧
      ((SwappedDatum data wall (M11RemoteCandidates.branchRoot star 1)
          (M11RemoteCandidates.branchRoot_ne star 1) (pinSheet profile 0) other
          hOther).edgePartition (star.edge 1)).block other = {other} ∧
      pinSheet profile 0 ≠ other :=
  branchSwap_separates shape hAligned other hOther hNe
    (separated star hConnected hGenus)

/-- **Alignment is a gauge condition, not an obstruction.**  Every `w2M1k`
profile -- aligned or not -- has a branch-swapped datum, valid whenever the
original is, on which *both* wall directions isolate one and the same sheet of
the distinguished block.  When the profile is already aligned the transposition
is the identity and the statement is the original pinning. -/
theorem exists_aligned_gauge (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ∃ (root : target.V) (hRoot : root ≠ wall) (p q : Fin degree)
      (hTogether : (data.vertexPartition wall).Rel p q),
      (SwappedDatum data wall root hRoot p q hTogether).Valid ∧
        ∀ label : Fin 2,
          ((SwappedDatum data wall root hRoot p q hTogether).edgePartition
            (star.edge label)).block (pinSheet profile 0) = {pinSheet profile 0} :=
  ⟨M11RemoteCandidates.branchRoot star 1, M11RemoteCandidates.branchRoot_ne star 1,
    pinSheet profile 0, pinSheet profile 1, (pinSheet_rel 0).symm.trans (pinSheet_rel 1),
    branchSwapped_valid input _ _ _ _ _,
    branchSwap_aligns_of_genus_zero shape hConnected hGenus⟩

/-! ## The gauge move this file takes -/

/-- The datum branch-swapped across the `t₃` branch, transposing the
distinguished sheet with its wall-block partner.  The `t₂` occurrence partition
is fixed by the swap and the `t₃` one is relabelled, which is exactly the
exchange `M⁽¹⁾`-condition ↦ `M⁽²⁾`-condition. -/
noncomputable abbrev swappedData (star : TwoStar target wall)
    (geometry : GlobalM1k.Geometry data wall) : GluingDatum target degree :=
  SwappedDatum data wall (M11RemoteCandidates.branchRoot star 1)
    (M11RemoteCandidates.branchRoot_ne star 1) geometry.first geometry.second
    geometry.first_second

/-- The selected `1,k` wall block of `swappedData`: the same block, since the
swap fixes the wall partition (`GlobalM1k.swappedDatum_vertexPartition_wall`). -/
abbrev swappedGeometry (star : TwoStar target wall)
    (geometry : GlobalM1k.Geometry data wall) :
    GlobalM1k.Geometry (swappedData star geometry) wall :=
  geometry.swapped (M11RemoteCandidates.branchRoot star 1)
    (M11RemoteCandidates.branchRoot_ne star 1) geometry.first geometry.second
    geometry.first_second

/-! ## The profile the swapped bundle needs -/

/-- **The M-1k analogue of `GlobalMkk.PinnedProfile`.**  The split background of
the leaf member, whose fresh trivalent endpoint carries *both* old wall
occurrences (`splitLeft`, `splitRight`), together with the single exterior
condition `M⁽¹⁾` imposes: each wall direction's occurrence partition isolates
the distinguished sheet.  Stated once per direction, that pair of fields is
precisely Base I.a's `p₀ = p₁`.

There is deliberately **no** second exterior condition.  `M⁽²⁾`'s Base II.2.2.M
distinctness is not a field here; it is derived from these two across the gauge
move in `swappedSecondPattern`, which is why this bundle is satisfiable where
`GlobalM1k.candidates`' is not. -/
structure AlignedProfile (star : TwoStar target wall)
    (geometry : GlobalM1k.Geometry data wall) where
  /-- Figure 33's `M⁽¹⁾` background: every other wall block grows a leaf arm. -/
  split : Background data wall geometry.first
  /-- The new leaf carries no old wall occurrence. -/
  splitLeft : split.leftEdges = []
  /-- Both old wall occurrences go to the fresh trivalent endpoint. -/
  splitRight : split.rightEdges = [star.edge 0, star.edge 1]
  /-- The `t₂` direction isolates the distinguished sheet. -/
  leftPinned :
    (data.edgePartition (star.edge 0)).block geometry.first = {geometry.first}
  /-- The `t₃` direction isolates the *same* sheet: this and `leftPinned`
  together are `p₀ = p₁`. -/
  rightPinned :
    (data.edgePartition (star.edge 1)).block geometry.first = {geometry.first}

namespace AlignedProfile

/-- With no old wall occurrence on the retained side, every wall occurrence is
on the fresh one. -/
theorem right_eq_true (aligned : AlignedProfile star geometry) (label : Fin 2) :
    aligned.split.right (star.edge label) = true := by
  have hEmpty : wallEdgesAssigned target wall aligned.split.right false = ∅ := by
    have hList := aligned.split.leftEdges_eq
    rw [aligned.splitLeft, Multiset.coe_nil] at hList
    exact Finset.val_eq_zero.mp hList.symm
  by_contra hFalse
  have hMem : star.edge label ∈
      wallEdgesAssigned target wall aligned.split.right false :=
    (mem_wallEdgesAssigned target wall aligned.split.right false _).mpr
      ⟨star_incident star label, by simpa using hFalse⟩
  rw [hEmpty] at hMem
  exact absurd hMem (Finset.notMem_empty _)

/-- **Member 1**, Figure 33's `M⁽¹⁾`, over the original datum.  Both directions
refine the same detachment, which is the whole content of Base I.a. -/
noncomputable def firstPattern (aligned : AlignedProfile star geometry) :
    GlobalM1k.FirstPattern geometry where
  background := aligned.split
  firstExternal := star.edge 0
  secondExternal := star.edge 1
  leftEdges := aligned.splitLeft
  rightEdges := aligned.splitRight
  exterior := by
    intro edge hAt
    obtain ⟨label, rfl⟩ := exists_label star edge (by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hAt)
    have hBlock : (data.edgePartition (star.edge label)).block geometry.first =
        {geometry.first} := by
      have hLabel : label = 0 ∨ label = 1 := by omega
      rcases hLabel with rfl | rfl
      · exact aligned.leftPinned
      · exact aligned.rightPinned
    rw [aligned.right_eq_true label]
    exact SheetPartition.refines_detachSheet_of_block_singleton
      (data.edgePartition (star.edge label)) (data.vertexPartition wall)
      geometry.first geometry.second geometry.first_ne_second geometry.first_second
      (star.edgePartition_refines_wall data label) hBlock

/-- **Member 3**, Figure 33's `M⁽³⁾`, over the original datum.  It imposes no
occurrence condition at all. -/
noncomputable def thirdPattern (_aligned : AlignedProfile star geometry) :
    GlobalM1k.ThirdPattern geometry :=
  joinedPattern star geometry

/-- The gauge move does not touch the `t₂` branch, so that direction still
isolates the distinguished sheet.  This is where `separated` -- and with it
`graph_connected target` and `genus target = 0` -- is the *only* thing used
beyond `leftPinned`. -/
theorem swappedData_block_zero (aligned : AlignedProfile star geometry)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ((swappedData star geometry).edgePartition (star.edge 0)).block geometry.first =
      {geometry.first} := by
  have hEdge : (swappedData star geometry).edgePartition (star.edge 0) =
      data.edgePartition (star.edge 0) :=
    branchSwapped_edgePartition_of_fixed (M11RemoteCandidates.branchRoot star 1)
      (M11RemoteCandidates.branchRoot_ne star 1) geometry.first geometry.second
      geometry.first_second (star.edge 0) (separated star hConnected hGenus)
  rw [hEdge]
  exact aligned.leftPinned

/-- The gauge move relabels the `t₃` branch by the transposition, so that
direction isolates `geometry.second` afterwards.  No target hypothesis is used:
the swap always moves the occurrence it is taken across. -/
theorem swappedData_block_one (aligned : AlignedProfile star geometry) :
    ((swappedData star geometry).edgePartition (star.edge 1)).block geometry.second =
      {geometry.second} := by
  have hEdge : (swappedData star geometry).edgePartition (star.edge 1) =
      (data.edgePartition (star.edge 1)).relabel
        (Equiv.swap geometry.first geometry.second) :=
    branchSwapped_edgePartition_of_moved (M11RemoteCandidates.branchRoot star 1)
      (M11RemoteCandidates.branchRoot_ne star 1) geometry.first geometry.second
      geometry.first_second (star.edge 1) (edgeMoved_self (star := star) 1)
  rw [hEdge]
  have hImage := SheetPartition.relabel_block (data.edgePartition (star.edge 1))
    (Equiv.swap geometry.first geometry.second) geometry.first
  rw [aligned.rightPinned, Equiv.swap_apply_left] at hImage
  simpa using hImage

/-- **Base II.2.2.M, derived rather than carried.**  This is the whole point of
the file.  Over the original datum `M⁽²⁾`'s requirement -- the two wall
directions isolate *distinct* sheets -- is the direct negation of the
`AlignedProfile` conditions.  Over the branch-swapped datum it is their
*consequence*: `t₂` keeps isolating `geometry.first`, `t₃` now isolates
`geometry.second`, and those are distinct because a `GlobalM1k.Geometry` says
so.  Nothing was assumed twice, and no `p₀ ≠ p₁` field appears anywhere. -/
theorem swapped_pins_ne (aligned : AlignedProfile star geometry)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ((swappedData star geometry).edgePartition (star.edge 0)).block geometry.first =
        {geometry.first} ∧
      ((swappedData star geometry).edgePartition (star.edge 1)).block geometry.second =
        {geometry.second} ∧
      geometry.first ≠ geometry.second :=
  ⟨aligned.swappedData_block_zero hConnected hGenus, aligned.swappedData_block_one,
    geometry.first_ne_second⟩

/-- **Member 2**, Figure 33's `M⁽²⁾`, over the branch-swapped datum -- the
instantiation `GlobalM1k.exists_valid_positive_exit_swapped` needs.
Its two exterior conditions are the two halves of `swapped_pins_ne`, so both
come from the one `AlignedProfile` that already produced member 1, and no
hypothesis beyond the target being a connected genus-zero graph is added. -/
noncomputable def swappedSecondPattern (aligned : AlignedProfile star geometry)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    GlobalM1k.SecondPattern (swappedGeometry star geometry) where
  background := M11SourceCandidates.joinedBackground (swappedData star geometry)
    star geometry.first
  leftExternal := star.edge 0
  rightExternal := star.edge 1
  leftEdges := rfl
  rightEdges := rfl
  exterior := by
    intro edge hAt
    obtain ⟨label, rfl⟩ := exists_label star edge (by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hAt)
    have hLabel : label = 0 ∨ label = 1 := by omega
    rcases hLabel with rfl | rfl
    · split_ifs with hRight
      · exact absurd (hRight.symm.trans star.right_edge_zero) (by simp)
      · exact SheetPartition.refines_detachSheet_of_block_singleton
          ((swappedData star geometry).edgePartition (star.edge 0))
          ((swappedData star geometry).vertexPartition wall)
          (swappedGeometry star geometry).first (swappedGeometry star geometry).second
          (swappedGeometry star geometry).first_ne_second
          (swappedGeometry star geometry).first_second
          (star.edgePartition_refines_wall (swappedData star geometry) 0)
          (aligned.swappedData_block_zero hConnected hGenus)
    · split_ifs with hRight
      · exact SheetPartition.refines_detachSheet_of_block_singleton
          ((swappedData star geometry).edgePartition (star.edge 1))
          ((swappedData star geometry).vertexPartition wall)
          (swappedGeometry star geometry).second (swappedGeometry star geometry).first
          (swappedGeometry star geometry).first_ne_second.symm
          (swappedGeometry star geometry).first_second.symm
          (star.edgePartition_refines_wall (swappedData star geometry) 1)
          aligned.swappedData_block_one
      · exact absurd star.right_edge_one hRight

end AlignedProfile

/-! ## The bundle, inhabited -/

/-- The hypothesis bundle of `GlobalM1k.exists_valid_positive_exit_swapped`,
packaged: members 1 and 3 over `data`, member 2 over one branch-swapped datum.
Compare `no_common_patterns`, which says the *unswapped* bundle of
`GlobalM1k.exists_valid_positive_exit` has no instance at a real profile. -/
structure SwappedBundle (geometry : GlobalM1k.Geometry data wall) where
  /-- The root of the branch the gauge move is taken across. -/
  root : target.V
  root_ne : root ≠ wall
  /-- The two sheets the gauge move transposes. -/
  p : Fin degree
  q : Fin degree
  together : (data.vertexPartition wall).Rel p q
  first : GlobalM1k.FirstPattern geometry
  second : GlobalM1k.SecondPattern (geometry.swapped root root_ne p q together)
  third : GlobalM1k.ThirdPattern geometry

namespace SwappedBundle

/-- The three globally assembled Figure 33 candidates, member 2 included
although it is built over the branch-swapped datum. -/
noncomputable def candidates (bundle : SwappedBundle geometry) :
    Fin 3 → CertifiedCandidate data :=
  GlobalM1k.swappedCandidates geometry bundle.root bundle.root_ne bundle.p bundle.q
    bundle.together bundle.first bundle.second bundle.third

/-- Each of the three is a valid outgoing datum as soon as the incoming one is:
the branch swap preserves validity, and blockwise assembly preserves it again. -/
theorem candidates_valid (bundle : SwappedBundle geometry) (hValid : data.Valid)
    (index : Fin 3) : (bundle.candidates index).datum.Valid :=
  (bundle.candidates index).valid_of_old hValid

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **Equation (7)'s positive exit for case M-1k with no assumed patterns.**
The M-1k mirror of `GlobalMkk.exists_valid_positive_exit_pinned`: the three
Figure 33 members come from the bundle, the second over the branch-swapped
datum, and only the length-matrix hypotheses remain.  The determinant
coefficients are `GlobalM1k.exists_valid_positive_exit_swapped`'s own -- nothing
is transcribed from Part I's display of Equation (7) here. -/
theorem exists_valid_positive_exit (bundle : SwappedBundle geometry)
    (matrix : Fin 3 → Matrix coordinate coordinate ℚ)
    (wallColumn : coordinate) (c₁ c₂ c₃ s : ℚ)
    (hdet : ∀ i, (matrix i).det =
      ![2 * c₁,
        c₁ + c₂ / ((geometry.k : ℚ) - 1) + s,
        c₃ / ((geometry.k : ℚ) + 1) + s] i)
    (hleft : c₁ + c₂ / (geometry.k : ℚ) + s = 0)
    (hright : c₃ / (geometry.k : ℚ) + s = 0)
    (hAgree : ∀ i j, AgreeOffColumn (matrix i) (matrix j) wallColumn)
    (hValid : data.Valid) (incoming : Fin 3)
    (hincoming : (matrix incoming).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin 3 → coordinate → ℚ)
    (hz : z wallColumn = 0)
    (hzpos : ∀ i, i ≠ wallColumn → 0 < z i)
    (hSystems : ∀ outgoing,
      (matrix incoming).mulVec incomingVelocity =
        (matrix outgoing).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity wallColumn < 0) :
    ∃ outgoing,
      (bundle.candidates outgoing).datum.Valid ∧
      (matrix incoming).det * (matrix outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (matrix outgoing).mulVec
            (z + t • outgoingVelocity outgoing) =
          (matrix incoming).mulVec z +
            t • (matrix incoming).mulVec incomingVelocity :=
  GlobalM1k.exists_valid_positive_exit_swapped geometry bundle.root bundle.root_ne
    bundle.p bundle.q bundle.together bundle.first bundle.second bundle.third
    matrix wallColumn c₁ c₂ c₃ s hdet hleft hright hAgree hValid incoming hincoming
    z incomingVelocity outgoingVelocity hz hzpos hSystems hIncomingDirection

end SwappedBundle

/-- **The bundle built from one `AlignedProfile`.**  No pattern is assumed; all
three are constructed, and the only target hypotheses are connectedness and
genus zero, used solely to discharge the branch separation. -/
noncomputable def AlignedProfile.swappedBundle (aligned : AlignedProfile star geometry)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    SwappedBundle geometry where
  root := M11RemoteCandidates.branchRoot star 1
  root_ne := M11RemoteCandidates.branchRoot_ne star 1
  p := geometry.first
  q := geometry.second
  together := geometry.first_second
  first := aligned.firstPattern
  second := aligned.swappedSecondPattern hConnected hGenus
  third := aligned.thirdPattern

/-! ## At an actual `w2M1k` source profile -/

/-- **An aligned profile has an `AlignedProfile`.**  Everything is read off the
profile: the background is the M-1k split background at the pinned sheet, and
the two exterior conditions are the two directions' own `pinSheet_block`, made
to speak about one sheet by `LeafPair.aligned`. -/
noncomputable def alignedProfileOfLeafPair (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) :
    AlignedProfile star (pair.geometry shape) where
  split := splitBackgroundAt input profile.ramification (pinSheet profile 0)
    (pinSheet_rel (profile := profile) 0)
  splitLeft := rfl
  splitRight := rfl
  leftPinned := pinSheet_block shape 0
  rightPinned := by
    have hBlock := pinSheet_block shape 1
    rw [← pair.aligned] at hBlock
    exact hBlock

/-- The geometry a `w2M1k` `Shape` determines, with its `AlignedProfile`: the
leaf geometry at the pinned sheet, whose `k` is the shape's own. -/
theorem exists_alignedProfile (input : W2SourceInput data star) (shape : Shape profile)
    (hAligned : pinSheet profile 0 = pinSheet profile 1) :
    ∃ geometry : GlobalM1k.Geometry data wall,
      (data.vertexPartition wall).Rel block.1 geometry.first ∧
        geometry.k = shape.k ∧ Nonempty (AlignedProfile star geometry) := by
  obtain ⟨pair⟩ := exists_leafPair shape hAligned
  exact ⟨pair.geometry shape, pinSheet_rel (profile := profile) 0, rfl,
    ⟨alignedProfileOfLeafPair input shape pair⟩⟩

/-- **The headline.**  At an actual aligned `w2M1k` source profile on a
connected genus-zero target all three Figure 33 members exist -- members 1 and 3
over the profile's own datum, member 2 over the branch-swapped one -- so the
hypothesis bundle of `GlobalM1k.exists_valid_positive_exit_swapped` is
nonempty, and each member is valid whenever the profile's datum is. -/
theorem nonempty_swappedBundle (input : W2SourceInput data star) (shape : Shape profile)
    (hAligned : pinSheet profile 0 = pinSheet profile 1)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    ∃ geometry : GlobalM1k.Geometry data wall,
      (data.vertexPartition wall).Rel block.1 geometry.first ∧
        geometry.k = shape.k ∧
        ∃ bundle : SwappedBundle geometry,
          ∀ index, data.Valid → (bundle.candidates index).datum.Valid := by
  obtain ⟨geometry, hRel, hk, ⟨aligned⟩⟩ := exists_alignedProfile input shape hAligned
  exact ⟨geometry, hRel, hk, aligned.swappedBundle hConnected hGenus,
    fun index hValid ↦ SwappedBundle.candidates_valid _ hValid index⟩

/-- **The sharp form, and the one structural difference from M-kk.**  The
swapped Figure 33 bundle exists over a given `w2M1k` datum **exactly when** the
two wall directions pin the same sheet.  The forward direction is
`firstPattern_forces_aligned`: member 1 lives over the unswapped datum in
`GlobalM1k.swappedCandidates`, so Base I.a is not negotiable there.  Unlike
`GlobalMkk.PinnedProfile`, an `AlignedProfile` is therefore *not* free; by
`exists_aligned_gauge` the condition is nevertheless reachable by a gauge
move from any profile. -/
theorem nonempty_swappedBundle_iff_aligned (input : W2SourceInput data star)
    (shape : Shape profile) (hConnected : graph_connected target)
    (hGenus : genus target = 0) :
    (∃ geometry : GlobalM1k.Geometry data wall,
        (data.vertexPartition wall).Rel block.1 geometry.first ∧
          Nonempty (SwappedBundle geometry)) ↔
      pinSheet profile 0 = pinSheet profile 1 := by
  constructor
  · rintro ⟨geometry, hRel, ⟨bundle⟩⟩
    exact firstPattern_forces_aligned shape geometry hRel bundle.first
  · intro hAligned
    obtain ⟨geometry, hRel, _, ⟨aligned⟩⟩ := exists_alignedProfile input shape hAligned
    exact ⟨geometry, hRel, ⟨aligned.swappedBundle hConnected hGenus⟩⟩

end DraismaVargas.LocalCases.W2M1kSwapped
