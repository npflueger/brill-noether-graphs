module

public import DraismaVargasCount.DegenerateRealizationImage
public import Utilities.Subdivision.OneEdgeSplitRefinement
public import DraismaVargasCount.DegenerateTransport
public import DraismaVargasCount.WitnessAssembly

@[expose] public section

/-!
# The endgame: rank one from a marker-free set, and the genus-six witness

This module is the endgame of the genus-six assembly (step 5 of `Assembly`):
`witness_of_c34_and_markerFreePencilCover` derives the genus-six odd-subdivision witness from
`CountSchedule.C34 2` and `MarkerFreePencilCoverSupply`, and `Assembly` applies it with
`Assembly.c34_genusSix` and `PencilTransportProducer.markerFreePencilCoverSupply`.

## The setting

A connected genus-six graph is reduced to a small specification `small` whose cubic model
`D.bigCore` is described by an expansion datum `D` (`ExpansionData`).  By
`ClosedBoundaryMember.genusSix_exists_closed_hasOddMult_of_nonneg` the fibre over the
degenerate request of `D.bigCore` has a closed member of odd multiplicity, and
`DegenerateBigDivisor.bnExists_of_degenerateMember` turns it into Brill--Noether existence on
an odd regular subdivision, given `ForestContractionRank`: rank at least one of the member's
pencil, pushed to the small side.  This module proves `ForestContractionRank` from a covering
statement about the pencil.

## Markers

When `D` has a `double` slot (a loop of the small core, displayed through a bivalent marker),
the marker `small.core.head j₁` **is** one of the `n` core vertices of the small
specification, and it need not be reached by the member's pencil:

* `marker_reached_iff` — the marker is reached iff the member's own row over the
  `double` slot has an interior address at oriented offset **exactly**
  `k * small.length j₁`.  Every other core vertex is reached unconditionally
  (`exists_pushDivisor_pos_fib`).
* That is a coincidence: the placement reads the target only through the slot's
  total length (`offsetVal_bigSpec_congr`), so the member cannot see where the split
  puts the marker, and a row realizes at most `rowLength - 1` offsets
  (`card_realized_le`).  §8 records a small core of this kind, in which the loop row of a
  member is folded at the loop's midpoint while the marker splits the loop `1 + 3`.

## Moving the marker, not the scale

A marker is a presentation artefact: moving it along its chain does not change the
graph.  `moveEquiv` is that `LaplacianEquiv`, built from
`OneEdgeSplitRefinement.laplacianEquivOfUnorientedUnitSteps`.  Moving each unreached
marker onto a reached vertex of its own chain and applying
`Spec.rank_ge_one_of_reaches_coreVertices` to the moved presentation gives

* `rank_ge_one_of_markerFree` — rank one from winnability at the `D.fib` images and at
  **some** vertex strictly inside each `double` chain;
* `MarkerFreePencilCover` (MPC), which asks that of the pencil, and
  `forestContractionRank_of_markerFreePencilCover`;
* `markerFreePencilCover_of_transport` — MPC from (T) (`PencilTransport`) and
  `DoubleRowInterior` (one interior address strictly inside each `double` chain);
* `MarkerFreePencilCoverSupply` — MPC for every closed odd member over every cubic connected
  genus-six expansion, with one premise `LoopDoubles` (every `double` displays a loop), which
  the data of the cubic-model reduction satisfy (`loopDoubles_data`,
  `exists_expansionModel_loopDoubles`, `exists_supplyInstance_of_c34_loopDoubles`); its
  consumer `exists_odd_bnExists_of_markerFreePencilCoverSupply`; the assembly
  `witness_of_c34_and_markerFreePencilCover`; and the producer
  `markerFreePencilCoverSupply_of_transport_doubleRowInterior`.

No change of scale is needed.  (The metric fibre through the marker would become
integral only at scale `c * k` with `c ∈ {1, 2, 3}`, since the indices over one target
edge sum to four; the placement is pinned to `k = memberScale member` by
`DegenerateBigDivisor.exact`, so the endgame could not absorb that change without new
placement work.  This remark is argued, not formalized; moving the marker makes it moot.)

## What is proved

§1 marker geometry of `ExpansionData` (`pathVertex_eq_coreVertex_iff`, `fib_ne_marker`,
`marker_or_exists_fib`, `kindVertex_eq_marker_iff`); §2 what the pencil reaches
(`realization`, `pushDivisor_pos_iff`, `exists_pushDivisor_pos_iff`,
`exists_pushDivisor_pos_fib`, `marker_reached_iff`); §3 the offsets a row realizes
(`RowOffsetRealized`, `card_realized_le`, `offsetVal_mem_Ioo_iff_general`,
`offsetVal_eq_of_midpoint`, `offsetVal_bigSpec_congr`, `rowOffsetRealized_bigSpec_congr`);
§4 the marker move (`MarkerPair`, `chainVertex`, `moveSpec`, `moveVertex`, `moveStep`,
`MoveHyp`, `moveEquiv`); §5 `rank_ge_one_of_markerFree`; §6 the marker-free cover
(`PencilTransport`, `pencilTransport_of_adjacent`, `pencilTransport_of_pencilTransport`,
`DoubleRowInterior`, `LoopDoubles`, `MarkerFreePencilCover` and its three theorems,
`offsetVal_mem_Ioo_iff`); §7 the assemblies at the level of
`DegenerateBigDivisor.bnExists_of_degenerateMember`; §8 the example small core `Seed57Loop`;
§9 the supply layer and the final assembly.

## What is not proved here

* **(T), `PencilTransport`, and `DoubleRowInterior` are hypotheses here.**  Both are proved
  in `PencilTransportProducer` (`PencilTransportProducer.pencilTransport`,
  `PencilTransportProducer.doubleRowInterior_of_loopDoubles`), which assembles
  `PencilTransportProducer.markerFreePencilCoverSupply` through
  `markerFreePencilCoverSupply_of_transport_doubleRowInterior`.
  `pencilTransport_of_adjacent` reduces (T) to the two ends of each target edge.
* **`LoopDoubles` is a premise of `MarkerFreePencilCoverSupply`.**  Argued, not
  formalized: without it the supply could fail.  Take a core with a slot split by a
  non-loop marker whose row is a single occurrence: then no pencil member reaches the open
  chain.  A non-loop marker is not needed for rank (Luo), but the `Spec`-based criterion
  here cannot drop it without a merge.
* **`small.core.Connected`** stays a hypothesis of the non-supply theorems; the supply
  carries it as a premise, discharged in the final assembly by
  `WitnessAssembly.coreConnected_unitSpec`.
-/

namespace DraismaVargas.Count.CorePencilCoverProducer

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases W4StableSource FullDimensionalSource
open StableGraphIncidence
open DraismaVargas.Count.DegenerateBigDivisor
open DraismaVargas.Count.DegenerateFibreCover
open DraismaVargas.Count.DegenerateRealizationImage
open CanonicalSurvivor PendantRetraction RowRealizedPosition
open SurvivingSlotMap SlotMoment
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Subdivision.CoreExpansion

/-! ## 1.  Marker geometry of an expansion datum -/

section MarkerGeometry

variable {n p N Q : ℕ}

/-- A path vertex of a subdivision is a core vertex exactly at the two ends of
its slot. -/
theorem pathVertex_eq_coreVertex_iff (S : Spec n p) (j : Fin p) (t : S.PathPosition j)
    (v : Fin n) :
    S.pathVertex j t = S.coreVertex v ↔
      (t.val = 0 ∧ S.core.tail j = v) ∨ (t.val = S.length j ∧ S.core.head j = v) := by
  have hpos := S.length_pos j
  unfold Spec.pathVertex
  by_cases h0 : t.val = 0
  · rw [dite_eq_left h0]
    simp only [Spec.coreVertex, Sum.inl.injEq, h0, true_and]
    constructor
    · exact Or.inl
    · rintro (h | ⟨h, _⟩)
      · exact h
      · omega
  · rw [dite_eq_right h0]
    by_cases hl : t.val = S.length j
    · rw [dite_eq_left hl]
      simp only [Spec.coreVertex, Sum.inl.injEq]
      constructor
      · exact fun h ↦ Or.inr ⟨hl, h⟩
      · rintro (⟨h, _⟩ | ⟨_, h⟩)
        · exact absurd h h0
        · exact h
    · rw [dite_eq_right hl]
      simp only [Spec.interiorVertex, Spec.coreVertex, reduceCtorEq, false_iff, not_or,
        not_and]
      exact ⟨fun h ↦ absurd h h0, fun h ↦ absurd h hl⟩

variable {D : ExpansionData n p N Q} {C : Utilities.Certificate.ExplicitPotential.Core n p}

/-- The marker of a `double` slot is not the image of any big core vertex. -/
theorem fib_ne_marker (hCond : D.Conditions C) {e : Fin Q} {j₁ j₂ : Fin p}
    (hk : D.kind e = SlotKind.double j₁ j₂) (v : Fin N) : D.fib v ≠ C.head j₁ :=
  (ExpansionData.marker_of_conditions hCond e j₁ j₂ hk).1 v

/-- **Every small core vertex is a `D.fib` image or a marker.**  The dichotomy of
`LocalCases.RetainedFibre.isMarker_or_exists_fib`, re-proved here at an arbitrary
core so that this file does not import the retained-fibre layer. -/
theorem marker_or_exists_fib (hCond : D.Conditions C) (w : Fin n) :
    (∃ (e : Fin Q) (j₁ j₂ : Fin p), D.kind e = SlotKind.double j₁ j₂ ∧ C.head j₁ = w) ∨
      ∃ v : Fin N, D.fib v = w := by
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

/-- **Where a `kindVertex` can land on a marker.**  At the marker of the `double`
slot `e`, and only there: the contraction of any other big slot, or of `e` at
any other offset, is a different vertex of the small subdivision.  `S` is any
specification on the small core, so that the statement applies verbatim to
`small.scale k hk`. -/
theorem kindVertex_eq_marker_iff (S : Spec n p) (hCond : D.Conditions S.core)
    {e : Fin Q} {j₁ j₂ : Fin p} (hk : D.kind e = SlotKind.double j₁ j₂)
    (e' : Fin Q) (q : ℕ) :
    kindVertex S (D.fib (D.bigCore.tail e')) (D.kind e') q =
        S.coreVertex (S.core.head j₁) ↔
      e' = e ∧ q = S.length j₁ := by
  have hComp := ExpansionData.compatible_of_conditions hCond e'
  constructor
  · intro h
    cases hk' : D.kind e' with
    | contracted =>
        rw [hk'] at h
        change S.coreVertex (D.fib (D.bigCore.tail e')) = S.coreVertex (S.core.head j₁) at h
        exact absurd (Sum.inl.inj h) (fib_ne_marker hCond hk _)
    | single j =>
        rw [hk'] at h
        change S.pathVertex j ⟨min q (S.length j), by omega⟩ =
          S.coreVertex (S.core.head j₁) at h
        obtain ⟨hT, hH⟩ := hComp.2.1 j hk'
        rcases (pathVertex_eq_coreVertex_iff S j _ _).mp h with ⟨_, ht⟩ | ⟨_, hh⟩
        · exact absurd (hT.trans ht) (fib_ne_marker hCond hk _)
        · exact absurd (hH.trans hh) (fib_ne_marker hCond hk _)
    | double a b =>
        rw [hk'] at h
        obtain ⟨hT, -, hH⟩ := hComp.2.2 a b hk'
        by_cases hq : q ≤ S.length a
        · rw [kindVertex_double_le a b _ hq] at h
          rcases (pathVertex_eq_coreVertex_iff S a _ _).mp h with ⟨_, ht⟩ | ⟨hlen, hh⟩
          · exact absurd (hT.trans ht) (fib_ne_marker hCond hk _)
          · have haj : a = j₁ := (ExpansionData.marker_of_conditions hCond e j₁ j₂ hk).2 a hh
            subst haj
            have hOwner' := (ExpansionData.owner_eq_of_double hCond hk').1
            have hOwner := (ExpansionData.owner_eq_of_double hCond hk).1
            refine ⟨hOwner'.symm.trans hOwner, ?_⟩
            change min q (S.length a) = S.length a at hlen
            omega
        · rw [kindVertex_double_gt a b _ hq] at h
          rcases (pathVertex_eq_coreVertex_iff S b _ _).mp h with ⟨h0, _⟩ | ⟨_, hh⟩
          · change min (q - S.length a) (S.length b) = 0 at h0
            have := S.length_pos b
            omega
          · exact absurd (hH.trans hh) (fib_ne_marker hCond hk _)
  · rintro ⟨rfl, rfl⟩
    rw [hk, kindVertex_double_le j₁ j₂ _ le_rfl]
    exact (pathVertex_eq_coreVertex_iff S j₁ _ _).mpr (Or.inr ⟨by simp, rfl⟩)

end MarkerGeometry

/-! ## 2.  The pencil at the core vertices: what it reaches, exactly -/

section Reach

variable {n p N Q degree : ℕ}
  (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)
  (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) degree)
  (hClosed : member.Closed) (hScale : memberScale member = k)

/-- The member's realization on the small subdivision: the placement followed by
the contraction.  `DegenerateBigDivisor.pushDivisor_bigDivisor` is the
statement that every pencil member is the pushforward of a pullback fibre along
this one map. -/
noncomputable def realization : member.data.SourceVertex → (small.scale k hk).Vertex :=
  ExpansionData.vertexMap D (small.scale k hk) hN hL ∘
    DegeneratePlacement.sourcePoint (D.bigSpec (small.scale k hk) hN hL)
      (degenerateLength D small) member hClosed (fit D small hN hL k hk member hScale)

/-- **Positivity of a pencil member, exactly.**  The pushed fibre over `root'` is
positive at `b` iff some source vertex over `root'` is realized at `b`. -/
theorem pushDivisor_pos_iff (root' : member.target.V) (b : (small.scale k hk).Vertex) :
    0 < ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
        (bigDivisor D small hN hL k hk member hClosed hScale root') b ↔
      ∃ raw : member.data.SourceVertex, raw.1.1 = root' ∧
        realization D small hN hL k hk member hClosed hScale raw = b := by
  classical
  rw [pushDivisor_bigDivisor, PendantDivisorTransport.push_apply,
    Finset.sum_pos_iff_of_nonneg (fun raw _ ↦ by
      split_ifs
      · exact fibre_nonneg _ _ _ _ _
      · exact le_refl 0)]
  constructor
  · rintro ⟨raw, -, hPos⟩
    split_ifs at hPos with hHit
    · refine ⟨raw, ?_, hHit⟩
      by_contra hRoot
      have hZero : DegeneratePlacement.fibre (D.bigSpec (small.scale k hk) hN hL)
          (degenerateLength D small) member root' raw = 0 := by
        show (if raw.1.1 = root' then
          ((member.data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ) else 0) = 0
        rw [ite_eq_right hRoot]
      omega
    · exact absurd hPos (lt_irrefl 0)
  · rintro ⟨raw, hRoot, hHit⟩
    refine ⟨raw, Finset.mem_univ _, ?_⟩
    split_ifs with h
    · have := one_le_fibre_self (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member raw
      rw [hRoot] at this
      omega
    · exact absurd hHit h

/-- **Some pencil member is positive at `b` iff `b` is realized.** -/
theorem exists_pushDivisor_pos_iff (b : (small.scale k hk).Vertex) :
    (∃ root' : member.target.V,
        0 < ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
          (bigDivisor D small hN hL k hk member hClosed hScale root') b) ↔
      ∃ raw : member.data.SourceVertex,
        realization D small hN hL k hk member hClosed hScale raw = b := by
  constructor
  · rintro ⟨root', hPos⟩
    obtain ⟨raw, -, hRaw⟩ :=
      (pushDivisor_pos_iff D small hN hL k hk member hClosed hScale root' b).mp hPos
    exact ⟨raw, hRaw⟩
  · rintro ⟨raw, hRaw⟩
    exact ⟨raw.1.1,
      (pushDivisor_pos_iff D small hN hL k hk member hClosed hScale raw.1.1 b).mpr
        ⟨raw, rfl, hRaw⟩⟩

/-- **Every non-marker core vertex is reached, unconditionally.**  A core vertex
in the image of `D.fib` is the realization of the member's branch vertex carrying
that label (`CoreIdentification.vertex` is an `Equiv`), so the pencil member over
that branch vertex's own target vertex has a chip there. -/
theorem exists_pushDivisor_pos_fib (a : Fin N) :
    ∃ root' : member.target.V,
      0 < ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
        (bigDivisor D small hN hL k hk member hClosed hScale root')
        ((small.scale k hk).coreVertex (D.fib a)) := by
  refine (exists_pushDivisor_pos_iff D small hN hL k hk member hClosed hScale _).mpr
    ⟨(member.ident.vertex.symm a).1, ?_⟩
  have h := vertexMap_sourcePoint_branch D small hN hL k hk member hClosed hScale
    (member.ident.vertex.symm a)
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- **The marker is reached iff the double row has an address at the marker
offset.**  For a `double` big slot `e` carrying the small slots `j₁, j₂`, the
marker `small.core.head j₁` — a genuine core vertex of `small`, bivalent, outside
the image of `D.fib` — carries a chip of some pencil member iff the member's own
row over `e` has an interior address whose oriented integral offset is exactly
`k * small.length j₁`. -/
theorem marker_reached_iff (hCond : D.Conditions small.core)
    {e : Fin Q} {j₁ j₂ : Fin p} (hk2 : D.kind e = SlotKind.double j₁ j₂) :
    (∃ root' : member.target.V,
        0 < ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
          (bigDivisor D small hN hL k hk member hClosed hScale root')
          ((small.scale k hk).coreVertex (small.core.head j₁))) ↔
      ∃ address : InteriorAddress member.fullDim,
        member.ident.row address.1 = e ∧
          DegeneratePlacement.offsetVal (D.bigSpec (small.scale k hk) hN hL)
            (degenerateLength D small) member hClosed e (address.2.val + 1) =
            k * small.length j₁ := by
  have hCond' : D.Conditions (small.scale k hk).core := hCond
  rw [exists_pushDivisor_pos_iff]
  constructor
  · rintro ⟨raw, hRaw⟩
    rcases exists_realizedVertex_of_sourceVertex D small hN hL k hk member hClosed hScale
        hCond raw with ⟨branch, hb⟩ | ⟨address, ha⟩
    · have hEq : (small.scale k hk).coreVertex (D.fib (member.ident.vertex branch)) =
          (small.scale k hk).coreVertex (small.core.head j₁) := hb.trans hRaw
      exact absurd (Sum.inl.inj hEq) (fib_ne_marker hCond hk2 _)
    · have hEq := ha.trans hRaw
      obtain ⟨hRow, hOff⟩ := (kindVertex_eq_marker_iff (small.scale k hk) hCond' hk2
        (member.ident.row address.1) _).mp hEq
      refine ⟨address, hRow, ?_⟩
      rw [← hRow]
      exact hOff
  · rintro ⟨address, hRow, hOff⟩
    refine ⟨addressVertex member.fullDim address, ?_⟩
    have h := vertexMap_sourcePoint_address D small hN hL k hk member hClosed hScale hCond
      address
    refine h.trans ((kindVertex_eq_marker_iff (small.scale k hk) hCond' hk2
      (member.ident.row address.1) _).mpr ⟨hRow, ?_⟩)
    rw [hRow]
    exact hOff

end Reach

/-! ## 3.  The offsets a row realizes: reaching a marker is a coincidence -/

section Consequences

variable {N Q degree : ℕ}

/-- **The double row carries an interior address at oriented offset `q`.**  Stated
for an arbitrary target `B` and natural request `y`, exactly as
`DegeneratePlacement.offsetVal` is, so that one member can be compared across
different small specifications. -/
def RowOffsetRealized (B : Spec N Q) (y : Fin Q → ℕ)
    (member : FibreMember B.core (fun e ↦ (y e : ℚ)) degree) (hClosed : member.Closed)
    (e : Fin Q) (q : ℕ) : Prop :=
  ∃ address : InteriorAddress member.fullDim,
    member.ident.row address.1 = e ∧
      DegeneratePlacement.offsetVal B y member hClosed e (address.2.val + 1) = q

open Classical in
/-- **At most `rowLength − 1` offsets are realized on a row.**  The offsets a row
realizes are read off its interior addresses, and there are
`(orderedRow …).length − 1` of those.  Consequently, among all candidate marker
positions `l` (scaled by `k > 0`), at most that many are realized. -/
theorem card_realized_le (B : Spec N Q) (y : Fin Q → ℕ)
    (member : FibreMember B.core (fun e ↦ (y e : ℚ)) degree) (hClosed : member.Closed)
    (e : Fin Q) {k : ℕ} (hk : 0 < k) (s : Finset ℕ) :
    (s.filter fun l ↦ RowOffsetRealized B y member hClosed e (k * l)).card ≤
      (RowWalk.orderedRow member.fullDim.pathEnds (member.ident.row.symm e)).length - 1 := by
  classical
  let g : Fin ((RowWalk.orderedRow member.fullDim.pathEnds
      (member.ident.row.symm e)).length - 1) → ℕ :=
    fun i ↦ DegeneratePlacement.offsetVal B y member hClosed e (i.val + 1) / k
  have hSub : (s.filter fun l ↦ RowOffsetRealized B y member hClosed e (k * l)) ⊆
      (Finset.univ.image g) := by
    intro l hl
    obtain ⟨-, address, hRow, hOff⟩ := Finset.mem_filter.mp hl
    obtain ⟨path, i⟩ := address
    have hPath : path = member.ident.row.symm e := by
      rw [← hRow, Equiv.symm_apply_apply]
    subst hPath
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    show DegeneratePlacement.offsetVal B y member hClosed e (i.val + 1) / k = l
    rw [hOff, Nat.mul_div_cancel_left l hk]
  refine (Finset.card_le_card hSub).trans (Finset.card_image_le.trans ?_)
  rw [Finset.card_univ, Fintype.card_fin]

/-- An oriented offset lies strictly inside its slot iff the row's own integral
prefix does: reversal is a reflection of the slot. -/
theorem offsetVal_mem_Ioo_iff_general (B : Spec N Q) (y : Fin Q → ℕ)
    (member : FibreMember B.core (fun e ↦ (y e : ℚ)) degree) (hClosed : member.Closed)
    (hFit : ∀ e : Fin Q, memberScale member * y e ≤ B.length e) (e : Fin Q) (j : ℕ) :
    (0 < DegeneratePlacement.offsetVal B y member hClosed e j ∧
      DegeneratePlacement.offsetVal B y member hClosed e j < B.length e) ↔
    (0 < integralPrefix member.fullDim (memberRealization member hClosed)
        (member.ident.row.symm e) j ∧
      integralPrefix member.fullDim (memberRealization member hClosed)
        (member.ident.row.symm e) j < B.length e) := by
  have hLe := DegeneratePlacement.integralPrefix_le B y member hClosed hFit e j
  unfold DegeneratePlacement.offsetVal
  split_ifs <;> omega

/-- A row prefix at the exact midpoint of its slot is placed at the midpoint in
either orientation. -/
theorem offsetVal_eq_of_midpoint (B : Spec N Q) (y : Fin Q → ℕ)
    (member : FibreMember B.core (fun e ↦ (y e : ℚ)) degree) (hClosed : member.Closed)
    (e : Fin Q) (j : ℕ) {P : ℕ}
    (hP : integralPrefix member.fullDim (memberRealization member hClosed)
      (member.ident.row.symm e) j = P)
    (hB : B.length e = 2 * P) :
    DegeneratePlacement.offsetVal B y member hClosed e j = P := by
  unfold DegeneratePlacement.offsetVal
  split_ifs <;> omega

variable {n p : ℕ} (D : ExpansionData n p N Q) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)

/-- **The placement does not see the split of a double.**  Two small
specifications whose scaled kind lengths agree on `e` place every row of one
member at the same offsets on `e`: `offsetVal` reads the target only through
`B.length e`.  For a `double` slot `e` this is the case for every pair of splits
`small.length j₁ + small.length j₂ = small'.length j₁ + small'.length j₂`, while
the marker offsets `k * small.length j₁` and `k * small'.length j₁` differ. -/
theorem offsetVal_bigSpec_congr (small small' : Spec n p) (e : Fin Q)
    (hLen : kindLength (small.scale k hk) (D.kind e) =
      kindLength (small'.scale k hk) (D.kind e))
    (y : Fin Q → ℕ) (member : FibreMember D.bigCore (fun e ↦ (y e : ℚ)) degree)
    (hClosed : member.Closed) (j : ℕ) :
    DegeneratePlacement.offsetVal (D.bigSpec (small.scale k hk) hN hL) y member hClosed e j =
      DegeneratePlacement.offsetVal (D.bigSpec (small'.scale k hk) hN hL) y member hClosed
        e j := by
  have hB : (D.bigSpec (small.scale k hk) hN hL).length e =
      (D.bigSpec (small'.scale k hk) hN hL).length e := hLen
  unfold DegeneratePlacement.offsetVal
  rw [hB]
  rfl

theorem rowOffsetRealized_bigSpec_congr (small small' : Spec n p) (e : Fin Q)
    (hLen : kindLength (small.scale k hk) (D.kind e) =
      kindLength (small'.scale k hk) (D.kind e))
    (y : Fin Q → ℕ) (member : FibreMember D.bigCore (fun e ↦ (y e : ℚ)) degree)
    (hClosed : member.Closed) (q : ℕ) :
    RowOffsetRealized (D.bigSpec (small.scale k hk) hN hL) y member hClosed e q ↔
      RowOffsetRealized (D.bigSpec (small'.scale k hk) hN hL) y member hClosed e q := by
  unfold RowOffsetRealized
  simp only [offsetVal_bigSpec_congr D hN hL k hk small small' e hLen y member hClosed]

variable (small : Spec n p)
  (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) degree)
  (hClosed : member.Closed) (hScale : memberScale member = k)

end Consequences


/-! ## 4.  Moving a bivalent marker along its chain is a Laplacian equivalence -/

section MarkerMove

variable {n p : ℕ}

/-- **`j₁` and `j₂` run in series through a bivalent marker** `C.head j₁`: the
marker is the joint, and no other slot ends or begins there. -/
def MarkerPair (C : ExplicitPotential.Core n p) (j₁ j₂ : Fin p) : Prop :=
  j₁ ≠ j₂ ∧ C.head j₁ = C.tail j₂ ∧
    (∀ j : Fin p, C.head j = C.head j₁ → j = j₁) ∧
    (∀ j : Fin p, C.tail j = C.head j₁ → j = j₂)

/-- The vertex at position `t` along the chain `j₁ ⋯ j₂`, measured from
`tail j₁`.  This is `kindVertex` of a `double` slot, whose fallback is unused. -/
def chainVertex (T : Spec n p) (j₁ j₂ : Fin p) (t : ℕ) : T.Vertex :=
  kindVertex T (T.core.tail j₁) (SlotKind.double j₁ j₂) t

theorem kindVertex_double_eq_chainVertex (T : Spec n p) (fallback : Fin n)
    (j₁ j₂ : Fin p) (t : ℕ) :
    kindVertex T fallback (SlotKind.double j₁ j₂) t = chainVertex T j₁ j₂ t := rfl

section Values

variable (T : Spec n p) {j₁ j₂ : Fin p}

theorem chainVertex_zero : chainVertex T j₁ j₂ 0 = T.coreVertex (T.core.tail j₁) :=
  kindVertex_zero_double (small := T) (T.core.tail j₁) j₁ j₂

theorem chainVertex_of_lt {t : ℕ} (h0 : 0 < t) (ht : t < T.length j₁) :
    chainVertex T j₁ j₂ t = T.interiorVertex j₁ ⟨t - 1, by omega⟩ := by
  unfold chainVertex
  rw [kindVertex_double_le j₁ j₂ _ ht.le,
    PathHelpers.pathVertex_of_interior T j₁ _ (by simp; omega) (by simp; omega)]
  congr 2
  simp only
  omega

theorem chainVertex_first : chainVertex T j₁ j₂ (T.length j₁) =
    T.coreVertex (T.core.head j₁) := by
  unfold chainVertex
  rw [kindVertex_double_le j₁ j₂ _ le_rfl]
  have := T.length_pos j₁
  exact PathHelpers.pathVertex_of_last T j₁ _ (by simp; omega) (by simp)

theorem chainVertex_of_gt {t : ℕ} (ht1 : T.length j₁ < t)
    (ht2 : t < T.length j₁ + T.length j₂) :
    chainVertex T j₁ j₂ t = T.interiorVertex j₂ ⟨t - T.length j₁ - 1, by omega⟩ := by
  unfold chainVertex
  rw [kindVertex_double_gt j₁ j₂ _ (by omega),
    PathHelpers.pathVertex_of_interior T j₂ _ (by simp; omega) (by simp; omega)]
  congr 2
  simp only
  omega

theorem chainVertex_last {t : ℕ} (ht : T.length j₁ + T.length j₂ ≤ t) :
    chainVertex T j₁ j₂ t = T.coreVertex (T.core.head j₂) := by
  have h1 := T.length_pos j₁
  have h2 := T.length_pos j₂
  unfold chainVertex
  rw [kindVertex_double_gt j₁ j₂ _ (by omega)]
  exact PathHelpers.pathVertex_of_last T j₂ _ (by simp; omega) (by simp; omega)

/-- On the second slot the chain is the path of `j₂`, shifted. -/
theorem chainVertex_shift (hMid : T.core.head j₁ = T.core.tail j₂) (i : ℕ) :
    chainVertex T j₁ j₂ (T.length j₁ + i) =
      T.pathVertex j₂ ⟨min i (T.length j₂), by omega⟩ :=
  kindVertex_double_shift _ hMid i

end Values

/-- The unit step at position `u` along the chain (junk beyond its end). -/
def chainStep (T : Spec n p) (j₁ j₂ : Fin p) (u : ℕ) : T.Step :=
  if h : u < T.length j₁ then ⟨j₁, ⟨u, h⟩⟩
  else if h' : u - T.length j₁ < T.length j₂ then ⟨j₂, ⟨u - T.length j₁, h'⟩⟩
  else ⟨j₁, ⟨0, T.length_pos j₁⟩⟩

theorem chainStep_first (T : Spec n p) {j₁ j₂ : Fin p} (o : Fin (T.length j₁)) :
    chainStep T j₁ j₂ o.val = ⟨j₁, o⟩ := by
  unfold chainStep
  rw [dite_eq_left o.isLt]

theorem chainStep_second (T : Spec n p) {j₁ j₂ : Fin p} (o : Fin (T.length j₂)) :
    chainStep T j₁ j₂ (T.length j₁ + o.val) = ⟨j₂, o⟩ := by
  unfold chainStep
  rw [dite_eq_right (by omega), dite_eq_left (by have := o.isLt; omega)]
  congr 2
  simp

theorem stepLeft_eq_pathVertex (T : Spec n p) (j : Fin p) (s : Fin (T.length j)) :
    T.stepLeft j s = T.pathVertex j ⟨s.val, by omega⟩ :=
  (T.pathVertex_stepLeftPosition j s).symm

theorem stepRight_eq_pathVertex (T : Spec n p) (j : Fin p) (s : Fin (T.length j)) :
    T.stepRight j s = T.pathVertex j ⟨s.val + 1, by omega⟩ :=
  (T.pathVertex_stepRightPosition j s).symm

/-- **A chain step joins consecutive chain vertices.** -/
theorem unitEdge_chainStep (T : Spec n p) {j₁ j₂ : Fin p}
    (hMid : T.core.head j₁ = T.core.tail j₂) {u : ℕ}
    (hu : u < T.length j₁ + T.length j₂) :
    T.unitEdge (chainStep T j₁ j₂ u) = (chainVertex T j₁ j₂ u, chainVertex T j₁ j₂ (u + 1)) := by
  by_cases h : u < T.length j₁
  · have hs : chainStep T j₁ j₂ u = ⟨j₁, ⟨u, h⟩⟩ := by
      unfold chainStep; rw [dite_eq_left h]
    rw [hs]
    show (T.stepLeft j₁ ⟨u, h⟩, T.stepRight j₁ ⟨u, h⟩) = _
    rw [stepLeft_eq_pathVertex, stepRight_eq_pathVertex]
    unfold chainVertex
    rw [kindVertex_double_le j₁ j₂ _ h.le, kindVertex_double_le j₁ j₂ _ (by omega)]
    congr 1
    · exact PathHelpers.pathVertex_congr T j₁ _ _ (by simp; omega)
    · exact PathHelpers.pathVertex_congr T j₁ _ _ (by simp; omega)
  · obtain ⟨i, rfl⟩ : ∃ i, u = T.length j₁ + i := ⟨u - T.length j₁, by omega⟩
    have hi : i < T.length j₂ := by omega
    have hs : chainStep T j₁ j₂ (T.length j₁ + i) = ⟨j₂, ⟨i, hi⟩⟩ :=
      chainStep_second T ⟨i, hi⟩
    rw [hs]
    show (T.stepLeft j₂ ⟨i, hi⟩, T.stepRight j₂ ⟨i, hi⟩) = _
    rw [stepLeft_eq_pathVertex, stepRight_eq_pathVertex, chainVertex_shift T hMid,
      show T.length j₁ + i + 1 = T.length j₁ + (i + 1) by omega, chainVertex_shift T hMid]
    congr 1
    · exact PathHelpers.pathVertex_congr T j₂ _ _ (by simp; omega)
    · exact PathHelpers.pathVertex_congr T j₂ _ _ (by simp; omega)

/-- **The re-split specification**: the chain `j₁ ⋯ j₂` keeps its total length but
its marker now sits at distance `a` from `tail j₁`. -/
def moveSpec (T : Spec n p) (j₁ j₂ : Fin p) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Spec n p where
  core := T.core
  length := fun j ↦ if j = j₁ then a else if j = j₂ then b else T.length j
  core_nonempty := T.core_nonempty
  core_loopless := T.core_loopless
  length_pos := by
    intro j
    show 0 < (if j = j₁ then a else if j = j₂ then b else T.length j)
    split_ifs
    · exact ha
    · exact hb
    · exact T.length_pos j

/-- The vertex relabelling: chain positions are kept, everything off the chain is
fixed.  Defined without hypotheses; the junk branches are never reached under
`MoveHyp`. -/
def moveVertex (T T' : Spec n p) (j₁ j₂ : Fin p) : T.Vertex → T'.Vertex
  | Sum.inl v => if v = T.core.head j₁ then chainVertex T' j₁ j₂ (T.length j₁) else Sum.inl v
  | Sum.inr x =>
      if x.1 = j₁ then chainVertex T' j₁ j₂ (x.2.val + 1)
      else if x.1 = j₂ then chainVertex T' j₁ j₂ (T.length j₁ + x.2.val + 1)
      else if h : T'.length x.1 = T.length x.1 then
        Sum.inr ⟨x.1, Fin.cast (congrArg (· - 1) h.symm) x.2⟩
      else Sum.inl (T.core.head j₁)

/-- The unit-step relabelling. -/
def moveStep (T T' : Spec n p) (j₁ j₂ : Fin p) : T.Step → T'.Step
  | x =>
      if x.1 = j₁ then chainStep T' j₁ j₂ x.2.val
      else if x.1 = j₂ then chainStep T' j₁ j₂ (T.length j₁ + x.2.val)
      else if h : T'.length x.1 = T.length x.1 then ⟨x.1, Fin.cast h.symm x.2⟩
      else ⟨j₁, ⟨0, T'.length_pos j₁⟩⟩

section Equations

variable (T T' : Spec n p) (j₁ j₂ : Fin p)

theorem moveVertex_inl (v : Fin n) :
    moveVertex T T' j₁ j₂ (Sum.inl v) =
      if v = T.core.head j₁ then chainVertex T' j₁ j₂ (T.length j₁) else Sum.inl v := rfl

theorem moveVertex_inr_first (o : Fin (T.length j₁ - 1)) :
    moveVertex T T' j₁ j₂ (Sum.inr ⟨j₁, o⟩) = chainVertex T' j₁ j₂ (o.val + 1) := by
  show (if j₁ = j₁ then chainVertex T' j₁ j₂ (o.val + 1) else _) = _
  rw [ite_eq_left rfl]

theorem moveVertex_inr_second (hne : j₂ ≠ j₁) (o : Fin (T.length j₂ - 1)) :
    moveVertex T T' j₁ j₂ (Sum.inr ⟨j₂, o⟩) =
      chainVertex T' j₁ j₂ (T.length j₁ + o.val + 1) := by
  show (if j₂ = j₁ then _ else if j₂ = j₂ then
    chainVertex T' j₁ j₂ (T.length j₁ + o.val + 1) else _) = _
  rw [ite_eq_right hne, ite_eq_left rfl]

theorem moveVertex_inr_other {j : Fin p} (hj₁ : j ≠ j₁) (hj₂ : j ≠ j₂)
    (hLen : T'.length j = T.length j) (o : Fin (T.length j - 1)) :
    moveVertex T T' j₁ j₂ (Sum.inr ⟨j, o⟩) =
      (Sum.inr ⟨j, Fin.cast (congrArg (· - 1) hLen.symm) o⟩ : T'.Vertex) := by
  simp only [moveVertex, ite_eq_right hj₁, ite_eq_right hj₂, dite_eq_left hLen]

theorem moveStep_first (o : Fin (T.length j₁)) :
    moveStep T T' j₁ j₂ ⟨j₁, o⟩ = chainStep T' j₁ j₂ o.val := by
  simp [moveStep]

theorem moveStep_second (hne : j₂ ≠ j₁) (o : Fin (T.length j₂)) :
    moveStep T T' j₁ j₂ ⟨j₂, o⟩ = chainStep T' j₁ j₂ (T.length j₁ + o.val) := by
  simp [moveStep, hne]

theorem moveStep_other {j : Fin p} (hj₁ : j ≠ j₁) (hj₂ : j ≠ j₂)
    (hLen : T'.length j = T.length j) (o : Fin (T.length j)) :
    moveStep T T' j₁ j₂ ⟨j, o⟩ = (⟨j, Fin.cast hLen.symm o⟩ : T'.Step) := by
  simp only [moveStep, ite_eq_right hj₁, ite_eq_right hj₂, dite_eq_left hLen]

end Equations

/-- The hypotheses under which `moveVertex`/`moveStep` are inverse bijections. -/
structure MoveHyp (T T' : Spec n p) (j₁ j₂ : Fin p) : Prop where
  core_eq : T'.core = T.core
  pair : MarkerPair T.core j₁ j₂
  len_eq : ∀ j : Fin p, j ≠ j₁ → j ≠ j₂ → T'.length j = T.length j
  sum_eq : T'.length j₁ + T'.length j₂ = T.length j₁ + T.length j₂

theorem MoveHyp.symm {T T' : Spec n p} {j₁ j₂ : Fin p} (h : MoveHyp T T' j₁ j₂) :
    MoveHyp T' T j₁ j₂ where
  core_eq := h.core_eq.symm
  pair := h.core_eq ▸ h.pair
  len_eq := fun j h1 h2 ↦ (h.len_eq j h1 h2).symm
  sum_eq := h.sum_eq.symm

theorem moveHyp_moveSpec (T : Spec n p) {j₁ j₂ : Fin p} (hpair : MarkerPair T.core j₁ j₂)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = T.length j₁ + T.length j₂) :
    MoveHyp T (moveSpec T j₁ j₂ a b ha hb) j₁ j₂ where
  core_eq := rfl
  pair := hpair
  len_eq := by
    intro j h1 h2
    show (if j = j₁ then a else if j = j₂ then b else T.length j) = T.length j
    rw [ite_eq_right h1, ite_eq_right h2]
  sum_eq := by
    show (if j₁ = j₁ then a else if j₁ = j₂ then b else T.length j₁) +
      (if j₂ = j₁ then a else if j₂ = j₂ then b else T.length j₂) = _
    rw [ite_eq_left rfl, ite_eq_right (Ne.symm hpair.1), ite_eq_left rfl]
    exact hab

theorem moveSpec_length_first (T : Spec n p) {j₁ j₂ : Fin p} (a b : ℕ) (ha : 0 < a)
    (hb : 0 < b) : (moveSpec T j₁ j₂ a b ha hb).length j₁ = a := by
  show (if j₁ = j₁ then a else if j₁ = j₂ then b else T.length j₁) = a
  rw [ite_eq_left rfl]

/-- Off the marker, core vertices are fixed. -/
theorem moveVertex_coreVertex {T T' : Spec n p} {j₁ j₂ : Fin p} {v : Fin n}
    (hv : v ≠ T.core.head j₁) :
    moveVertex T T' j₁ j₂ (T.coreVertex v) = T'.coreVertex v := by
  show moveVertex T T' j₁ j₂ (Sum.inl v) = Sum.inl v
  rw [moveVertex_inl, ite_eq_right hv]

section MoveLemmas

variable {T T' : Spec n p} {j₁ j₂ : Fin p} (h : MoveHyp T T' j₁ j₂)
include h

theorem MoveHyp.head_second_ne_marker : T.core.head j₂ ≠ T.core.head j₁ := by
  intro hEq
  exact h.pair.1 (h.pair.2.2.1 j₂ hEq).symm

theorem MoveHyp.head_ne_marker {j : Fin p} (hj : j ≠ j₁) : T.core.head j ≠ T.core.head j₁ :=
  fun hEq ↦ hj (h.pair.2.2.1 j hEq)

theorem MoveHyp.tail_ne_marker {j : Fin p} (hj : j ≠ j₂) : T.core.tail j ≠ T.core.head j₁ :=
  fun hEq ↦ hj (h.pair.2.2.2 j hEq)

/-- **Chain positions are kept.** -/
theorem moveVertex_chainVertex {t : ℕ} (ht : t ≤ T.length j₁ + T.length j₂) :
    moveVertex T T' j₁ j₂ (chainVertex T j₁ j₂ t) = chainVertex T' j₁ j₂ t := by
  have h1 := T.length_pos j₁
  have h2 := T.length_pos j₂
  rcases Nat.eq_zero_or_pos t with rfl | h0
  · rw [chainVertex_zero, moveVertex_coreVertex (T.core_loopless j₁), chainVertex_zero,
      h.core_eq]
  rcases lt_trichotomy t (T.length j₁) with hlt | heq | hgt
  · rw [chainVertex_of_lt T h0 hlt]
    show moveVertex T T' j₁ j₂ (Sum.inr ⟨j₁, ⟨t - 1, _⟩⟩) = _
    rw [moveVertex_inr_first]
    congr 1
    simp only
    omega
  · subst heq
    rw [chainVertex_first]
    show moveVertex T T' j₁ j₂ (Sum.inl (T.core.head j₁)) = _
    rw [moveVertex_inl, ite_eq_left rfl]
  · rcases lt_or_eq_of_le ht with hlt | heq
    · rw [chainVertex_of_gt T hgt hlt]
      show moveVertex T T' j₁ j₂ (Sum.inr ⟨j₂, ⟨t - T.length j₁ - 1, _⟩⟩) = _
      rw [moveVertex_inr_second T T' j₁ j₂ (Ne.symm h.pair.1)]
      congr 1
      simp only
      omega
    · rw [chainVertex_last T heq.ge, moveVertex_coreVertex h.head_second_ne_marker,
        chainVertex_last T' (by rw [h.sum_eq]; omega), h.core_eq]

/-- **Every other slot is fixed, position by position.** -/
theorem moveVertex_pathVertex {j : Fin p} (hj₁ : j ≠ j₁) (hj₂ : j ≠ j₂)
    (t : T.PathPosition j) :
    moveVertex T T' j₁ j₂ (T.pathVertex j t) =
      T'.pathVertex j ⟨t.val, by rw [h.len_eq j hj₁ hj₂]; exact t.isLt⟩ := by
  have hLen := h.len_eq j hj₁ hj₂
  by_cases h0 : t.val = 0
  · rw [PathHelpers.pathVertex_of_zero T j t h0,
      PathHelpers.pathVertex_of_zero T' j _ h0,
      moveVertex_coreVertex (h.tail_ne_marker hj₂), h.core_eq]
  · by_cases hl : t.val = T.length j
    · rw [PathHelpers.pathVertex_of_last T j t h0 hl,
        PathHelpers.pathVertex_of_last T' j _ h0 (by show t.val = T'.length j; omega),
        moveVertex_coreVertex (h.head_ne_marker hj₁), h.core_eq]
    · rw [PathHelpers.pathVertex_of_interior T j t h0 hl,
        PathHelpers.pathVertex_of_interior T' j _ h0 (by show t.val ≠ T'.length j; omega)]
      show moveVertex T T' j₁ j₂ (Sum.inr ⟨j, ⟨t.val - 1, _⟩⟩) = _
      rw [moveVertex_inr_other T T' j₁ j₂ hj₁ hj₂ hLen]
      rfl

/-- **The step relabelling respects unit edges.** -/
theorem unitEdge_moveStep (s : T.Step) :
    T'.unitEdge (moveStep T T' j₁ j₂ s) =
      (moveVertex T T' j₁ j₂ (T.unitEdge s).1, moveVertex T T' j₁ j₂ (T.unitEdge s).2) := by
  have hMid := h.pair.2.1
  have hMid' : T'.core.head j₁ = T'.core.tail j₂ := by rw [h.core_eq]; exact hMid
  obtain ⟨j, o⟩ := s
  have ho := o.isLt
  by_cases h1 : j = j₁
  · subst h1
    have hs : (⟨j, o⟩ : T.Step) = chainStep T j j₂ o.val := (chainStep_first T o).symm
    rw [moveStep_first, unitEdge_chainStep T' hMid' (by rw [h.sum_eq]; omega), hs,
      unitEdge_chainStep T hMid (by omega),
      moveVertex_chainVertex h (by omega), moveVertex_chainVertex h (by omega)]
  · by_cases h2 : j = j₂
    · subst h2
      have hs : (⟨j, o⟩ : T.Step) = chainStep T j₁ j (T.length j₁ + o.val) :=
        (chainStep_second T o).symm
      rw [moveStep_second T T' j₁ j h1, unitEdge_chainStep T' hMid' (by rw [h.sum_eq]; omega),
        hs, unitEdge_chainStep T hMid (by omega),
        moveVertex_chainVertex h (by omega), moveVertex_chainVertex h (by omega)]
    · have hLen := h.len_eq j h1 h2
      rw [moveStep_other T T' j₁ j₂ h1 h2 hLen]
      show (T'.stepLeft j (Fin.cast hLen.symm o), T'.stepRight j (Fin.cast hLen.symm o)) =
        (moveVertex T T' j₁ j₂ (T.stepLeft j o), moveVertex T T' j₁ j₂ (T.stepRight j o))
      rw [stepLeft_eq_pathVertex, stepRight_eq_pathVertex, stepLeft_eq_pathVertex,
        stepRight_eq_pathVertex, moveVertex_pathVertex h h1 h2,
        moveVertex_pathVertex h h1 h2]
      rfl

/-- `moveStep` carries chain steps to chain steps. -/
theorem moveStep_chainStep {u : ℕ} (hu : u < T.length j₁ + T.length j₂) :
    moveStep T T' j₁ j₂ (chainStep T j₁ j₂ u) = chainStep T' j₁ j₂ u := by
  by_cases hlt : u < T.length j₁
  · rw [show chainStep T j₁ j₂ u = ⟨j₁, ⟨u, hlt⟩⟩ from chainStep_first T ⟨u, hlt⟩,
      moveStep_first]
  · obtain ⟨i, rfl⟩ : ∃ i, u = T.length j₁ + i := ⟨u - T.length j₁, by omega⟩
    have hi : i < T.length j₂ := by omega
    rw [show chainStep T j₁ j₂ (T.length j₁ + i) = ⟨j₂, ⟨i, hi⟩⟩ from
      chainStep_second T ⟨i, hi⟩, moveStep_second T T' j₁ j₂ (Ne.symm h.pair.1)]

end MoveLemmas

section RoundTrip

variable {T T' : Spec n p} {j₁ j₂ : Fin p}

theorem moveVertex_moveVertex (h : MoveHyp T T' j₁ j₂) (x : T.Vertex) :
    moveVertex T' T j₁ j₂ (moveVertex T T' j₁ j₂ x) = x := by
  have hs := h.symm
  have h1 := T.length_pos j₁
  have h2 := T.length_pos j₂
  rcases x with v | ⟨j, o⟩
  · by_cases hv : v = T.core.head j₁
    · subst hv
      rw [moveVertex_inl, ite_eq_left rfl, moveVertex_chainVertex hs (by rw [h.sum_eq]; omega),
        chainVertex_first]
      rfl
    · have hv' : v ≠ T'.core.head j₁ := by rw [h.core_eq]; exact hv
      rw [moveVertex_inl, ite_eq_right hv, moveVertex_inl, ite_eq_right hv']
  · have ho := o.isLt
    by_cases hj₁ : j = j₁
    · subst hj₁
      rw [moveVertex_inr_first, moveVertex_chainVertex hs (by rw [h.sum_eq]; omega),
        chainVertex_of_lt T (by omega) (by omega)]
      simp only [Spec.interiorVertex, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and,
        Fin.ext_iff]
      omega
    · by_cases hj₂ : j = j₂
      · subst hj₂
        rw [moveVertex_inr_second T T' j₁ j hj₁,
          moveVertex_chainVertex hs (by rw [h.sum_eq]; omega),
          chainVertex_of_gt T (by omega) (by omega)]
        simp only [Spec.interiorVertex, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and,
          Fin.ext_iff]
        omega
      · have hLen := h.len_eq j hj₁ hj₂
        rw [moveVertex_inr_other T T' j₁ j₂ hj₁ hj₂ hLen,
          moveVertex_inr_other T' T j₁ j₂ hj₁ hj₂ hLen.symm]
        rfl

theorem moveStep_moveStep (h : MoveHyp T T' j₁ j₂) (s : T.Step) :
    moveStep T' T j₁ j₂ (moveStep T T' j₁ j₂ s) = s := by
  have hs := h.symm
  obtain ⟨j, o⟩ := s
  have ho := o.isLt
  by_cases hj₁ : j = j₁
  · subst hj₁
    rw [moveStep_first, moveStep_chainStep hs (by rw [h.sum_eq]; omega)]
    exact chainStep_first T o
  · by_cases hj₂ : j = j₂
    · subst hj₂
      rw [moveStep_second T T' j₁ j hj₁, moveStep_chainStep hs (by rw [h.sum_eq]; omega)]
      exact chainStep_second T o
    · have hLen := h.len_eq j hj₁ hj₂
      rw [moveStep_other T T' j₁ j₂ hj₁ hj₂ hLen, moveStep_other T' T j₁ j₂ hj₁ hj₂ hLen.symm]
      rfl

/-- **Moving a marker along its chain does not change the graph.** -/
def moveEquiv (h : MoveHyp T T' j₁ j₂) : LaplacianEquiv T.graph T'.graph :=
  OneEdgeSplitRefinement.laplacianEquivOfUnorientedUnitSteps T T'
    { toFun := moveVertex T T' j₁ j₂
      invFun := moveVertex T' T j₁ j₂
      left_inv := moveVertex_moveVertex h
      right_inv := moveVertex_moveVertex h.symm }
    { toFun := moveStep T T' j₁ j₂
      invFun := moveStep T' T j₁ j₂
      left_inv := moveStep_moveStep h
      right_inv := moveStep_moveStep h.symm }
    (fun s ↦ Or.inl (unitEdge_moveStep h s))

@[simp] theorem moveEquiv_apply (h : MoveHyp T T' j₁ j₂) (x : T.Vertex) :
    moveEquiv h x = moveVertex T T' j₁ j₂ x := rfl

end RoundTrip

end MarkerMove

/-! ## 5.  Rank one from a marker-free set: move every unreached marker -/

section MarkerFreeRank

variable {n p N Q : ℕ} {D : ExpansionData n p N Q}

/-- Under `ExpansionData.Conditions`, the two small slots of a `double` big slot
run in series through a genuine bivalent marker. -/
theorem markerPair_of_double {C : Utilities.Certificate.ExplicitPotential.Core n p}
    (hCond : D.Conditions C) {e : Fin Q} {j₁ j₂ : Fin p}
    (hk : D.kind e = SlotKind.double j₁ j₂) : MarkerPair C j₁ j₂ := by
  obtain ⟨hT, hMid, hH⟩ := (ExpansionData.compatible_of_conditions hCond e).2.2 j₁ j₂ hk
  refine ⟨?_, hMid, (ExpansionData.marker_of_conditions hCond e j₁ j₂ hk).2, ?_⟩
  · intro hEq
    subst hEq
    exact fib_ne_marker hCond hk _ hH
  · intro j hj
    rcases ExpansionData.exists_carrier hCond j with ⟨hk', -⟩ | ⟨j', hk', -⟩ | ⟨j', hk', -⟩
    · have := ((ExpansionData.compatible_of_conditions hCond (D.owner j)).2.1 j hk').1
      exact absurd (this.trans hj) (fib_ne_marker hCond hk _)
    · have := ((ExpansionData.compatible_of_conditions hCond (D.owner j)).2.2 j j' hk').1
      exact absurd (this.trans hj) (fib_ne_marker hCond hk _)
    · have hMid' := ((ExpansionData.compatible_of_conditions hCond (D.owner j)).2.2 j' j hk').2.1
      have hj' : j' = j₁ :=
        (ExpansionData.marker_of_conditions hCond e j₁ j₂ hk).2 j' (hMid'.trans hj)
      subst hj'
      have hOwner : D.owner j = e :=
        (ExpansionData.owner_eq_of_double hCond hk').1.symm.trans
          (ExpansionData.owner_eq_of_double hCond hk).1
      rw [hOwner, hk] at hk'
      exact (SlotKind.double.inj hk').2.symm

/-- Distinct `double` slots carry disjoint pairs of small slots. -/
theorem disjoint_of_double {C : Utilities.Certificate.ExplicitPotential.Core n p}
    (hCond : D.Conditions C) {e e' : Fin Q} {j₁ j₂ i₁ i₂ : Fin p}
    (hk : D.kind e = SlotKind.double j₁ j₂) (hk' : D.kind e' = SlotKind.double i₁ i₂)
    (hne : e' ≠ e) : (i₁ ≠ j₁ ∧ i₁ ≠ j₂) ∧ (i₂ ≠ j₁ ∧ i₂ ≠ j₂) := by
  obtain ⟨o₁, -, o₂, -⟩ := ExpansionData.owner_eq_of_double hCond hk
  obtain ⟨o₁', -, o₂', -⟩ := ExpansionData.owner_eq_of_double hCond hk'
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> intro hEq <;> subst hEq <;> apply hne
  · exact o₁'.symm.trans o₁
  · exact o₁'.symm.trans o₂
  · exact o₂'.symm.trans o₁
  · exact o₂'.symm.trans o₂

/-- A move fixes every chain disjoint from the moved one. -/
theorem moveVertex_chainVertex_other {T T' : Spec n p} {j₁ j₂ : Fin p}
    (h : MoveHyp T T' j₁ j₂) {i₁ i₂ : Fin p} (hi₁ : i₁ ≠ j₁ ∧ i₁ ≠ j₂)
    (hi₂ : i₂ ≠ j₁ ∧ i₂ ≠ j₂) (t : ℕ) :
    moveVertex T T' j₁ j₂ (chainVertex T i₁ i₂ t) = chainVertex T' i₁ i₂ t := by
  have hL1 := h.len_eq i₁ hi₁.1 hi₁.2
  have hL2 := h.len_eq i₂ hi₂.1 hi₂.2
  have hTail : T'.core.tail i₁ = T.core.tail i₁ := by rw [h.core_eq]
  unfold chainVertex
  by_cases hq : t ≤ T.length i₁
  · rw [kindVertex_double_le i₁ i₂ _ hq, kindVertex_double_le i₁ i₂ _ (by rw [hL1]; exact hq),
      moveVertex_pathVertex h hi₁.1 hi₁.2]
    exact PathHelpers.pathVertex_congr T' i₁ _ _ (by simp [hL1])
  · rw [kindVertex_double_gt i₁ i₂ _ hq, kindVertex_double_gt i₁ i₂ _ (by rw [hL1]; exact hq),
      moveVertex_pathVertex h hi₂.1 hi₂.2]
    exact PathHelpers.pathVertex_congr T' i₂ _ _ (by simp [hL1, hL2])

open Classical in
/-- The `double` slots whose marker `Dv` does not yet reach. -/
noncomputable def unreachedMarkers (D : ExpansionData n p N Q) (T : Spec n p)
    (Dv : CFDiv T.graph) : Finset (Fin Q) :=
  Finset.univ.filter fun e ↦ ∃ j₁ j₂ : Fin p, D.kind e = SlotKind.double j₁ j₂ ∧
    ¬ winnable T.graph (Dv - one_chip (T.coreVertex (T.core.head j₁)))

/-- Transport of a reach statement along a Laplacian equivalence. -/
theorem winnable_sub_one_chip_mapDiv {G H : CFGraph} (φ : LaplacianEquiv G H)
    (Dv : CFDiv G) (x : G.V) :
    winnable H (φ.mapDiv Dv - one_chip (φ x)) ↔ winnable G (Dv - one_chip x) := by
  rw [← LaplacianEquiv.mapDiv_one_chip, ← LaplacianEquiv.mapDiv_sub,
    LaplacianEquiv.winnable_mapDiv_iff]

theorem rank_ge_one_of_markerFree_aux (m : ℕ) :
    ∀ (T : Spec n p), D.Conditions T.core → graph_connected T.graph →
      ∀ (Dv : CFDiv T.graph),
      (∀ a : Fin N, winnable T.graph (Dv - one_chip (T.coreVertex (D.fib a)))) →
      (∀ (e : Fin Q) (j₁ j₂ : Fin p), D.kind e = SlotKind.double j₁ j₂ →
        ∃ t, 0 < t ∧ t < T.length j₁ + T.length j₂ ∧
          winnable T.graph (Dv - one_chip (chainVertex T j₁ j₂ t))) →
      (unreachedMarkers D T Dv).card = m → rank T.graph Dv ≥ 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro T hCond hConn Dv hFib hDouble hm
  classical
  by_cases hAll : unreachedMarkers D T Dv = ∅
  · refine Spec.rank_ge_one_of_reaches_coreVertices T T.core_loopless hConn Dv (fun v ↦ ?_)
    rcases marker_or_exists_fib hCond v with ⟨e, j₁, j₂, hk, rfl⟩ | ⟨a, rfl⟩
    · by_contra hNot
      have hMem : e ∈ unreachedMarkers D T Dv := by
        unfold unreachedMarkers
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j₁, j₂, hk, hNot⟩
      rw [hAll] at hMem
      exact absurd hMem (Finset.notMem_empty _)
    · exact hFib a
  · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hAll
    obtain ⟨j₁, j₂, hk, hUn⟩ :=
      (Finset.mem_filter.mp (by unfold unreachedMarkers at he; exact he)).2
    obtain ⟨t, ht0, htL, hReach⟩ := hDouble e j₁ j₂ hk
    have hPair : MarkerPair T.core j₁ j₂ := markerPair_of_double hCond hk
    have hb : 0 < T.length j₁ + T.length j₂ - t := by omega
    let T' := moveSpec T j₁ j₂ t (T.length j₁ + T.length j₂ - t) ht0 hb
    have hMove : MoveHyp T T' j₁ j₂ := moveHyp_moveSpec T hPair _ _ ht0 hb (by omega)
    let φ := moveEquiv hMove
    have hCond' : D.Conditions T'.core := hCond
    have hConn' : graph_connected T'.graph := φ.graphConnected hConn
    have hFirst : T'.length j₁ = t := moveSpec_length_first T _ _ ht0 hb
    -- the marker of `e` is reached in the moved presentation
    have hMarkerReached :
        winnable T'.graph (φ.mapDiv Dv - one_chip (T'.coreVertex (T'.core.head j₁))) := by
      have hEq : T'.coreVertex (T'.core.head j₁) = φ (chainVertex T j₁ j₂ t) := by
        rw [moveEquiv_apply, moveVertex_chainVertex hMove htL.le, ← hFirst,
          chainVertex_first]
      rw [hEq, winnable_sub_one_chip_mapDiv]
      exact hReach
    -- every other core vertex keeps its status
    have hCore : ∀ v : Fin n, v ≠ T.core.head j₁ →
        (winnable T'.graph (φ.mapDiv Dv - one_chip (T'.coreVertex v)) ↔
          winnable T.graph (Dv - one_chip (T.coreVertex v))) := by
      intro v hv
      rw [show T'.coreVertex v = φ (T.coreVertex v) from
        (moveVertex_coreVertex hv).symm, winnable_sub_one_chip_mapDiv]
    have hSub : unreachedMarkers D T' (φ.mapDiv Dv) ⊂ unreachedMarkers D T Dv := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨e, he, ?_⟩
        intro he'
        unfold unreachedMarkers at he'
        obtain ⟨i₁, i₂, hk', hUn'⟩ := (Finset.mem_filter.mp he').2
        rw [hk] at hk'
        obtain ⟨rfl, rfl⟩ := SlotKind.double.inj hk'
        exact hUn' hMarkerReached
      · intro e' he'
        unfold unreachedMarkers at he' ⊢
        obtain ⟨i₁, i₂, hk', hUn'⟩ := (Finset.mem_filter.mp he').2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, i₁, i₂, hk', ?_⟩
        by_cases hee : e' = e
        · subst hee
          rw [hk] at hk'
          obtain ⟨rfl, rfl⟩ := SlotKind.double.inj hk'
          exact absurd hMarkerReached hUn'
        · have hi := disjoint_of_double hCond hk hk' hee
          have hv : T.core.head i₁ ≠ T.core.head j₁ := fun hEq ↦ hi.1.1 (hPair.2.2.1 i₁ hEq)
          exact fun hW ↦ hUn' ((hCore _ hv).mpr hW)
    have hLt : (unreachedMarkers D T' (φ.mapDiv Dv)).card < m := by
      rw [← hm]
      exact Finset.card_lt_card hSub
    have hRank := ih _ hLt T' hCond' hConn' (φ.mapDiv Dv)
      (fun a ↦ (hCore (D.fib a) (fib_ne_marker hCond hk a)).mpr (hFib a))
      (fun e' i₁ i₂ hk' ↦ by
        by_cases hee : e' = e
        · subst hee
          rw [hk] at hk'
          obtain ⟨rfl, rfl⟩ := SlotKind.double.inj hk'
          refine ⟨t, ht0, by rw [hMove.sum_eq]; exact htL, ?_⟩
          rw [← moveVertex_chainVertex hMove htL.le, ← moveEquiv_apply hMove,
            winnable_sub_one_chip_mapDiv]
          exact hReach
        · have hi := disjoint_of_double hCond hk hk' hee
          obtain ⟨t', ht0', htL', hReach'⟩ := hDouble e' i₁ i₂ hk'
          refine ⟨t', ht0', by rw [hMove.len_eq i₁ hi.1.1 hi.1.2,
            hMove.len_eq i₂ hi.2.1 hi.2.2]; exact htL', ?_⟩
          rw [← moveVertex_chainVertex_other hMove hi.1 hi.2 t', ← moveEquiv_apply hMove,
            winnable_sub_one_chip_mapDiv]
          exact hReach')
      rfl
    exact (φ.rank_mapDiv_ge_iff Dv 1).mp hRank

/-- **Rank one from a marker-free set.**  On a subdivision whose core carries the
markers of an expansion datum, `Dv` has rank at least one as soon as it reaches
every `D.fib` image and, for every `double` slot, **some** vertex strictly inside
the chain `j₁ ⋯ j₂` — not necessarily the marker.

The proof moves each unreached marker to a reached vertex of its own chain
(`moveEquiv`, a Laplacian equivalence of the same graph) and then applies
`Spec.rank_ge_one_of_reaches_coreVertices` to the moved presentation.  A
chain's interior is the only place its marker has to be reached from: this is
Luo's criterion for a loop (the interior of a loop chain must meet the test set),
realized here by re-presentation rather than by porting Luo. -/
theorem rank_ge_one_of_markerFree (T : Spec n p) (hCond : D.Conditions T.core)
    (hConn : graph_connected T.graph) (Dv : CFDiv T.graph)
    (hFib : ∀ a : Fin N, winnable T.graph (Dv - one_chip (T.coreVertex (D.fib a))))
    (hDouble : ∀ (e : Fin Q) (j₁ j₂ : Fin p), D.kind e = SlotKind.double j₁ j₂ →
      ∃ t, 0 < t ∧ t < T.length j₁ + T.length j₂ ∧
        winnable T.graph (Dv - one_chip (chainVertex T j₁ j₂ t))) :
    rank T.graph Dv ≥ 1 :=
  rank_ge_one_of_markerFree_aux _ T hCond hConn Dv hFib hDouble rfl

end MarkerFreeRank

/-! ## 6.  Forest-contraction rank through the marker-free set -/

/-- An effective divisor linearly equivalent to `Dv` and positive at `x` makes
`Dv - x` winnable.  (The step used by `forestContractionRank_of_markerFreePencilCover`,
stated once.) -/
theorem winnable_sub_one_chip_of_linear_equiv {G : CFGraph} {Dv E : CFDiv G}
    (hE : effective E) (hEquiv : linear_equiv G Dv E) {x : G.V} (hx : 0 < E x) :
    winnable G (Dv - one_chip x) := by
  rw [winnable_iff_exists_effective]
  refine ⟨E - one_chip x, ?_, ?_⟩
  · intro b
    by_cases hb : b = x
    · subst hb
      simp only [Pi.sub_apply, one_chip_apply_v]
      omega
    · simp only [Pi.sub_apply, one_chip, ite_eq_right hb, sub_zero]
      exact hE b
  · unfold linear_equiv at hEquiv ⊢
    have hEq : (E - one_chip x) - (Dv - one_chip x) = E - Dv := by abel
    rw [hEq]
    exact hEquiv

section Application

variable {n p N Q degree : ℕ}
  (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)
  (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) degree)
  (hClosed : member.Closed) (hScale : memberScale member = k)

/-- **(T), on the small side.**  Every member of the pencil is linearly
equivalent, on the small subdivision, to the one at `root`.

It is root-independent (`pencilTransport_of_pencilTransport`) and reduces to target edges
(`pencilTransport_of_adjacent`); it is proved at every root by
`PencilTransportProducer.pencilTransport`. -/
def PencilTransport (root : member.target.V) : Prop :=
  ∀ root' : member.target.V,
    linear_equiv (small.scale k hk).graph
      (ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
        (bigDivisor D small hN hL k hk member hClosed hScale root))
      (ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
        (bigDivisor D small hN hL k hk member hClosed hScale root'))

/-- **(T) edge by edge.**  The target is a connected tree, so linear equivalence
of the pushed fibres at the two ends of every target edge already gives
`PencilTransport` at every root. -/
theorem pencilTransport_of_adjacent (root : member.target.V)
    (hAdj : ∀ r₁ r₂ : member.target.V, 0 < num_edges member.target r₁ r₂ →
      linear_equiv (small.scale k hk).graph
        (ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
          (bigDivisor D small hN hL k hk member hClosed hScale r₁))
        (ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
          (bigDivisor D small hN hL k hk member hClosed hScale r₂))) :
    PencilTransport D small hN hL k hk member hClosed hScale root := by
  classical
  intro r
  by_contra hr
  let S : Finset member.target.V := Finset.univ.filter fun r' ↦
    linear_equiv (small.scale k hk).graph
      (ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
        (bigDivisor D small hN hL k hk member hClosed hScale root))
      (ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
        (bigDivisor D small hN hL k hk member hClosed hScale r'))
  obtain ⟨v, hv, w, hw, hvw⟩ := member.fullDim.targetConnected S
    ⟨root, r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, linear_equiv.refl _ _⟩,
      fun hMem ↦ hr (Finset.mem_filter.mp hMem).2⟩
  exact hw (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    linear_equiv.trans (Finset.mem_filter.mp hv).2 (hAdj v w hvw)⟩)

/-- **(T) does not depend on the base root**: linear equivalence is an
equivalence relation, so transport from one root is transport from every root. -/
theorem pencilTransport_of_pencilTransport {root : member.target.V}
    (hT : PencilTransport D small hN hL k hk member hClosed hScale root)
    (root₀ : member.target.V) :
    PencilTransport D small hN hL k hk member hClosed hScale root₀ :=
  fun root' ↦ linear_equiv.trans (linear_equiv.symm (hT root₀)) (hT root')

/-- **The double rows reach strictly inside their chains.**  For every `double`
big slot, the member's own row over it has an interior address whose oriented
integral offset lies strictly between `0` and the chain length.  This asks for
**some** interior point of the chain, not for the marker. -/
def DoubleRowInterior : Prop :=
  ∀ (e : Fin Q) (j₁ j₂ : Fin p), D.kind e = SlotKind.double j₁ j₂ →
    ∃ address : InteriorAddress member.fullDim,
      member.ident.row address.1 = e ∧
        0 < DegeneratePlacement.offsetVal (D.bigSpec (small.scale k hk) hN hL)
          (degenerateLength D small) member hClosed e (address.2.val + 1) ∧
        DegeneratePlacement.offsetVal (D.bigSpec (small.scale k hk) hN hL)
          (degenerateLength D small) member hClosed e (address.2.val + 1) <
            k * small.length j₁ + k * small.length j₂

/-- **Every `double` slot displays a loop**: its chain starts and ends at one small
vertex.  The expansion data of the cubic-model reduction have this property (every marker
of a `Marking` closes a loop, `Marking.head_mate`); an arbitrary `ExpansionData` need
not. -/
def LoopDoubles {n p N Q : ℕ} (D : ExpansionData n p N Q)
    (C : Utilities.Certificate.ExplicitPotential.Core n p) : Prop :=
  ∀ (e : Fin Q) (j₁ j₂ : Fin p), D.kind e = SlotKind.double j₁ j₂ → C.tail j₁ = C.head j₂

/-- **(MPC): the marker-free pencil cover.**  Every `D.fib` image is reached by some member
of the pencil (a pushed fibre linearly equivalent to the one at `root` and positive there),
and each `double` chain is reached at **some** vertex strictly inside it, not necessarily at
its marker. -/
def MarkerFreePencilCover (root : member.target.V) : Prop :=
  (∀ a : Fin N, ∃ root' : member.target.V,
    linear_equiv (small.scale k hk).graph
        (ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
          (bigDivisor D small hN hL k hk member hClosed hScale root))
        (ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
          (bigDivisor D small hN hL k hk member hClosed hScale root')) ∧
      0 < ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
        (bigDivisor D small hN hL k hk member hClosed hScale root')
        ((small.scale k hk).coreVertex (D.fib a))) ∧
  (∀ (e : Fin Q) (j₁ j₂ : Fin p), D.kind e = SlotKind.double j₁ j₂ →
    ∃ (root' : member.target.V) (t : ℕ), 0 < t ∧
      t < k * small.length j₁ + k * small.length j₂ ∧
      linear_equiv (small.scale k hk).graph
          (ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
            (bigDivisor D small hN hL k hk member hClosed hScale root))
          (ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
            (bigDivisor D small hN hL k hk member hClosed hScale root')) ∧
        0 < ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
          (bigDivisor D small hN hL k hk member hClosed hScale root')
          (chainVertex (small.scale k hk) j₁ j₂ t))

/-- **(MPC) suffices for `ForestContractionRank`.** -/
theorem forestContractionRank_of_markerFreePencilCover (hCond : D.Conditions small.core)
    (hCoreConn : small.core.Connected) (root : member.target.V)
    (hCover : MarkerFreePencilCover D small hN hL k hk member hClosed hScale root) :
    ForestContractionRank D small hN hL k hk member hClosed hScale root := by
  show rank (small.scale k hk).graph _ ≥ 1
  refine rank_ge_one_of_markerFree (D := D) (small.scale k hk) hCond
    ((small.scale k hk).graph_connected_of_coreConnected hCoreConn) _ (fun a ↦ ?_)
    (fun e j₁ j₂ hk2 ↦ ?_)
  · obtain ⟨root', hEquiv, hPos⟩ := hCover.1 a
    exact winnable_sub_one_chip_of_linear_equiv
      (DegenerateTransport.effective_pushDivisor_bigDivisor D small hN hL k hk member hClosed
        hScale root')
      hEquiv hPos
  · obtain ⟨root', t, ht0, htL, hEquiv, hPos⟩ := hCover.2 e j₁ j₂ hk2
    exact ⟨t, ht0, htL, winnable_sub_one_chip_of_linear_equiv
      (DegenerateTransport.effective_pushDivisor_bigDivisor D small hN hL k hk member hClosed
        hScale root')
      hEquiv hPos⟩

/-- **(MPC) from (T) and the double rows.**  The `D.fib` images are reached by
the member's branch vertices (`exists_pushDivisor_pos_fib`, unconditional); a
`double` chain is reached at the realization of any interior address of its own
row lying strictly inside the chain. -/
theorem markerFreePencilCover_of_transport (hCond : D.Conditions small.core)
    (root : member.target.V)
    (hT : PencilTransport D small hN hL k hk member hClosed hScale root)
    (hRow : DoubleRowInterior D small hN hL k hk member hClosed) :
    MarkerFreePencilCover D small hN hL k hk member hClosed hScale root := by
  refine ⟨fun a ↦ ?_, fun e j₁ j₂ hk2 ↦ ?_⟩
  · obtain ⟨root', hPos⟩ := exists_pushDivisor_pos_fib D small hN hL k hk member hClosed
      hScale a
    exact ⟨root', hT root', hPos⟩
  · obtain ⟨address, hRowEq, h0, hlt⟩ := hRow e j₁ j₂ hk2
    have hReal := vertexMap_sourcePoint_address D small hN hL k hk member hClosed hScale hCond
      address
    rw [hRowEq, hk2] at hReal
    obtain ⟨root', hPos⟩ :=
      (exists_pushDivisor_pos_iff D small hN hL k hk member hClosed hScale _).mpr
        ⟨addressVertex member.fullDim address, hReal⟩
    exact ⟨root', _, h0, hlt, hT root', hPos⟩

/-- **`ForestContractionRank` from (T) and the double rows.** -/
theorem forestContractionRank_of_transport_doubleRowInterior
    (hCond : D.Conditions small.core) (hCoreConn : small.core.Connected)
    (root : member.target.V)
    (hT : PencilTransport D small hN hL k hk member hClosed hScale root)
    (hRow : DoubleRowInterior D small hN hL k hk member hClosed) :
    ForestContractionRank D small hN hL k hk member hClosed hScale root :=
  forestContractionRank_of_markerFreePencilCover D small hN hL k hk member hClosed hScale
    hCond hCoreConn root
    (markerFreePencilCover_of_transport D small hN hL k hk member hClosed hScale hCond root
      hT hRow)

include hScale in
/-- `DoubleRowInterior` is orientation-free: it is the statement that the row's
own integral prefix lies strictly inside the chain. -/
theorem offsetVal_mem_Ioo_iff (e : Fin Q) (j : ℕ) :
    (0 < DegeneratePlacement.offsetVal (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed e j ∧
      DegeneratePlacement.offsetVal (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed e j <
        (D.bigSpec (small.scale k hk) hN hL).length e) ↔
    (0 < integralPrefix member.fullDim (memberRealization member hClosed)
        (member.ident.row.symm e) j ∧
      integralPrefix member.fullDim (memberRealization member hClosed)
        (member.ident.row.symm e) j < (D.bigSpec (small.scale k hk) hN hL).length e) :=
  offsetVal_mem_Ioo_iff_general (D.bigSpec (small.scale k hk) hN hL)
    (degenerateLength D small) member hClosed (fit D small hN hL k hk member hScale) e j

end Application

/-! ## 7.  The assembly, with the marker-free hypotheses -/

/-- **Brill--Noether existence from a closed odd member, through the marker-free set.**
`DegenerateBigDivisor.bnExists_of_degenerateMember` with its rank hypothesis supplied by
(MPC). -/
theorem bnExists_of_degenerateMember_of_markerFreePencilCover {n p N Q : ℕ}
    (small : Spec n p) (D : ExpansionData n p N Q) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (hCond : D.Conditions small.core) (hCoreConn : small.core.Connected)
    (u a : ℕ) (hu : 0 < u) (hk : 0 < 2 ^ a * u)
    (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) 4)
    (hClosed : member.Closed) (hOdd : Odd member.oddMult)
    (hScale : memberScale member = 2 ^ a * u)
    (root : member.target.V) (hInternal : ¬ IsLeafVertex member.target root)
    (hCover : MarkerFreePencilCover D small hN hL (2 ^ a * u) hk member hClosed hScale
      root) :
    BNExists (small.scale u hu).graph 1 4 :=
  bnExists_of_degenerateMember small D hN hL hCond u a hu hk member hClosed hOdd hScale
    root hInternal
    (forestContractionRank_of_markerFreePencilCover D small hN hL (2 ^ a * u) hk member
      hClosed hScale hCond hCoreConn root hCover)

/-- **The same, from (T) and the double rows**: small-side transport of the pencil, and one
interior address strictly inside each `double` chain. -/
theorem bnExists_of_degenerateMember_of_transport_doubleRowInterior {n p N Q : ℕ}
    (small : Spec n p) (D : ExpansionData n p N Q) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (hCond : D.Conditions small.core) (hCoreConn : small.core.Connected)
    (u a : ℕ) (hu : 0 < u) (hk : 0 < 2 ^ a * u)
    (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) 4)
    (hClosed : member.Closed) (hOdd : Odd member.oddMult)
    (hScale : memberScale member = 2 ^ a * u)
    (root : member.target.V) (hInternal : ¬ IsLeafVertex member.target root)
    (hT : PencilTransport D small hN hL (2 ^ a * u) hk member hClosed hScale root)
    (hRow : DoubleRowInterior D small hN hL (2 ^ a * u) hk member hClosed) :
    BNExists (small.scale u hu).graph 1 4 :=
  bnExists_of_degenerateMember small D hN hL hCond u a hu hk member hClosed hOdd hScale
    root hInternal
    (forestContractionRank_of_transport_doubleRowInterior D small hN hL (2 ^ a * u) hk
      member hClosed hScale hCond hCoreConn root hT hRow)

/-! ## 8.  An example: a loop displayed through a marker

The data below describe a small specification of the kind §2 and §3 are about.  A cubic,
loopless genus-six core with a digon (slots `3` and `4` both joining `1` to `2`) becomes,
after slot `3` is contracted, a core in which slot `4` is a **loop** at the merged vertex,
and a loopless small core must display it through a bivalent marker.  In `smallCore` the
loop is displayed as `3 : 1 → 9` and `4 : 9 → 1` through the marker `9`, split `1 + 3`
(`smallLength`); the small core has genus six with one four-valent vertex (`1`), so it lies
on the **non-cubic** branch of the witness.

`coords` are the target coordinates, at the degenerate request of `small`, of a member of
multiplicity one over the cubic core: zero exactly on column `6` (the fold of the
contracted digon row), and two on column `7`, the loop's.  The loop row of that member
consists of two occurrences over column `7`, each of realized length `2`, so its only
interior address on the loop sits at the **midpoint**, offset `2 k` of `4 k`, while the
marker sits at offset `k * small.length 3 = k`.  The marker is not reached, and the interior
of the loop is; `chainVertex_two` identifies the chain vertex at offset `2` with an interior
vertex of slot `4`.  This is why `MarkerFreePencilCover` asks for an interior vertex of each
chain rather than for its marker.  The example is recorded as data only: the statements
about the member in this paragraph are not formalized here. -/

namespace Seed57Loop

/-- The small core: a cubic genus-six core with a digon `3, 4`, with slot `3` contracted;
the loop left by slot `4` is displayed as `3 : 1 → 9` and `4 : 9 → 1` through the marker
`9`. -/
def smallCore : Utilities.Certificate.ExplicitPotential.Core 10 15 where
  tail := ![6, 1, 0, 1, 9, 1, 2, 2, 4, 7, 0, 2, 0, 4, 4]
  head := ![3, 6, 6, 9, 1, 5, 3, 3, 8, 8, 8, 7, 7, 5, 5]

theorem smallCore_loopless : ∀ j : Fin 15, smallCore.tail j ≠ smallCore.head j := by
  decide

/-- The requested small lengths.  The loop is split `1 + 3` by its marker. -/
def smallLength : Fin 15 → ℕ := ![3, 1, 3, 1, 3, 4, 2, 2, 1, 4, 1, 1, 3, 2, 2]

theorem smallLength_pos : ∀ j : Fin 15, 0 < smallLength j := by decide

def small : Spec 10 15 :=
  Spec.ofCore smallCore (by norm_num) smallCore_loopless smallLength smallLength_pos

theorem bigVertices_pos : 0 < 10 := by norm_num

/-- The small core is connected. -/
theorem small_core_connected : small.core.Connected :=
  Utilities.Certificate.ExplicitPotential.Core.connected_of_connectedCheckFast
    (by decide +kernel)

/-- The target coordinates at the degenerate request: zero on column `6` (the
contracted digon's fold), two on column `7` (the loop's). -/
def coords : Fin 15 → ℚ := ![1, 1, 1, 1, 1, 1, 0, 2, 1, 1, 1, 1, 1, 1, 1]

theorem chainVertex_two : chainVertex small 3 4 2 = small.interiorVertex 4 ⟨0, by decide⟩ := by
  rw [chainVertex_of_gt small (by decide) (by decide)]
  rfl

end Seed57Loop

/-! ## 9.  The supply layer and the final assembly

`MarkerFreePencilCoverSupply` asks for (MPC) at an internal root of **every** closed odd
member over **every** cubic connected genus-six expansion whose small core is connected and
whose doubles are loops.  It reaches Brill--Noether existence
(`exists_odd_bnExists_of_markerFreePencilCoverSupply`) and reduces to (T) and
`DoubleRowInterior` (`markerFreePencilCoverSupply_of_transport_doubleRowInterior`). -/

section Supply

universe u

/-- **The marker-free cover, for every closed odd member.**  At an internal root of every
closed member of odd multiplicity over the degenerate request of every cubic connected
genus-six expansion with connected small core, `MarkerFreePencilCover` holds.  The premise
`LoopDoubles` says that every `double` slot displays a loop; the data of the cubic-model
reduction satisfy it (`loopDoubles_data`), so the assembly loses nothing.  Without it the
statement could fail, by a **non-loop** marker on a slot whose row is a single occurrence,
where no pencil member reaches the open chain at all. -/
def MarkerFreePencilCoverSupply : Prop :=
  ∀ {n p N Q : ℕ} (small : Spec n p) (D : ExpansionData n p N Q) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e),
    D.Conditions small.core → LoopDoubles D small.core → small.core.Connected →
      D.bigCore.Cubic → D.bigCore.Connected → Q + 1 - N = 6 →
    ∀ (k : ℕ) (hk : 0 < k)
      (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) 4)
      (hClosed : member.Closed) (hScale : memberScale member = k),
      Odd member.oddMult →
        ∃ root : member.target.V, ¬ IsLeafVertex member.target root ∧
          MarkerFreePencilCover D small hN hL k hk member hClosed hScale root

/-- **The supply gives Brill--Noether existence** on an odd regular subdivision of the small
specification, for every closed member of odd multiplicity at the degenerate request. -/
theorem exists_odd_bnExists_of_markerFreePencilCoverSupply
    (hCover : MarkerFreePencilCoverSupply)
    {n p N Q : ℕ} (small : Spec n p) (D : ExpansionData n p N Q) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (hCond : D.Conditions small.core) (hLoop : LoopDoubles D small.core)
    (hCoreConn : small.core.Connected)
    (hCubic : D.bigCore.Cubic) (hConnBig : D.bigCore.Connected) (hgenus : Q + 1 - N = 6)
    (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) 4)
    (hClosed : member.Closed) (hOdd : Odd member.oddMult) :
    ∃ (u : ℕ) (hu : 0 < u), Odd u ∧ BNExists (small.scale u hu).graph 1 4 := by
  obtain ⟨a, u, hu, hOddU, hfac⟩ :=
    OddWitness.exists_eq_two_pow_mul_odd_pos (memberScale_pos member)
  have hk : 0 < 2 ^ a * u := hfac ▸ memberScale_pos member
  obtain ⟨root, hInternal, hCov⟩ := hCover small D hN hL hCond hLoop hCoreConn hCubic hConnBig
    hgenus (2 ^ a * u) hk member hClosed hfac hOdd
  exact ⟨u, hu, hOddU, bnExists_of_degenerateMember_of_markerFreePencilCover
    small D hN hL hCond hCoreConn u a hu hk member hClosed hOdd hfac root hInternal hCov⟩

/-- **The expansion data of the cubic-model reduction display loops only.**  In
`StableModelReduction.data` a `double` slot is `double j (mk.mate j)` for a first
half `j` of the marking, and `Marking.head_mate` closes it:
`C.head (mk.mate j) = C.tail j`. -/
theorem loopDoubles_data {n p : ℕ} {C : Utilities.Certificate.ExplicitPotential.Core n p}
    (mk : StableModelReduction.Marking C) (hs : StableModelReduction.Stable mk) :
    LoopDoubles (StableModelReduction.data mk hs) C := by
  intro e j₁ j₂ hk
  obtain ⟨a, rfl⟩ := (StableModelReduction.eEquiv mk hs).surjective e
  rcases a with x | ⟨j, hj⟩
  · rw [StableModelReduction.data_kind_inl] at hk
    cases hk
  · by_cases hf : mk.first j = true
    · rw [StableModelReduction.data_kind_inr_first mk hs hj hf] at hk
      obtain ⟨rfl, rfl⟩ := SlotKind.double.inj hk
      exact (mk.head_mate j hf).symm
    · rw [StableModelReduction.data_kind_inr_not_first mk hs hj (by simpa using hf)] at hk
      cases hk

/-- **The cubic-model reduction with its expansion datum exposed, and its doubles shown to
be loops.**  `RequestedExpandedEndpoints.exists_expansionModel`, re-run so that the datum is
`StableModelReduction.data` itself and `LoopDoubles` can be read off. -/
theorem exists_expansionModel_loopDoubles {n p : ℕ} (spec : Spec n p)
    (hConn : spec.core.Connected) (hGenus : n < p) :
    ∃ (n₀ p₀ : ℕ) (spec₀ : Spec n₀ p₀)
      (D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀))),
      D.Conditions spec₀.core ∧ LoopDoubles D spec₀.core ∧ D.bigCore.Cubic ∧
        D.bigCore.Connected ∧
        (∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e) ∧
        0 < 2 * (p₀ - n₀) ∧ spec₀.core.Connected ∧ n₀ < p₀ ∧
        (p₀ : ℤ) - n₀ = (p : ℤ) - n ∧
        (∀ (k : ℕ) (hk : 0 < k) (r d : ℤ),
          BNExists (spec₀.scale k hk).graph r d ↔
            BNExists (spec.scale k hk).graph r d) := by
  obtain ⟨n₀, p₀, spec₀, mk, hbase, hc₀, hb₀, hlt₀, hg₀, -, hbns₀⟩ :=
    StableModelPackaging.exists_markedSpec spec hConn hGenus
  have hstable : StableModelReduction.Stable mk :=
    BridgeReduction.stable_of_bridgeless mk spec₀.core_loopless hbase hb₀
  have hCond := StableModelReduction.conditions mk hstable spec₀.core_loopless
  exact ⟨n₀, p₀, spec₀, StableModelReduction.data mk hstable, hCond,
    loopDoubles_data mk hstable, StableModelReduction.bigCore_cubic mk hstable,
    StableModelReduction.bigCore_connected mk hstable hc₀,
    fun e ↦ ExpansionData.loopless_of_conditions hCond e, by omega, hc₀, hlt₀, hg₀, hbns₀⟩

/-- **`WitnessAssembly.exists_supplyInstance_of_c34`, with `LoopDoubles`.**  The same
proof, fed by `exists_expansionModel_loopDoubles`. -/
theorem exists_supplyInstance_of_c34_loopDoubles (hC34 : CountSchedule.C34 2)
    (H : CFGraph.{u}) (hconn : graph_connected H) (hgenus : genus H = 6) :
    ∃ (n₀ p₀ : ℕ) (spec₀ : Spec n₀ p₀)
      (D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀))),
      0 < 2 * (p₀ - n₀) ∧ (∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e) ∧
        D.Conditions spec₀.core ∧ LoopDoubles D spec₀.core ∧ spec₀.core.Connected ∧
        D.bigCore.Cubic ∧ D.bigCore.Connected ∧ 3 * (p₀ - n₀) + 1 - 2 * (p₀ - n₀) = 6 ∧
        (∀ (k : ℕ) (hk : 0 < k) (r d : ℤ),
          BNExists (spec₀.scale k hk).graph r d ↔
            BNExists ((UnitSubdivisionPresentation.spec H).scale k hk).graph r d) ∧
        ∃ member : FibreMember D.bigCore (fun e ↦ (degenerateLength D spec₀ e : ℚ)) 4,
          member.Closed ∧ Odd member.oddMult := by
  have hE := WitnessAssembly.card_edges_sub_card_vertices H hgenus
  obtain ⟨n₀, p₀, spec₀, D, hCond, hLoop, hCubic, hConnBig, hL, hN, hc₀, hlt₀, hg₀, hbns₀⟩ :=
    exists_expansionModel_loopDoubles (UnitSubdivisionPresentation.spec H)
      (WitnessAssembly.coreConnected_unitSpec H hconn) (by omega)
  have hgenusBig : 3 * (p₀ - n₀) + 1 - 2 * (p₀ - n₀) = 6 := by omega
  obtain ⟨member, hClosed, hHasOdd⟩ :=
    ClosedBoundaryMember.genusSix_exists_closed_hasOddMult_of_nonneg hC34 D.bigCore hCubic
      hConnBig hgenusBig (fun e ↦ (degenerateLength D spec₀ e : ℚ))
      (fun _ ↦ Nat.cast_nonneg _)
  exact ⟨n₀, p₀, spec₀, D, hN, hL, hCond, hLoop, hc₀, hCubic, hConnBig, hgenusBig, hbns₀,
    member, hClosed, (hasOddMult_iff_odd_oddMult member).mp hHasOdd⟩

/-- **The final assembly.**  From `CountSchedule.C34 2` and `MarkerFreePencilCoverSupply`,
every connected graph of genus six has a regular subdivision of odd order carrying a divisor
of degree four and rank at least one.  The count gives a closed odd member at the degenerate
request of the graph's cubic model (`exists_supplyInstance_of_c34_loopDoubles`), and the
supply turns it into Brill--Noether existence
(`exists_odd_bnExists_of_markerFreePencilCoverSupply`).  This is step 5 of `Assembly`. -/
theorem witness_of_c34_and_markerFreePencilCover (hC34 : CountSchedule.C34 2)
    (hCover : MarkerFreePencilCoverSupply) :
    ∀ H : CFGraph.{u}, graph_connected H → genus H = 6 →
      ∃ (N : ℕ) (hN : 0 < N), Odd N ∧
        BNExists (Utilities.Gonality.regularSubdivision H N hN) 1 4 := by
  intro H hconn hgenus
  obtain ⟨n₀, p₀, spec₀, D, hN, hL, hCond, hLoop, hc₀, hCubic, hConnBig, hg, hbns, member,
    hClosed, hOdd⟩ := exists_supplyInstance_of_c34_loopDoubles hC34 H hconn hgenus
  obtain ⟨u, hu, hOddU, hBN⟩ := exists_odd_bnExists_of_markerFreePencilCoverSupply hCover spec₀
    D hN hL hCond hLoop hc₀ hCubic hConnBig hg member hClosed hOdd
  exact ⟨u, hu, hOddU, (hbns u hu 1 4).mp hBN⟩

/-- **The replacement from (T) and the double rows.**  Transport at *some* root
(any root: `pencilTransport_of_pencilTransport`) and an interior address strictly
inside every `double` chain give the marker-free supply. -/
theorem markerFreePencilCoverSupply_of_transport_doubleRowInterior
    (h : ∀ {n p N Q : ℕ} (small : Spec n p) (D : ExpansionData n p N Q) (hN : 0 < N)
      (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e),
      D.Conditions small.core → LoopDoubles D small.core → small.core.Connected →
        D.bigCore.Cubic → D.bigCore.Connected → Q + 1 - N = 6 →
      ∀ (k : ℕ) (hk : 0 < k)
        (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) 4)
        (hClosed : member.Closed) (hScale : memberScale member = k),
        Odd member.oddMult →
          (∃ root : member.target.V,
            PencilTransport D small hN hL k hk member hClosed hScale root) ∧
          DoubleRowInterior D small hN hL k hk member hClosed) :
    MarkerFreePencilCoverSupply := by
  intro n p N Q small D hN hL hCond hLoop hCoreConn hCubic hConnBig hgenus k hk member hClosed
    hScale hOdd
  obtain ⟨⟨root₀, hT⟩, hRow⟩ := h small D hN hL hCond hLoop hCoreConn hCubic hConnBig hgenus
    k hk member hClosed hScale hOdd
  obtain ⟨root, hInternal⟩ := OddWitness.exists_internal_root member (by omega)
  exact ⟨root, hInternal, markerFreePencilCover_of_transport D small hN hL k hk member hClosed
    hScale hCond root (pencilTransport_of_pencilTransport D small hN hL k hk member hClosed
      hScale hT root) hRow⟩

end Supply

end DraismaVargas.Count.CorePencilCoverProducer
