import DraismaVargasCount.M11StarCensusProof
import DraismaVargasCount.W4StarParity

/-!
# The W4 star census at every four-valent wall: Stages 1 and 3, and Stage 2 reduced to transports

Source: Draisma--Vargas Part I (arXiv:1909.12924), the inherited properties of limits
(`section-inherited-properties`: the target expansion and the limit matrix) and the auxiliary
cases `{aux-r0-nd2}`, `{aux-r0-nd3}` that produce Equation (1)'s W4 family; Vargas, Part II
(arXiv:2609.09109), the star of a codimension-one wall and `prop-signed-mult`.  Engine:
`StarCensusEngine`; worked example: `M11StarCensusProof`; the discrete case: `W4StarParity`.

## The result, in one paragraph

`W4StarParity` reduces the `w4` clause of `RegrowthWallInput.FamilyStarParity` to
`W4StarParity.NonDiscreteW4StarParity`, the star clause at four-valent regrowths whose
merged partition is not discrete.  Here that clause is reduced to the single statement
`W4NonDiscreteStarExhaustion` (Stage 2 (b): every star member is a frame isomorph of a
nonsingular position of Equation (1)), which is *equivalent* to the census
`W4NonDiscreteCensus` (`w4NonDiscreteStarExhaustion_iff`).  **Stages 1 (a) and 3 (c) are
proved at every four-valent wall, discrete or not, with no hypothesis**: Equation (1)'s
member at a nonsingular pairing is a wall-anchored star member for any full-dimensional
presentation of its datum (`position`, `rep`), and distinct pairings give distinct classes
(`repCls_injective`, by `W4PairingRigidity` through the engine's column rigidity).  Nothing
in the W4 balance family (`W4OutgoingStableRows.member`, `.equivalence`,
`.matrix_retained`) assumes discreteness; only the *exhaustion* route of `W4StarParity`
(`DiscreteW4Normalization`) does, and it is replaced here by the valency-free resolution
normal form (`normIso`).  Unconditionally, every four-valent star has at least two classes
(`two_le_card_star`): the wall's own pairing is nonsingular (`nonsingular_incoming`), and a
single nonzero term cannot make Equation (1) vanish (`exists_other_nonsingular`).

## What is proved

* **Stage 1 (a).**  `branchSquare` (the family's branch dictionary contracts to the
  identity on wall branches, at any wall), `position` (the member at any pairing, for any
  full-dimensional presentation, as a member of the wall's star, anchored at the wall
  itself), `rep` and `multNat_rep` (the class of a nonsingular position carries
  `|num (signedMult (lab q))|`).
* **Stage 3 (c).**  `pairing_eq_of_frameIso`, `repCls_injective`.
* **Bounds, unconditional.**  `nonsingular_incoming`, `exists_other_nonsingular`,
  `two_le_card_nonsingular`, `card_nonsingular_le_card_star`, `two_le_card_star`,
  `card_nonsingular_eq_two_of_card_star`.
* **Per-wall assembly.**  `Exhausts`, `repCls_surjective`, `census_of_exhausts`,
  `exhausts_of_census`, `starParityAt_of_exhausts` (the star clause at any four-valent
  wall from exhaustion).
* **Exhaustion at discrete walls** (non-vacuity of `Exhausts`): `exhausts_of_discrete`,
  from the partial engine of `W4StarParity`.
* **Stage 2 reduced to transports.**  `memberPlacement`, `memberResolution`,
  `memberCompatible`, `normIso`, `memberNV`, `memberNE` (every star member's normal form,
  with no discreteness), `PositionTransport`, `eq_index_of_transport` (a transport can
  only land at the member's own pairing), `nonsingular_of_transport` (and makes that
  pairing nonsingular), `exhausts_of_transports`.
* **Family.**  `W4NonDiscreteStarExhaustion`, `W4NonDiscreteCensus`,
  `w4NonDiscreteStarExhaustion_iff`, `w4NonDiscreteStarExhaustion_of_transports`,
  `nonDiscreteW4StarParity_of_exhaustion`, `familyStarParity_w4_of_exhaustion`,
  `starParityAt_of_four_valent`.

## What is not proved here (every surviving hypothesis, explicitly)

* **`FamilyStarParity (2+2) (4*2+2) (6*2+3) .w4` is not proved here.**  Its exact remaining
  hypothesis is `W4NonDiscreteStarExhaustion` (Stage 2 (b) at non-discrete walls),
  equivalent to `W4NonDiscreteCensus` (`w4NonDiscreteStarExhaustion_iff`).
  `W4NonDiscreteStarExhaustionProof` proves it (`w4NonDiscreteStarExhaustion`), and with it
  the `w4` clause with no hypothesis (`familyStarParity_w4`).  The antecedent (a four-valent,
  non-discrete regrowth) is not inhabited by any regrowth constructed in this library; the
  per-wall predicate `Exhausts` is a theorem at every discrete four-valent wall
  (`exhausts_of_discrete`).  A computer enumeration of walls (not part of this library,
  untrusted) finds four four-valent walls whose stars each have two classes at two
  *different* pairings, one near and one far, multiplicity one each.  That agrees with the
  census: `two_le_card_nonsingular` and `card_nonsingular_le_card_star` force exactly two
  nonsingular pairings at a two-class star, and distinct classes sit at distinct pairings.
  No counterexample was found.
* **What Stage 2 needs** (the hypothesis of `w4NonDiscreteStarExhaustion_of_transports`,
  supplied in `W4NonDiscreteStarExhaustionProof`): for each star member `m` with limit
  isomorphism `ψ`, a `ResolutionExpansionFree.TransportFree` along `ψ` from `m`'s read-off
  resolution onto the pasted resolution of Equation (1)'s member at `m`'s own pairing.
  Three of its ingredients are free at W4: the wall vertex is pinned
  (`W4WallExhaustion.map_merge`), the side map is `W4WallExhaustion.right_map`, and the
  pairing is forced (`eq_index_of_transport`).  The remaining ingredient is the resolution
  factor: the three endpoint and regrown-edge permutations and `endpoint_compatible`, i.e.
  that the member's own local resolution is the family's at that pairing, up to relabelling.
  Part I's incoming identification for W4 holds at *every* wall, with no discreteness
  (`W4IncomingPairingReceipts.stored_representative_normalization_of_forest`, used by
  `RegrowthWallInput.exists_w4Matched`), but on the member's *own* limit and input.
  Carrying it to the wall's family needs the naturality of the W4 blockwise family
  (`AuxR0SourceInput`'s block pictures and active profile) along `ψ`.  That is the W4 form
  of the transport the other star exhaustion proofs need (for example
  `M11StarExhaustionProof`).
* Nothing about the other nine families; nothing about schedules.

## Remarks

* **Nonsingular members.**  At a non-discrete wall only some of Equation (1)'s three members
  need be nonsingular.  At *every* four-valent wall at least two members are nonsingular
  (`two_le_card_nonsingular`), and at a two-class star exactly two are
  (`card_nonsingular_eq_two_of_card_star`).  The enumerated walls have two-class stars, so
  exactly two are nonsingular there.  That at every non-discrete wall exactly two (rather
  than three) are nonsingular is **not** proved and is not needed.
* **No discreteness in the family.**  `member`, `equivalence`, `matrix_retained`,
  `W4StarParity.fullDim`, `M11StarCensusProof.candidate_merge/old/edge` and `branchSquare`
  are all discreteness-free, so `position` exists at every four-valent wall.  On the
  discrete route of `W4StarParity`, discreteness enters in exactly one place:
  `W4WallExhaustion.normIso` and `W4WallExhaustion.limit_discrete`, through
  `DiscreteW4Normalization.datumIso`.  That is the exhaustion step, and `normIso` here
  replaces it.  (`W4StarParity.merge` and `limitIso` also use discreteness, but only to
  build its `Candidate`s; the engine's `hMerge` via `candidate_merge` does not need it.)
* **Exhaustion as transports.**  The reduction is stated in the shape of
  `exhausts_of_transports` (`PositionTransport`), with two refinements: at W4 the placement
  factor needs no transported input (it is the member's own
  `W4IncomingTargetNormalization.pairing`, and the index is forced), and a wall input exists
  natively on every member's limit (`RegrowthWallInput.w4Input` at the member).  What must
  be transported is the *comparison* of the two blockwise families (block pictures / active
  profile) along `ψ`.  M-11 needed the input itself.

## Consumers

`W4NonDiscreteStarExhaustionProof`, which proves `W4NonDiscreteStarExhaustion` and hence the
`w4` clause `familyStarParity_w4` that `StarSupplyAssembly` uses in step 2 (trivalent walls)
of `DraismaVargasCount/Assembly.lean`.
-/

namespace DraismaVargas.Count.W4NonDiscreteStarCensus

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4TargetPairings (FourStar)
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

section Positions

variable (w : Regrowth core y degree) (hy : Nondegenerate y)
  (star : FourStar (w.frame.limitTarget w.column) (mergeVertex w))

/-- The member of Equation (1)'s family at the pairing `q`, as a blockwise candidate. -/
noncomputable abbrev member (q : Fin 3) :=
  W4OutgoingStableRows.member (W4StarParity.input w hy star) q

/-- The family's own row/branch dictionary at the pairing `q`. -/
noncomputable abbrev equiv (q : Fin 3) :
    StableGraphIncidence.Equivalence w.limit (W4StarParity.datum w hy star q) :=
  W4OutgoingStableRows.equivalence (W4StarParity.input w hy star) q

theorem matrix_retained (q : Fin 3) (path : StablePath w.limit)
    (place : (w.frame.limitTarget w.column).edges) :
    StableSourceMatrix.matrix (W4StarParity.datum w hy star q) ((equiv w hy star q).row path)
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) (star.right q)
          (some place)) =
      StableSourceMatrix.matrix w.limit path place :=
  W4OutgoingStableRows.matrix_retained (W4StarParity.input w hy star) q path place

/-- **The branch square of the family member at any pairing**, with no discreteness:
the incidence equivalence sends each wall branch to a source vertex whose contraction is
that branch. -/
theorem branchSquare (q : Fin 3) (v : BranchVertex w.limit) :
    w.limit.sourceEndpoint
        (contractVertex (w.frame.limitTarget w.column) (mergeVertex w)
          ((equiv w hy star q).vertex v).1.1.1)
        ((equiv w hy star q).vertex v).1.1.2 = v.1 := by
  have hImage : ((equiv w hy star q).vertex v).1 =
      W4OutgoingStableRows.branchImage (W4StarParity.input w hy star) q v.1 := rfl
  by_cases hAt : v.1.1.1 = mergeVertex w
  · have hE : ((equiv w hy star q).vertex v).1 =
        (W4StarParity.datum w hy star q).sourceEndpoint
          (W4OutgoingSurvival.sideVertex (w.frame.limitTarget w.column) (mergeVertex w)
            (W4OutgoingStableRows.branchSide (W4StarParity.input w hy star) q
              (W4Assembly.WallBlock.ofSheet w.limit (mergeVertex w) v.1.1.2))) v.1.1.2 := by
      rw [hImage, W4OutgoingStableRows.branchImage, if_pos hAt]
      rfl
    rw [hE, StarCensusEngine.sourceEndpoint_contract _ w.limit _ _
      (M11StarCensusProof.candidate_refines (member w hy star q) _),
      W4StarParity.contract_sideVertex, ← hAt]
    exact w.limit.sourceEndpoint_self v.1
  · have hE : ((equiv w hy star q).vertex v).1 =
        (W4StarParity.datum w hy star q).sourceEndpoint
          (oldVertex (w.frame.limitTarget w.column) v.1.1.1) v.1.1.2 := by
      rw [hImage, W4OutgoingStableRows.branchImage, if_neg hAt]
      rfl
    rw [hE, StarCensusEngine.sourceEndpoint_contract _ w.limit _ _
      (M11StarCensusProof.candidate_refines (member w hy star q) _)]
    exact w.limit.sourceEndpoint_self v.1

variable (q : Fin 3) (fd : FullDimensionalSourcePresentation (W4StarParity.datum w hy star q) (Fin p))

/-- **The member of Equation (1)'s family at the pairing `q` is a member of the wall's
star**, for any full-dimensional presentation of its datum, wall-anchored, at any
four-valent wall -- discrete or not. -/
noncomputable def position : GeometricStar.StarMember hy w :=
  StarCensusEngine.starMember (w := w) (hy := hy) (E := equiv w hy star q) (fd := fd)
    (hRetained := matrix_retained w hy star q)
    (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
    (hMerge := M11StarCensusProof.candidate_merge _ (M11StarCensusProof.wall_join w))
    (hOld := M11StarCensusProof.candidate_old _) (hEdge := M11StarCensusProof.candidate_edge _)
    (fun v ↦ (M11StarCensusProof.refl_sourceVertexEquiv w _).trans (branchSquare w hy star q v))
    (M11StarCensusProof.refl_rowSquare w _ _ (fun _ ↦ rfl))

end Positions

/-! ## Separation -/

section Separation

open GeometricSegmentWalls (FrameIso)

variable (w : Regrowth core y degree) (hy : Nondegenerate y)
  (star : FourStar (w.frame.limitTarget w.column) (mergeVertex w))

/-- The frame of the position at the pairing `q`. -/
noncomputable abbrev frame (q : Fin 3)
    (fd : FullDimensionalSourcePresentation (W4StarParity.datum w hy star q) (Fin p)) :=
  StarCensusEngine.frame w hy (W4StarParity.datum w hy star q) (equiv w hy star q) fd

/-- **Two positions related by a frame isomorphism sit at the same pairing**, at any
four-valent wall.  The frame isomorphism fixes every column (both frames have the wall's
slot order and agree off the wall column), hence sends every occurrence label of the
first expansion to the same label of the second, and `W4PairingRigidity` applies. -/
theorem pairing_eq_of_frameIso {q q' : Fin 3}
    {fd : FullDimensionalSourcePresentation (W4StarParity.datum w hy star q) (Fin p)}
    {fd' : FullDimensionalSourcePresentation (W4StarParity.datum w hy star q') (Fin p)}
    (fi : FrameIso (frame w hy star q fd) (frame w hy star q' fd')) : q = q' := by
  have hagree := StarCensusEngine.agreeOffColumnSlot w hy fd fd' (matrix_retained w hy star q)
    (matrix_retained w hy star q')
  refine W4PairingRigidity.pairing_eq_of_expansionIso star q q' fi.datum.targetVertex
    fi.datum.targetEdge fi.datum.ends ?_
  intro label
  have h := GeometricSegmentWalls.FrameIso.targetEdge_map_of_agreeOffColumn fi hagree
    ((W4StarParity.columnEquiv w).symm label)
  change fi.datum.targetEdge (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w)
      (star.right q) ((W4StarParity.columnEquiv w) ((W4StarParity.columnEquiv w).symm label))) =
    occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) (star.right q')
      ((W4StarParity.columnEquiv w) ((W4StarParity.columnEquiv w).symm label)) at h
  rwa [Equiv.apply_symm_apply] at h

end Separation

/-! ## Census -/

section Census

variable (w : Regrowth core y degree) (hy : Nondegenerate y)
  (star : FourStar (w.frame.limitTarget w.column) (mergeVertex w))

/-- The pairing `q` is **nonsingular**: Equation (1)'s member there has nonzero
determinant, equivalently (`W4StarParity.fullDim`) it is full-dimensional. -/
def Nonsingular (q : Fin 3) : Prop :=
  (GluingDatum.LengthMatrixPresentation.matrix (W4StarParity.lab w hy star q).presentation).det ≠ 0

/-- The star member of a nonsingular position. -/
noncomputable def rep (q : Fin 3) (hq : Nonsingular w hy star q) : GeometricStar.StarMember hy w :=
  position w hy star q (W4StarParity.fullDim w hy star q hq)

theorem multNat_rep (q : Fin 3) (hq : Nonsingular w hy star q) :
    (GeometricStar.Star.toFibre (rep w hy star q hq).cls).multNat =
      (signedMult (W4StarParity.lab w hy star q).presentation).num.natAbs :=
  M11StarCensusProof.num_natAbs_eq_of_abs_eq (absMult_labelling_indep _ _)

/-- The positions' classes. -/
noncomputable def repCls (q : {q : Fin 3 // Nonsingular w hy star q}) : GeometricStar.Star hy w :=
  (rep w hy star q.1 q.2).cls

/-- **Stage 3 (c): distinct nonsingular positions are distinct star classes.** -/
theorem repCls_injective : Function.Injective (repCls w hy star) := by
  intro a b h
  obtain ⟨fi⟩ := Quotient.exact h
  exact Subtype.ext (pairing_eq_of_frameIso w hy star fi)

/-- **Exhaustion at one wall** (Stage 2 (b)): every member of the star is in
the class of some nonsingular position.  With Stages 1 and 3 it is
equivalent to the census at this wall (`census_of_exhausts`, `exhausts_of_census`). -/
def Exhausts : Prop :=
  ∀ m : GeometricStar.StarMember hy w, ∃ q : Fin 3, ∃ hq : Nonsingular w hy star q,
    m.cls = (rep w hy star q hq).cls

theorem repCls_surjective (hExh : Exhausts w hy star) : Function.Surjective (repCls w hy star) := by
  refine Quotient.ind ?_
  intro m
  obtain ⟨q, hq, h⟩ := hExh m
  exact ⟨⟨q, hq⟩, h.symm⟩

/-- **The W4 census at one four-valent wall from exhaustion**: the star is the set of
nonsingular pairings, each class carrying its term of Equation (1). -/
theorem census_of_exhausts (hExh : Exhausts w hy star) :
    ∃ e : {q : Fin 3 // Nonsingular w hy star q} ≃ GeometricStar.Star hy w,
      ∀ q, (GeometricStar.Star.toFibre (e q)).multNat =
        (signedMult (W4StarParity.lab w hy star q.1).presentation).num.natAbs :=
  ⟨Equiv.ofBijective _ ⟨repCls_injective w hy star, repCls_surjective w hy star hExh⟩,
    fun q ↦ multNat_rep w hy star q.1 q.2⟩

/-- **Conversely, the census implies exhaustion.** -/
theorem exhausts_of_census (e : {q : Fin 3 // Nonsingular w hy star q} ≃ GeometricStar.Star hy w) :
    Exhausts w hy star := by
  classical
  have hBij : Function.Bijective (repCls w hy star) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨repCls_injective w hy star, Fintype.card_congr e⟩
  intro m
  obtain ⟨q, hq⟩ := hBij.2 m.cls
  exact ⟨q.1, q.2, hq.symm⟩

theorem signedMult_eq_zero_of_not_nonsingular (q : Fin 3) (hq : ¬ Nonsingular w hy star q) :
    signedMult (W4StarParity.lab w hy star q).presentation = 0 := by
  unfold Nonsingular at hq
  simp only [not_not] at hq
  unfold signedMult
  rw [hq, mul_zero]

theorem signedMult_ne_zero_of_nonsingular (q : Fin 3) (hq : Nonsingular w hy star q) :
    signedMult (W4StarParity.lab w hy star q).presentation ≠ 0 := by
  have h := (W4StarParity.absMult_ne_zero_iff (W4StarParity.lab w hy star q).presentation).mpr hq
  unfold absMult at h
  exact fun h0 ↦ h (by rw [h0, abs_zero])

/-- **The star clause at a four-valent wall from exhaustion**, discrete or not. -/
theorem starParityAt_of_exhausts (hExh : Exhausts w hy star) :
    RegrowthWallInput.StarParityAt hy w := by
  obtain ⟨e, he⟩ := census_of_exhausts w hy star hExh
  refine StarCensusEngine.starParityAt_of_census
    (fun q ↦ signedMult (W4StarParity.lab w hy star q).presentation) ?_
    (RegrowthWallInput.w4_sum_signedMult_eq_zero w hy star (W4StarParity.initial w hy star))
    (Nonsingular w hy star) (signedMult_eq_zero_of_not_nonsingular w hy star) e he
  intro q
  by_cases hq : Nonsingular w hy star q
  · exact isIntegralMultiplicity (W4StarParity.fullDim w hy star q hq)
  · exact ⟨0, by rw [signedMult_eq_zero_of_not_nonsingular w hy star q hq]; simp⟩

/-! ### Unconditional bounds: at least two nonsingular positions, hence at least two classes -/

/-- **The wall's own pairing is always nonsingular**: the regrowth's own cover is a
full-dimensional member of the family there (`RegrowthWallInput.w4Matched`). -/
theorem nonsingular_incoming : Nonsingular w hy star (RegrowthWallInput.w4Incoming w star) := by
  have h := absMult_labelling_indep (RegrowthWallInput.w4Matched w hy star).labelling
    (W4StarParity.lab w hy star (RegrowthWallInput.w4Incoming w star))
  have hfd := (W4StarParity.absMult_ne_zero_iff _).mpr
    (RegrowthWallInput.w4Matched w hy star).det_ne_zero
  exact (W4StarParity.absMult_ne_zero_iff _).mp (h ▸ hfd)

/-- **Nonsingular positions come in at least pairs**: a single nonzero term cannot make
Equation (1) vanish. -/
theorem exists_other_nonsingular (q : Fin 3) (hq : Nonsingular w hy star q) :
    ∃ q' : Fin 3, q' ≠ q ∧ Nonsingular w hy star q' := by
  by_contra hNone
  push Not at hNone
  have hSum := RegrowthWallInput.w4_sum_signedMult_eq_zero w hy star (W4StarParity.initial w hy star)
  rw [Finset.sum_eq_single q (fun q' _ hne ↦ by
    by_cases h' : Nonsingular w hy star q'
    · exact absurd h' (hNone q' hne)
    · exact signedMult_eq_zero_of_not_nonsingular w hy star q' h')
    (fun h ↦ absurd (Finset.mem_univ q) h)] at hSum
  exact signedMult_ne_zero_of_nonsingular w hy star q hq hSum

/-- **At every four-valent wall at least two of Equation (1)'s three members are
nonsingular.** -/
theorem two_le_card_nonsingular : 2 ≤ Nat.card {q : Fin 3 // Nonsingular w hy star q} := by
  classical
  obtain ⟨q', hne, hq'⟩ := exists_other_nonsingular w hy star _ (nonsingular_incoming w hy star)
  rw [Nat.card_eq_fintype_card]
  have hSub : ({RegrowthWallInput.w4Incoming w star, q'} : Finset (Fin 3)) ⊆
      Finset.univ.filter (Nonsingular w hy star) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, nonsingular_incoming w hy star⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq'⟩
  have h := Finset.card_le_card hSub
  rw [Finset.card_pair hne.symm] at h
  rwa [Fintype.card_subtype]

/-- **At every four-valent wall the star has at least as many classes as nonsingular
positions, hence at least two**, with no exhaustion. -/
theorem card_nonsingular_le_card_star :
    Nat.card {q : Fin 3 // Nonsingular w hy star q} ≤ Nat.card (GeometricStar.Star hy w) :=
  Nat.card_le_card_of_injective _ (repCls_injective w hy star)

/-- **Every four-valent star has at least two classes.** -/
theorem two_le_card_star (hFour : (GluingDatum.incidentEdges (mergeVertex w)).card = 4) :
    2 ≤ Nat.card (GeometricStar.Star hy w) :=
  (two_le_card_nonsingular w hy (FourStar.of_card hFour)).trans
    (card_nonsingular_le_card_star w hy (FourStar.of_card hFour))

/-- **A two-class star forces exactly two nonsingular positions** (in the form a computer
enumeration can test): both sides of `card_nonsingular_le_card_star`
and `two_le_card_nonsingular`. -/
theorem card_nonsingular_eq_two_of_card_star (hStar : Nat.card (GeometricStar.Star hy w) = 2) :
    Nat.card {q : Fin 3 // Nonsingular w hy star q} = 2 :=
  le_antisymm (hStar ▸ card_nonsingular_le_card_star w hy star) (two_le_card_nonsingular w hy star)

/-! ### Exhaustion at discrete walls (non-vacuity of `Exhausts`) -/

/-- **At a discrete four-valent wall `Exhausts` is a theorem**: the partial engine of
`W4StarParity` puts every member in the class of a `W4StarParity.candidate`, whose frame
has the position's datum and core labels. -/
theorem exhausts_of_discrete (hFour : (GluingDatum.incidentEdges (mergeVertex w)).card = 4)
    (hDiscrete : w.limit.vertexPartition (mergeVertex w) = SheetPartition.discrete degree) :
    Exhausts w hy star := by
  intro m
  obtain ⟨⟨q, hq⟩, hcls⟩ := W4StarParity.partial_cls_surjective hFour hDiscrete star
    (Nonsingular w hy star) (W4StarParity.candidate w hy star hDiscrete)
    (W4StarParity.det_ne_zero_index w hy star hDiscrete hFour) m.cls
  refine ⟨q, hq, hcls.symm.trans (Quotient.sound ⟨?_⟩)⟩
  let F := (W4StarParity.candidate w hy star hDiscrete q hq).starMember.member.frame
  exact ⟨(GeometricSegmentWalls.FrameIso.refl F).datum,
    (GeometricSegmentWalls.FrameIso.refl F).overCore_vertex,
    (GeometricSegmentWalls.FrameIso.refl F).overCore_row⟩

end Census

/-! ## Stage 2 reduced to decoupled transports -/

section Transport

variable (w : Regrowth core y degree) (hy : Nondegenerate y)
  (star : FourStar (w.frame.limitTarget w.column) (mergeVertex w))
  (hFour : (GluingDatum.incidentEdges (mergeVertex w)).card = 4)

/-- **The placement an arbitrary star member presents**: its inherited four-star's side
assignment at its own pairing.  No discreteness: the pairing is
`W4IncomingTargetNormalization.pairing` of the member's own frame, and the merged vertex
is pinned by four-valency (`W4WallExhaustion.map_merge`). -/
noncomputable abbrev memberPlacement (other : Regrowth core y degree)
    (ψ : GeometricStar.LimitIso hy other w) :
    (other.frame.limitTarget other.column).edges → Bool :=
  (W4WallExhaustion.inheritedStar other ψ hFour star).right
    (W4WallExhaustion.index hFour star other ψ)

/-- **The local resolution an arbitrary star member presents**, read off its own endpoint
partitions (`M11WallExhaustion.incomingResolution`, valency-free). -/
noncomputable def memberResolution (other : Regrowth core y degree)
    (ψ : GeometricStar.LimitIso hy other w) : ResolutionM11.LocalResolution degree :=
  M11WallExhaustion.incomingResolution other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    (memberPlacement w hy star hFour other ψ)
    (W4WallExhaustion.pairing_placement other ψ hFour star)

theorem memberCompatible (other : Regrowth core y degree)
    (ψ : GeometricStar.LimitIso hy other w) :
    GlobalResolution.OldCompatible other.limit (mergeVertex other)
      (memberPlacement w hy star hFour other ψ) (memberResolution w hy star hFour other ψ) :=
  M11WallExhaustion.incomingOldCompatible other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    (memberPlacement w hy star hFour other ψ)
    (W4WallExhaustion.pairing_placement other ψ hFour star)
    other.frame.fullDim.targetConnected other.frame.fullDim.targetGenus

/-- **The member's normal form**: its datum is the resolution expansion of its own limit
at its own placement and resolution.  This replaces `DiscreteW4Normalization`, which needs
discreteness. -/
noncomputable def normIso (other : Regrowth core y degree)
    (ψ : GeometricStar.LimitIso hy other w) :
    GeometricDatumIso other.frame.data
      (GlobalResolution.datum other.limit (mergeVertex other)
        (memberPlacement w hy star hFour other ψ) (memberResolution w hy star hFour other ψ)
        (memberCompatible w hy star hFour other ψ)) :=
  M11WallExhaustion.datumIso other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    (memberPlacement w hy star hFour other ψ)
    (W4WallExhaustion.pairing_placement other ψ hFour star)
    other.frame.fullDim.targetConnected other.frame.fullDim.targetGenus

theorem memberNV (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)
    (vertex : other.frame.data.SourceVertex) :
    InheritedLimitBranches.vertexMap other vertex =
      GlobalResolution.sourceVertexMap other.limit (mergeVertex other)
        (memberPlacement w hy star hFour other ψ) (memberResolution w hy star hFour other ψ)
        (memberCompatible w hy star hFour other ψ)
        ((normIso w hy star hFour other ψ).sourceVertexEquiv vertex) :=
  M11WallExhaustion.sourceVertexMap_datumIso other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    (memberPlacement w hy star hFour other ψ)
    (W4WallExhaustion.pairing_placement other ψ hFour star)
    other.frame.fullDim.targetConnected other.frame.fullDim.targetGenus vertex

theorem memberNE (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)
    (edge : other.limit.SourceEdge) :
    (normIso w hy star hFour other ψ).sourceEdgeEquiv
        (InheritedLimitRows.edgeEmbedding other edge) =
      ResolutionExpansion.retainedSourceEdge other.limit (mergeVertex other)
        (memberPlacement w hy star hFour other ψ) (memberResolution w hy star hFour other ψ)
        (memberCompatible w hy star hFour other ψ) edge :=
  M11WallExhaustion.retainedSourceEdge_datumIso other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    (memberPlacement w hy star hFour other ψ)
    (W4WallExhaustion.pairing_placement other ψ hFour star)
    other.frame.fullDim.targetConnected other.frame.fullDim.targetGenus edge

/-- **The receipt a member must present to be received at the pairing `q`**: a decoupled
transport from its own normal form, along its limit isomorphism (all positions are
wall-anchored), onto the pasted resolution of Equation (1)'s member at `q`. -/
def PositionTransport (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)
    (q : Fin 3) : Type :=
  ResolutionExpansionFree.TransportFree (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm)
    (mergeVertex other) (mergeVertex w) (memberPlacement w hy star hFour other ψ) (star.right q)
    (memberResolution w hy star hFour other ψ) (M11StarCensusProof.pasted (member w hy star q))

/-- **A transport can only land at the member's own pairing**: its `side_map` field and
`W4WallExhaustion.right_map` give the same side assignment on all four star labels. -/
theorem eq_index_of_transport (other : Regrowth core y degree)
    (ψ : GeometricStar.LimitIso hy other w) (q : Fin 3)
    (t : PositionTransport w hy star hFour other ψ q) :
    q = W4WallExhaustion.index hFour star other ψ := by
  have key : ∀ a b : Fin 3,
      (∀ i : Fin 4, W4TargetPairings.Pairing.labelRight a i =
        W4TargetPairings.Pairing.labelRight b i) → a = b := by
    decide
  refine key _ _ fun i ↦ ?_
  have hSide := t.side_map (ψ.datum.targetEdge.symm (star.edge i))
  have hRight := W4WallExhaustion.right_map hFour star other ψ
    (ψ.datum.targetEdge.symm (star.edge i))
  change star.right q (ψ.datum.targetEdge (ψ.datum.targetEdge.symm (star.edge i))) = _ at hSide
  rw [Equiv.apply_symm_apply] at hSide hRight
  rw [← FourStar.right_edge, ← FourStar.right_edge, hSide, hRight]

/-- **A transport makes its pairing nonsingular**: the member's datum is then isomorphic
to Equation (1)'s member there, and multiplicity is an isomorphism invariant. -/
theorem nonsingular_of_transport (other : Regrowth core y degree)
    (ψ : GeometricStar.LimitIso hy other w) (q : Fin 3)
    (t : PositionTransport w hy star hFour other ψ q) : Nonsingular w hy star q := by
  have e : GeometricDatumIso other.frame.data (W4StarParity.datum w hy star q) :=
    (normIso w hy star hFour other ψ).trans
      (ResolutionExpansionFree.liftFree (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm)
        (mergeVertex other) (mergeVertex w) _ _ _ _ (memberCompatible w hy star hFour other ψ)
        (GlobalAssembly.blockwiseCompatible _ _ _ _ _ (member w hy star q).exterior) t)
  have habs := GeometricMultiplicity.absMult_eq_of_datumIso e other.frame.fullDim.connected
    other.frame.fullDim.labelling (W4StarParity.lab w hy star q)
  unfold Nonsingular
  rw [← W4StarParity.absMult_ne_zero_iff, habs, W4StarParity.absMult_ne_zero_iff]
  exact other.frame.fullDim.det_ne_zero

/-- **Stage 2 reduced to transports**: if every star member presents a decoupled
transport at its own pairing, the star is exhausted by the nonsingular positions.
Nonsingularity is not a hypothesis: the transport supplies it
(`nonsingular_of_transport`). -/
theorem exhausts_of_transports
    (h : ∀ m : GeometricStar.StarMember hy w, ∃ ψ : GeometricStar.LimitIso hy m.member w,
      Nonempty (PositionTransport w hy star hFour m.member ψ
        (W4WallExhaustion.index hFour star m.member ψ))) :
    Exhausts w hy star := by
  intro m
  obtain ⟨ψ, ⟨t⟩⟩ := h m
  set q := W4WallExhaustion.index hFour star m.member ψ
  have hq := nonsingular_of_transport w hy star hFour m.member ψ q t
  refine ⟨q, hq, ?_⟩
  exact StarCensusEngine.cls_eq_of_transport (w := w) (hy := hy)
    (E := equiv w hy star q) (fd := W4StarParity.fullDim w hy star q hq)
    (hRetained := matrix_retained w hy star q)
    (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
    (hMerge := M11StarCensusProof.candidate_merge _ (M11StarCensusProof.wall_join w))
    (hOld := M11StarCensusProof.candidate_old _) (hEdge := M11StarCensusProof.candidate_edge _)
    (fun v ↦ (M11StarCensusProof.refl_sourceVertexEquiv w _).trans (branchSquare w hy star q v))
    (M11StarCensusProof.refl_rowSquare w _ _ (fun _ ↦ rfl))
    (compat := GlobalAssembly.blockwiseCompatible _ _ _ _ _ (member w hy star q).exterior) rfl
    m ψ (normIso w hy star hFour m.member ψ) (memberNV w hy star hFour m.member ψ)
    (memberNE w hy star hFour m.member ψ) t

end Transport

/-! ## The family clause -/

section Family

/-- **Stage 2 at the non-discrete four-valent walls**: at every four-valent
regrowth whose merged partition is not discrete, for every labelling of its four
occurrences, every star member is in the class of a nonsingular position of Equation (1).
It is equivalent to `W4NonDiscreteCensus` (`w4NonDiscreteStarExhaustion_iff`).
At discrete walls the same per-wall statement is a theorem (`exhausts_of_discrete`). -/
def W4NonDiscreteStarExhaustion (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree),
    (GluingDatum.incidentEdges (mergeVertex w)).card = 4 →
    w.limit.vertexPartition (mergeVertex w) ≠ SheetPartition.discrete degree →
    ∀ star : FourStar (w.frame.limitTarget w.column) (mergeVertex w), Exhausts w hy star

/-- The census form of `W4NonDiscreteStarExhaustion`. -/
def W4NonDiscreteCensus (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree),
    (GluingDatum.incidentEdges (mergeVertex w)).card = 4 →
    w.limit.vertexPartition (mergeVertex w) ≠ SheetPartition.discrete degree →
    ∀ star : FourStar (w.frame.limitTarget w.column) (mergeVertex w),
      ∃ e : {q : Fin 3 // Nonsingular w hy star q} ≃ GeometricStar.Star hy w,
        ∀ q, (GeometricStar.Star.toFibre (e q)).multNat =
          (signedMult (W4StarParity.lab w hy star q.1).presentation).num.natAbs

variable {degree n p : ℕ}

theorem w4NonDiscreteCensus_of_exhaustion (h : W4NonDiscreteStarExhaustion degree n p) :
    W4NonDiscreteCensus degree n p :=
  fun core y hy w hFour hND star ↦ census_of_exhausts w hy star (h core y hy w hFour hND star)

theorem w4NonDiscreteStarExhaustion_of_census (h : W4NonDiscreteCensus degree n p) :
    W4NonDiscreteStarExhaustion degree n p :=
  fun core y hy w hFour hND star ↦ exhausts_of_census w hy star (h core y hy w hFour hND star).choose

/-- **`W4NonDiscreteStarExhaustion` is exactly the census at non-discrete walls.** -/
theorem w4NonDiscreteStarExhaustion_iff :
    W4NonDiscreteStarExhaustion degree n p ↔ W4NonDiscreteCensus degree n p :=
  ⟨w4NonDiscreteCensus_of_exhaustion, w4NonDiscreteStarExhaustion_of_census⟩

/-- **`W4NonDiscreteStarExhaustion` reduced to transports**, family-wide: one decoupled
transport per star member, at its own pairing, suffices. -/
theorem w4NonDiscreteStarExhaustion_of_transports
    (h : ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
      (hFour : (GluingDatum.incidentEdges (mergeVertex w)).card = 4),
      w.limit.vertexPartition (mergeVertex w) ≠ SheetPartition.discrete degree →
      ∀ (star : FourStar (w.frame.limitTarget w.column) (mergeVertex w))
        (m : GeometricStar.StarMember hy w), ∃ ψ : GeometricStar.LimitIso hy m.member w,
          Nonempty (PositionTransport w hy star hFour m.member ψ
            (W4WallExhaustion.index hFour star m.member ψ))) :
    W4NonDiscreteStarExhaustion degree n p :=
  fun core y hy w hFour hND star ↦
    exhausts_of_transports w hy star hFour (h core y hy w hFour hND star)

/-- **Star parity at every non-discrete four-valent regrowth**, from
`W4NonDiscreteStarExhaustion`. -/
theorem nonDiscreteW4StarParity_of_exhaustion (h : W4NonDiscreteStarExhaustion degree n p) :
    W4StarParity.NonDiscreteW4StarParity degree n p :=
  fun core y hy w hFour hND ↦
    starParityAt_of_exhausts w hy (FourStar.of_card hFour) (h core y hy w hFour hND _)

/-- **The `w4` clause of `FamilyStarParity` at genus six and degree four**, modulo the
non-discrete exhaustion `W4NonDiscreteStarExhaustion` alone (proved in
`W4NonDiscreteStarExhaustionProof`). -/
theorem familyStarParity_w4_of_exhaustion
    (h : W4NonDiscreteStarExhaustion (2 + 2) (4 * 2 + 2) (6 * 2 + 3)) :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w4 :=
  W4StarParity.familyStarParity_w4 (nonDiscreteW4StarParity_of_exhaustion h)

/-- **The whole `w4` clause, discrete and non-discrete walls alike, from exhaustion at
every four-valent wall**; at discrete walls the hypothesis is a theorem
(`exhausts_of_discrete`), so this is `familyStarParity_w4_of_exhaustion` again, stated
without the case split. -/
theorem starParityAt_of_four_valent (w : Regrowth core y degree) (hy : Nondegenerate y)
    (hFour : (GluingDatum.incidentEdges (mergeVertex w)).card = 4)
    (h : w.limit.vertexPartition (mergeVertex w) ≠ SheetPartition.discrete degree →
      Exhausts w hy (FourStar.of_card hFour)) :
    RegrowthWallInput.StarParityAt hy w := by
  by_cases hD : w.limit.vertexPartition (mergeVertex w) = SheetPartition.discrete degree
  · exact starParityAt_of_exhausts w hy (FourStar.of_card hFour)
      (exhausts_of_discrete w hy (FourStar.of_card hFour) hFour hD)
  · exact starParityAt_of_exhausts w hy (FourStar.of_card hFour) (h hD)

end Family

end DraismaVargas.Count.W4NonDiscreteStarCensus

