module

public import DraismaVargasCount.RowHairpinPosition
public import DraismaVargas.Infrastructure.NonnegativeRationalRealization

@[expose] public section

/-!
# Literal integral prefixes of a closed-cone source row

The integral position is a sum of the actual source lengths in the canonical
nonnegative realization. Zero occurrences are retained: different source
vertices may occupy the same integral position.
-/

namespace DraismaVargas.Count.RowRealizedPosition

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases W4StableSource FullDimensionalSource
open RowWalk RowPosition PendantRetraction SlotMoment
open Utilities.Certificate.SubdivisionGraph

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Position obtained by literally traversing the integral source occurrences. -/
noncomputable def integralPrefix
    (fd : FullDimensionalSourcePresentation data coordinate)
    (realization : data.NonnegativeIntegralRealization) (path : StablePath data)
    (j : ℕ) : ℕ :=
  ((orderedRow fd.pathEnds path).take j |>.map realization.sourceLength).sum

/-- Denominator clearing commutes with each actual ordered-row prefix,
including prefixes containing zero-length occurrences. -/
theorem integralPrefix_cast
    (fd : FullDimensionalSourcePresentation data coordinate) (z : coordinate → ℚ)
    (hNonnegative : ∀ c, 0 ≤ z c) (path : StablePath data) (j : ℕ) :
    (integralPrefix fd
      (NonnegativeIntegralRealization.ofNonnegativeRational data
        (fun edge ↦ z (fd.labelling.targetEdge.symm edge))
        (fun _ ↦ hNonnegative _)) path j : ℚ) =
      (data.rationalRealizationScale (fun edge ↦ z (fd.labelling.targetEdge.symm edge)) : ℚ) *
        prefixPosition fd z path j := by
  simp only [integralPrefix, Nat.cast_list_sum, List.map_map, Function.comp_def,
    NonnegativeIntegralRealization.ofNonnegativeRational_sourceLength_cast,
    sourceEdgeLength, prefixPosition, ← List.sum_map_mul_left]

/-- The canonical closed-cone realization of a counted member. -/
noncomputable def memberRealization {n p : ℕ}
    {core : Utilities.Certificate.ExplicitPotential.Core n p} {y : Fin p → ℚ}
    (member : FibreMember core y degree) (hClosed : member.Closed) :
    member.data.NonnegativeIntegralRealization :=
  NonnegativeIntegralRealization.ofNonnegativeRational member.data
    (fun edge ↦ member.coords (member.fullDim.labelling.targetEdge.symm edge))
    (fun _ ↦ hClosed _)

/-- The actual common scale used for target and source occurrence lengths. -/
noncomputable def memberScale {n p : ℕ}
    {core : Utilities.Certificate.ExplicitPotential.Core n p} {y : Fin p → ℚ}
    (member : FibreMember core y degree) : ℕ :=
  member.data.rationalRealizationScale
    (fun edge ↦ member.coords (member.fullDim.labelling.targetEdge.symm edge))

theorem memberScale_pos {n p : ℕ}
    {core : Utilities.Certificate.ExplicitPotential.Core n p} {y : Fin p → ℚ}
    (member : FibreMember core y degree) : 0 < memberScale member :=
  member.data.rationalRealizationScale_pos _

theorem member_integralPrefix_cast {n p : ℕ}
    {core : Utilities.Certificate.ExplicitPotential.Core n p} {y : Fin p → ℚ}
    (member : FibreMember core y degree) (hClosed : member.Closed)
    (slot : Fin p) (j : ℕ) :
    (integralPrefix member.fullDim (memberRealization member hClosed)
      (member.ident.row.symm slot) j : ℚ) =
      (memberScale member : ℚ) * prefixPosition member.fullDim member.coords
        (member.ident.row.symm slot) j :=
  integralPrefix_cast member.fullDim member.coords hClosed _ _

/-- The total realized length is exactly the scaled requested slot length. -/
theorem member_integralPrefix_full {n p : ℕ}
    {core : Utilities.Certificate.ExplicitPotential.Core n p} (y : Fin p → ℕ)
    (member : FibreMember core (fun slot ↦ (y slot : ℚ)) degree)
    (hClosed : member.Closed) (slot : Fin p) :
    integralPrefix member.fullDim (memberRealization member hClosed)
      (member.ident.row.symm slot)
      (orderedRow member.fullDim.pathEnds (member.ident.row.symm slot)).length =
      memberScale member * y slot := by
  have h := member_integralPrefix_cast member hClosed slot
    (orderedRow member.fullDim.pathEnds (member.ident.row.symm slot)).length
  rw [member_prefixPosition_full] at h
  exact_mod_cast h

/-- Literal row-interior chip mass at one integral position. The finite sum
retains every preimage, including collisions of zero-length occurrences. -/
noncomputable def collisionCoefficient
    (fd : FullDimensionalSourcePresentation data coordinate)
    (realization : data.NonnegativeIntegralRealization) (root : target.V)
    (path : StablePath data) (offset : ℕ) : ℤ := by
  classical
  exact ∑ i : Fin ((orderedRow fd.pathEnds path).length - 1),
    if integralPrefix fd realization path (i.val + 1) = offset then
      retractedFibre root (retractVertex (rowVertex fd path (i.val + 1))) else 0

/-- Aggregation does not lose 2-integrality when several actual row vertices
occupy one realized position. No injectivity or positive-length hypothesis
enters this statement. -/
theorem member_collisionCoefficient_mem {n p : ℕ}
    {core : Utilities.Certificate.ExplicitPotential.Core n p} (y : Fin p → ℤ)
    (member : FibreMember core (fun slot ↦ (y slot : ℚ)) degree)
    (hClosed : member.Closed) (hOdd : Odd member.oddMult) (slot : Fin p)
    {root : member.target.V} (hInternal : ¬ IsLeafVertex member.target root)
    (offset : ℕ) :
    (collisionCoefficient member.fullDim (memberRealization member hClosed) root
      (member.ident.row.symm slot) offset : ℚ) *
        ((offset : ℚ) / memberScale member) ∈ oddDenominatorSubring := by
  classical
  simp only [collisionCoefficient, Int.cast_sum, Finset.sum_mul]
  apply oddDenominatorSubring.sum_mem
  intro i _
  by_cases hOffset : integralPrefix member.fullDim (memberRealization member hClosed)
      (member.ident.row.symm slot) (i.val + 1) = offset
  · simp only [ite_eq_left hOffset]
    have hScale : (memberScale member : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (memberScale_pos member))
    have hPosition := member_integralPrefix_cast member hClosed slot (i.val + 1)
    rw [hOffset] at hPosition
    have hDivide : (offset : ℚ) / memberScale member =
        prefixPosition member.fullDim member.coords (member.ident.row.symm slot)
          (i.val + 1) := by
      rw [hPosition, mul_div_cancel_left₀ _ hScale]
    rw [hDivide]
    apply RowHairpinPosition.member_weighted_prefix_mem y member hOdd slot hInternal
    have hi := i.isLt
    omega
  · simp only [ite_eq_right hOffset, Int.cast_zero, zero_mul]
    exact oddDenominatorSubring.zero_mem

/-- The interior part of the literal row-position pushforward, on the actual
scaled request specification. Core coefficients are zero here: this isolates
exactly the part entering slot moments. Identification with the transported
pencil, and alignment of row direction with the slot's tail, are separate statements. -/
noncomputable def interiorRowPushforward {n p : ℕ} (spec : Spec n p)
    (member : FibreMember spec.core (fun slot ↦ (spec.length slot : ℚ)) degree)
    (hClosed : member.Closed) (root : member.target.V) :
    CFDiv (spec.scale (memberScale member) (memberScale_pos member)).graph
  | Sum.inl _ => 0
  | Sum.inr point => collisionCoefficient member.fullDim (memberRealization member hClosed)
      root (member.ident.row.symm point.1) (point.2.val + 1)

theorem interiorRowPushforward_interior {n p : ℕ} (spec : Spec n p)
    (member : FibreMember spec.core (fun slot ↦ (spec.length slot : ℚ)) degree)
    (hClosed : member.Closed) (root : member.target.V) (slot : Fin p)
    (offset : Fin ((spec.scale (memberScale member) (memberScale_pos member)).length slot - 1)) :
    interiorRowPushforward spec member hClosed root
      ((spec.scale (memberScale member) (memberScale_pos member)).interiorVertex slot offset) =
    collisionCoefficient member.fullDim (memberRealization member hClosed) root
      (member.ident.row.symm slot) (offset.val + 1) := rfl

/-- The exact per-slot divisibility conclusion for the constructed interior
pushforward. It is proved here, not assumed of the individual terms. -/
theorem interiorRowPushforward_slotMoment {n p : ℕ} (spec : Spec n p)
    (member : FibreMember spec.core (fun slot ↦ (spec.length slot : ℚ)) degree)
    (hClosed : member.Closed) (hOdd : Odd member.oddMult)
    {root : member.target.V} (hInternal : ¬ IsLeafVertex member.target root)
    (a : ℕ) (hScale : 2 ^ a ∣ memberScale member) (slot : Fin p) :
    ((2 ^ a : ℕ) : ℤ) ∣ InteriorFiring.slotMoment
      (spec.scale (memberScale member) (memberScale_pos member))
      (interiorRowPushforward spec member hClosed root) slot := by
  apply slotMoment_dvd_two_pow_of_terms _ _ (memberScale member) a
    (memberScale_pos member) hScale slot
  intro offset
  rw [interiorRowPushforward_interior]
  exact member_collisionCoefficient_mem (fun slot ↦ (spec.length slot : ℤ))
    member hClosed hOdd slot hInternal (offset.val + 1)

/-- The same literal collision sum with independently chosen directions on
the request slots. Reversal is made at the full scaled slot length, not at
an unrelated row or an unscaled offset. -/
noncomputable def orientedInteriorRowPushforward {n p : ℕ} (spec : Spec n p)
    (member : FibreMember spec.core (fun slot ↦ (spec.length slot : ℚ)) degree)
    (hClosed : member.Closed) (root : member.target.V) (reverse : Fin p → Bool) :
    CFDiv (spec.scale (memberScale member) (memberScale_pos member)).graph
  | Sum.inl _ => 0
  | Sum.inr point => collisionCoefficient member.fullDim (memberRealization member hClosed)
      root (member.ident.row.symm point.1)
      (if reverse point.1 then memberScale member * spec.length point.1 - (point.2.val + 1)
        else point.2.val + 1)

/-- Every direction convention gives the exact moment divisibility. Thus
tail/head alignment is a matter of geometric identification only, not an additional
arithmetic assumption. Zero-length collisions remain aggregated literally. -/
theorem orientedInteriorRowPushforward_slotMoment {n p : ℕ} (spec : Spec n p)
    (member : FibreMember spec.core (fun slot ↦ (spec.length slot : ℚ)) degree)
    (hClosed : member.Closed) (hOdd : Odd member.oddMult)
    {root : member.target.V} (hInternal : ¬ IsLeafVertex member.target root)
    (reverse : Fin p → Bool) (a : ℕ) (hScale : 2 ^ a ∣ memberScale member)
    (slot : Fin p) :
    ((2 ^ a : ℕ) : ℤ) ∣ InteriorFiring.slotMoment
      (spec.scale (memberScale member) (memberScale_pos member))
      (orientedInteriorRowPushforward spec member hClosed root reverse) slot := by
  apply slotMoment_dvd_two_pow_of_terms _ _ (memberScale member) a
    (memberScale_pos member) hScale slot
  intro offset
  change ((collisionCoefficient member.fullDim (memberRealization member hClosed) root
      (member.ident.row.symm slot)
      (if reverse slot then memberScale member * spec.length slot - (offset.val + 1)
        else offset.val + 1) : ℤ) : ℚ) * _ ∈ _
  by_cases hReverse : reverse slot = true
  · simp only [hReverse, ↓reduceIte]
    let c := collisionCoefficient member.fullDim (memberRealization member hClosed) root
      (member.ident.row.symm slot) (memberScale member * spec.length slot - (offset.val + 1))
    have hTerm := member_collisionCoefficient_mem (fun slot ↦ (spec.length slot : ℤ))
      member hClosed hOdd slot hInternal
      (memberScale member * spec.length slot - (offset.val + 1))
    have hBound : offset.val + 1 ≤ memberScale member * spec.length slot := by
      have h := offset.isLt
      simp only [Spec.scale_length] at h
      omega
    have hScaleQ : (memberScale member : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (memberScale_pos member))
    have hTotal : (c : ℚ) * (spec.length slot : ℚ) ∈ oddDenominatorSubring :=
      oddDenominatorSubring.mul_mem (intCast_mem _ c) (natCast_mem _ _)
    have hDifference := oddDenominatorSubring.sub_mem hTotal hTerm
    simp only [Nat.cast_sub hBound, Nat.cast_mul] at hDifference
    convert hDifference using 1
    dsimp [c]
    field_simp
    ring
  · simp only [hReverse]
    exact member_collisionCoefficient_mem (fun slot ↦ (spec.length slot : ℤ))
      member hClosed hOdd slot hInternal (offset.val + 1)

end DraismaVargas.Count.RowRealizedPosition

