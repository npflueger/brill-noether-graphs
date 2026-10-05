module

public import DraismaVargas.LocalCases.StableSourceMatrix
public import DraismaVargas.LocalCases.W2R2Nd2SourceProfile

@[expose] public section

/-!
# The actual P wall columns differ only in the distinguished stable row

Source: Draisma--Vargas Part I, case `{w2-r2-nd2-P}` and Figure 36. The surviving
pair has indices `k,k+2` and one actual stable-path class `h`. Each wall
column consists of its distinguished reciprocal-index contribution and the
same background. Thus `Csmall - Clarge = (1/k - 1/(k+2)) e_h`. This is proved
from literal occurrences, not supplied as a matrix receipt.

Every linear functional annihilating the wall columns therefore vanishes on
`e_h`. This is the source's conclusion `c_h = 0` from the two limit-column
equations. The downstream `W2R2Nd2PExclusion` excludes P by identifying the
incoming column's cofactor-weighted background with a retained column's.

`column_eq_of_path_ne` and `annihilator_single_eq_zero_of_rank` generalize
the argument to every nd2 profile, including the same-direction return:
the two columns agree off the distinguished row, and rank ensures their
difference is nonzero. The explicit P reciprocal-index formula below remains
an independent source-facing computation, but the generalized rank form is
the one consumed by `W2R2Nd2PCofactor`.
-/

namespace DraismaVargas.LocalCases.W2R2Nd2PColumns

open DraismaVargas.Infrastructure
open W4Assembly W4StableSource W2R2Nd2SourceProfile W2R1Target

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {block : WallBlock data wall}

noncomputable local instance : DecidableEq (StablePath data) := Classical.decEq _

/-- The distinguished actual common stable class of the two survivors. -/
noncomputable def distinguishedPath (profile : SourceProfile data block) : StablePath data :=
  NonDanglingEdge.stablePath ⟨profile.small.1, profile.small_survives⟩

/-- Away from the distinguished row, the two wall columns agree even when
the surviving pair returns in one target direction. Only r0 occurrences
contribute to such a row, so the row-local transport theorem applies. -/
theorem column_eq_of_path_ne
    (hDivalent : (GluingDatum.incidentEdges wall).card = 2)
    (profile : SourceProfile data block)
    (hOthers : ∀ other : WallBlock data wall, other ≠ block →
      data.localRamification wall other = 0)
    {first second : target.edges} (hNe : first ≠ second)
    (hFirst : first ∈ GluingDatum.incidentEdges wall)
    (hSecond : second ∈ GluingDatum.incidentEdges wall)
    (path : StablePath data) (hPathNe : path ≠ distinguishedPath profile) :
    StableSourceMatrix.matrix data path first = StableSourceMatrix.matrix data path second := by
  apply StableSourceMatrix.column_eq_of_divalent_of_path_localRamification_zero
    wall hDivalent path ?_ hNe hFirst hSecond
  intro edge hSurvives hPath hAt
  apply hOthers (WallBlock.ofSheet data wall edge.1.2)
  intro hBlock
  have hIncident := (incident_wallBlock_sourceVertex_iff data block edge).mpr ⟨hAt, hBlock⟩
  have hEq : NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data) =
      distinguishedPath profile := by
    by_cases hSame : edge = profile.small.1
    · exact congrArg NonDanglingEdge.stablePath (Subtype.ext hSame)
    · exact stablePath_eq_of_consecutive
        ⟨fun h ↦ hSame (congrArg Subtype.val h), WallBlock.sourceVertex data wall block,
          hIncident, profile.small.2, profile.valency⟩
  exact hPathNe (hPath.symm.trans hEq)

/-- Inherited rank excludes a zero column difference. Since the difference
is supported on one row, every annihilator vanishes there. This extends the
Figure 36 cofactor argument to the residual same-direction unit pair, without
requiring the source's global pass-once theorem as an extra input. -/
theorem annihilator_single_eq_zero_of_rank
    (star : TwoStar target wall) (profile : SourceProfile data block)
    (hOthers : ∀ other : WallBlock data wall, other ≠ block →
      data.localRamification wall other = 0)
    (hRank : LinearIndependent ℚ (StableSourceMatrix.matrix data).col)
    (functional : (StablePath data → ℚ) →ₗ[ℚ] ℚ)
    (hAnnihilates : ∀ targetEdge : target.edges,
      functional ((StableSourceMatrix.matrix data).col targetEdge) = 0) :
    functional (Pi.single (distinguishedPath profile) (1 : ℚ)) = 0 := by
  classical
  let C := StableSourceMatrix.matrix data
  let h := distinguishedPath profile
  have hNe : star.edge 0 ≠ star.edge 1 := fun hEq ↦
    (by decide : (0 : Fin 2) ≠ 1) (star.edge_injective hEq)
  have hOff (path : StablePath data) (hPath : path ≠ h) :
      C path (star.edge 0) = C path (star.edge 1) :=
    column_eq_of_path_ne star.card_incidentEdges profile hOthers hNe
      (star.edge_mem_incidentEdges 0) (star.edge_mem_incidentEdges 1) path hPath
  have hCoefficient : C h (star.edge 0) - C h (star.edge 1) ≠ 0 := by
    intro hZero
    apply hNe
    apply hRank.injective
    funext path
    by_cases hPath : path = h
    · exact hPath ▸ sub_eq_zero.mp hZero
    · exact hOff path hPath
  have hDifference : C.col (star.edge 0) - C.col (star.edge 1) =
      (C h (star.edge 0) - C h (star.edge 1)) • Pi.single h (1 : ℚ) := by
    funext path
    change C path (star.edge 0) - C path (star.edge 1) =
      (C h (star.edge 0) - C h (star.edge 1)) * (Pi.single h (1 : ℚ) : StablePath data → ℚ) path
    by_cases hPath : path = h
    · rw [hPath, Pi.single_eq_same, mul_one]
    · rw [Pi.single_eq_of_ne hPath, mul_zero, hOff path hPath, sub_self]
  have hImage := congrArg functional hDifference
  rw [map_sub, map_smul, hAnnihilates, hAnnihilates, sub_self, smul_eq_mul] at hImage
  exact (mul_eq_zero.mp hImage.symm).resolve_left hCoefficient

end DraismaVargas.LocalCases.W2R2Nd2PColumns
