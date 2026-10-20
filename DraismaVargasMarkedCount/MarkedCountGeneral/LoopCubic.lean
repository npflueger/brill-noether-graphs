module

public import DraismaVargasMarkedCount.MarkedCountGeneral.TypedFrame

@[expose] public section

/-!
# The loop case of the drop lemma, part 1: distinct marks make the core marked-cubic

The loop reversal
(`DropSmooth.exists_loop_reversal`) reads the hairpin of a loop row on the unmarked regrowth of
`DenomRegrow`, which needs the marks to be distinct source vertices (`IsMarkedCubic`, through
`DenomRegrow.hInj`). This module derives `IsMarkedCubic` from a typed frame whose marks are
distinct: a core vertex has the incidence degree of its branch vertex
(`nonDanglingValency_eq_incidenceDegree`), which is two at a mark and three elsewhere.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open Utilities.Certificate.ExplicitPotential (Core)

namespace LoopCubic

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}


/-- The incidence degree of a core vertex is the surviving valency of its branch vertex. -/
theorem nonDanglingValency_eq_incidenceDegree (κ : TypedFrame core mark types degree)
    (B : MarkedBranchVertex κ.data (markSet κ.markSource)) :
    nonDanglingValency κ.data B.1 = core.incidenceDegree (κ.ident.vertex B) := by
  classical
  have h1 : core.incidenceDegree (κ.ident.vertex B) =
      ∑ slot, Count.coreIncidence core (κ.ident.vertex B) slot := rfl
  rw [h1, ← StablePathCount.card_incidentEdges]
  simp_rw [← κ.ident.incidence B]
  rw [Equiv.sum_comp κ.ident.row.symm (fun r ↦ markedIncidenceCount κ.data
    (markSet κ.markSource) B.1 r)]
  unfold markedIncidenceCount
  exact Finset.card_eq_sum_card_fiberwise fun _ _ ↦ Finset.mem_univ _

/-- **A typed frame with distinct marks has a marked-cubic core**: the marks have incidence
degree two (`markValency`), every other vertex three (`trivalent`). -/
theorem isMarkedCubic_of_injective (κ : TypedFrame core mark types degree)
    (hInj : Function.Injective κ.markSource) : IsMarkedCubic core mark where
  injective := by
    intro i j h
    apply hInj
    rw [← κ.ident.vertex_mark i, ← κ.ident.vertex_mark j] at h
    exact congrArg Subtype.val (κ.ident.vertex.injective h)
  mark_degree j := by
    rw [← κ.ident.vertex_mark j]
    exact (nonDanglingValency_eq_incidenceDegree κ _).symm.trans
      (κ.fullDim.markValency _ (mem_markSet _ j))
  other_degree v hv := by
    obtain ⟨B, rfl⟩ := κ.ident.vertex.surjective v
    refine (nonDanglingValency_eq_incidenceDegree κ B).symm.trans ?_
    rcases B.2 with h | h
    · exact le_antisymm (κ.fullDim.trivalent _) h
    · exfalso
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
      apply hv
      refine ⟨j, ?_⟩
      rw [← κ.ident.vertex_mark j]
      congr 1
      exact Subtype.ext hj

end LoopCubic

end DraismaVargas.Count.MarkedCountGeneral
