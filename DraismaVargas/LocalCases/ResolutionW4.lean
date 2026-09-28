import DraismaVargas.LocalCases.W4TargetPairings
import DraismaVargas.LocalCases.ResolutionCoarseFine

/-!
# Sheet resolutions for the W4 r0 source blocks

For a non-dangling-valency-two wall block in source Case `{w4}`, the two
external branches either lie on the same side of the chosen `2+2` target
pairing or on opposite sides.  In the first situation the block stays joined
at that side and splits into singleton dangling sheets at the other endpoint.
In the second it stays joined across the new edge.  This is exactly the
`aux-r0-nd2` construction preceding Figure 26.

The construction below is degree-parametric and proves contraction to the
original wall partition for both `aux-r0-nd2` and `aux-r0-nd3`.  Exterior
refinement and the endpoint Riemann--Hurwitz receipts depend on the
occurrences and are proved on top of this construction.
-/

namespace DraismaVargas.LocalCases.ResolutionW4

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine

/-- The W4 r0-nd2 local resolution determined by the sides of its two
external target branches. -/
def nd2Resolution (wall : SheetPartition d) (anchor : Fin d)
    (firstRight secondRight : Bool) : LocalResolution d :=
  if _hSame : firstRight = secondRight then
    if firstRight then
      (splitResolutionAt wall anchor).reverse
    else
      splitResolutionAt wall anchor
  else
    joinedResolutionAt wall

/-- Every r0-nd2 side pattern contracts to the same wall block. -/
theorem nd2Resolution_contracts (wall : SheetPartition d) (anchor : Fin d)
    (firstRight secondRight : Bool) :
    (nd2Resolution wall anchor firstRight secondRight).ContractsTo wall := by
  unfold nd2Resolution
  split_ifs
  · exact LocalResolution.reverse_contracts
      (splitResolutionAt_contracts wall anchor)
  · exact splitResolutionAt_contracts wall anchor
  · exact joinedResolutionAt_contracts wall

/-- When the two external branches choose the same target endpoint, the new
edge separates the selected wall block into singleton sheets. -/
theorem nd2Resolution_newEdge_of_same (wall : SheetPartition d)
    (anchor : Fin d) (firstRight secondRight : Bool)
    (hSame : firstRight = secondRight) :
    (nd2Resolution wall anchor firstRight secondRight).newEdge =
      wall.splitBlock anchor := by
  subst secondRight
  cases firstRight <;> rfl

/-- When the two external branches choose opposite target endpoints, the new
edge retains the joined wall block. -/
theorem nd2Resolution_newEdge_of_ne (wall : SheetPartition d)
    (anchor : Fin d) (firstRight secondRight : Bool)
    (hNe : firstRight ≠ secondRight) :
    (nd2Resolution wall anchor firstRight secondRight).newEdge = wall := by
  unfold nd2Resolution
  rw [dif_neg hNe]
  rfl

/-- Under a same-side nd2 pattern, the endpoint carrying the two active
branches retains the wall partition. -/
theorem nd2Resolution_activeEndpoint_of_same (wall : SheetPartition d)
    (anchor : Fin d) (firstRight secondRight : Bool)
    (hSame : firstRight = secondRight) :
    (if firstRight then
        (nd2Resolution wall anchor firstRight secondRight).right
      else
        (nd2Resolution wall anchor firstRight secondRight).left) = wall := by
  subst secondRight
  cases firstRight <;> rfl

/-- Under a same-side nd2 pattern, the opposite endpoint splits the selected
wall block into singleton sheets. -/
theorem nd2Resolution_otherEndpoint_of_same (wall : SheetPartition d)
    (anchor : Fin d) (firstRight secondRight : Bool)
    (hSame : firstRight = secondRight) :
    (if firstRight then
        (nd2Resolution wall anchor firstRight secondRight).left
      else
        (nd2Resolution wall anchor firstRight secondRight).right) =
      wall.splitBlock anchor := by
  subst secondRight
  cases firstRight <;> rfl

/-- Under an opposite-side nd2 pattern both new endpoints retain the wall
partition. -/
theorem nd2Resolution_endpoints_of_ne (wall : SheetPartition d)
    (anchor : Fin d) (firstRight secondRight : Bool)
    (hNe : firstRight ≠ secondRight) :
    (nd2Resolution wall anchor firstRight secondRight).left = wall ∧
      (nd2Resolution wall anchor firstRight secondRight).right = wall := by
  unfold nd2Resolution
  rw [dif_neg hNe]
  exact ⟨rfl, rfl⟩

/-- The same-side W4 resolution gives every sheet in the selected wall block
unit index on the new target edge. -/
theorem nd2Resolution_newEdge_blockCard_of_same (wall : SheetPartition d)
    (anchor sheet : Fin d) (firstRight secondRight : Bool)
    (hSame : firstRight = secondRight) (hSheet : wall.Rel anchor sheet) :
    (nd2Resolution wall anchor firstRight secondRight).newEdge.blockCard sheet =
      1 := by
  rw [nd2Resolution_newEdge_of_same wall anchor firstRight secondRight hSame]
  exact wall.splitBlock_blockCard_of_rel anchor sheet hSheet

/-- The opposite-side W4 resolution gives the new target edge the original
wall-block index. -/
theorem nd2Resolution_newEdge_blockCard_of_ne (wall : SheetPartition d)
    (anchor sheet : Fin d) (firstRight secondRight : Bool)
    (hNe : firstRight ≠ secondRight) :
    (nd2Resolution wall anchor firstRight secondRight).newEdge.blockCard sheet =
      wall.blockCard sheet := by
  rw [nd2Resolution_newEdge_of_ne wall anchor firstRight secondRight hNe]

/-- For two actual W4 star labels, choose the r0-nd2 resolution prescribed by
one of the three target pairings. -/
noncomputable def nd2ResolutionForPairing
    {target : CFGraph} {wallVertex : target.V}
    (star : W4TargetPairings.FourStar target wallVertex) (pairing : Fin 3)
    (wallPartition : SheetPartition d) (anchor : Fin d)
    (firstBranch secondBranch : Fin 4) : LocalResolution d :=
  nd2Resolution wallPartition anchor
    (star.right pairing (star.edge firstBranch))
    (star.right pairing (star.edge secondBranch))

theorem nd2ResolutionForPairing_contracts
    {target : CFGraph} {wallVertex : target.V}
    (star : W4TargetPairings.FourStar target wallVertex) (pairing : Fin 3)
    (wallPartition : SheetPartition d) (anchor : Fin d)
    (firstBranch secondBranch : Fin 4) :
    (nd2ResolutionForPairing star pairing wallPartition anchor
      firstBranch secondBranch).ContractsTo wallPartition :=
  nd2Resolution_contracts wallPartition anchor _ _

/-! ### The r0-nd3 source block -/

/-- The W4 r0-nd3 resolution.  The singleton-side endpoint carries the
refined external-branch partition, as does the new edge; the endpoint carrying
the other two external branches retains the wall partition. -/
def nd3Resolution (wall fine : SheetPartition d)
    (hFine : fine.Refines wall) (singletonRight : Bool) : LocalResolution d :=
  if singletonRight then
    (fineResolution wall fine hFine).reverse
  else
    fineResolution wall fine hFine

/-- Every r0-nd3 side pattern contracts to the original wall block. -/
theorem nd3Resolution_contracts (wall fine : SheetPartition d)
    (hFine : fine.Refines wall) (singletonRight : Bool) :
    (nd3Resolution wall fine hFine singletonRight).ContractsTo wall := by
  cases singletonRight
  · exact fineResolution_contracts wall fine hFine
  · exact LocalResolution.reverse_contracts
      (fineResolution_contracts wall fine hFine)

/-- The singleton-side endpoint is `fine`, while the endpoint receiving the
other two external branches is `wall`. -/
theorem nd3Resolution_endpoint_partitions (wall fine : SheetPartition d)
    (hFine : fine.Refines wall) (singletonRight : Bool) :
    (if singletonRight then
        (nd3Resolution wall fine hFine singletonRight).right
      else
        (nd3Resolution wall fine hFine singletonRight).left) = fine ∧
    (if singletonRight then
        (nd3Resolution wall fine hFine singletonRight).left
      else
        (nd3Resolution wall fine hFine singletonRight).right) = wall := by
  cases singletonRight <;>
    simp [nd3Resolution, fineResolution, LocalResolution.reverse]

/-- Any occurrence on the singleton branch's side sees the fine endpoint. -/
theorem nd3Resolution_endpoint_of_same_side (wall fine : SheetPartition d)
    (hFine : fine.Refines wall) (singletonRight edgeRight : Bool)
    (hSame : edgeRight = singletonRight) :
    (if edgeRight then
        (nd3Resolution wall fine hFine singletonRight).right
      else
        (nd3Resolution wall fine hFine singletonRight).left) = fine := by
  subst edgeRight
  exact (nd3Resolution_endpoint_partitions wall fine hFine singletonRight).1

/-- Any occurrence on the other side sees the unchanged wall endpoint. -/
theorem nd3Resolution_endpoint_of_other_side (wall fine : SheetPartition d)
    (hFine : fine.Refines wall) (singletonRight edgeRight : Bool)
    (hNe : edgeRight ≠ singletonRight) :
    (if edgeRight then
        (nd3Resolution wall fine hFine singletonRight).right
      else
        (nd3Resolution wall fine hFine singletonRight).left) = wall := by
  cases edgeRight <;> cases singletonRight <;>
    simp_all [nd3Resolution, fineResolution, LocalResolution.reverse]

/-- The new target edge carries the singleton external branch's refined sheet
partition. -/
theorem nd3Resolution_newEdge (wall fine : SheetPartition d)
    (hFine : fine.Refines wall) (singletonRight : Bool) :
    (nd3Resolution wall fine hFine singletonRight).newEdge = fine := by
  cases singletonRight <;> rfl

/-- Choose the r0-nd3 resolution for one actual W4 target pairing after the
singleton external branch and its sheet partition have been identified. -/
noncomputable def nd3ResolutionForPairing
    {target : CFGraph} {wallVertex : target.V}
    (star : W4TargetPairings.FourStar target wallVertex) (pairing : Fin 3)
    (wallPartition fine : SheetPartition d)
    (hFine : fine.Refines wallPartition) (singletonBranch : Fin 4) :
    LocalResolution d :=
  nd3Resolution wallPartition fine hFine
    (star.right pairing (star.edge singletonBranch))

theorem nd3ResolutionForPairing_contracts
    {target : CFGraph} {wallVertex : target.V}
    (star : W4TargetPairings.FourStar target wallVertex) (pairing : Fin 3)
    (wallPartition fine : SheetPartition d)
    (hFine : fine.Refines wallPartition) (singletonBranch : Fin 4) :
    (nd3ResolutionForPairing star pairing wallPartition fine hFine
      singletonBranch).ContractsTo wallPartition :=
  nd3Resolution_contracts wallPartition fine hFine _

end DraismaVargas.LocalCases.ResolutionW4
