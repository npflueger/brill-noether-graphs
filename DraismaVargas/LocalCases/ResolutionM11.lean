module

public import DraismaVargas.Infrastructure.TargetTreePotential
public import DraismaVargas.Infrastructure.TargetBranchRegion
public import DraismaVargas.LocalCases.BalancingValencyTwo

@[expose] public section

/-!
# The local sheet partitions in case `w2-r2-nd3-M-11`

This is the partition-theoretic core of Figure 32 in Draisma--Vargas Part I.
The distinguished wall class has two sheets.  The first two resolutions use
singleton classes at the trivalent endpoint and a joined class at the new
leaf; the third uses the joined class at both divalent endpoints and along
the new edge.  In all three cases the endpoint join contracts to the same
two-sheet wall class.

The theorem `m11_local_resolution` packages the exact contraction statements
with Equation (6), already proved in `BalancingValencyTwo`.
`wallRegionSwap_preserves_valid` supplies the global remote-sheet transport
once a Boolean target region has been chosen: only incidences crossing its
boundary need use the indiscrete two-sheet wall block. `wallBranchSwap` makes
that region canonical: delete the wall vertex and take the component of any
chosen root.  What the M-11 case then needs beyond this file is to construct
the three outgoing target/gluing data and to identify which component is
swapped; the remote transport need not be reproved.
-/

namespace DraismaVargas.LocalCases.ResolutionM11

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancingValencyTwo
open Utilities

/-- The endpoint and new-edge relations of one local resolution. -/
structure LocalResolution (d : ℕ) where
  left : SheetPartition d
  right : SheetPartition d
  newEdge : SheetPartition d
  edge_refines_left : newEdge.Refines left
  edge_refines_right : newEdge.Refines right

namespace LocalResolution

/-- Contracting the new edge produces `wall`. -/
def ContractsTo (resolution : LocalResolution d) (wall : SheetPartition d) : Prop :=
  SheetPartition.IsJoin resolution.left resolution.right wall

/-- Reverse the two endpoints of a local target expansion. -/
def reverse (resolution : LocalResolution d) : LocalResolution d where
  left := resolution.right
  right := resolution.left
  newEdge := resolution.newEdge
  edge_refines_left := resolution.edge_refines_right
  edge_refines_right := resolution.edge_refines_left

@[simp] theorem reverse_left (resolution : LocalResolution d) :
    resolution.reverse.left = resolution.right := rfl

@[simp] theorem reverse_right (resolution : LocalResolution d) :
    resolution.reverse.right = resolution.left := rfl

@[simp] theorem reverse_newEdge (resolution : LocalResolution d) :
    resolution.reverse.newEdge = resolution.newEdge := rfl

/-- Reversing the new target edge preserves its contracted wall partition. -/
theorem reverse_contracts {resolution : LocalResolution d}
    {wall : SheetPartition d} (h : resolution.ContractsTo wall) :
    resolution.reverse.ContractsTo wall :=
  SheetPartition.isJoin_comm h

/-- The Riemann--Hurwitz inequality at one endpoint, restricted to the sheets
in one original wall block.  The local continuation of Draisma--Vargas is
assembled block by block, so this is the exact local verification unit. -/
def RiemannHurwitzAtBlock (wall endpoint : SheetPartition d)
    (incident : List (SheetPartition d)) (anchor : Fin d) : Prop :=
  ∀ sheet, wall.Rel anchor sheet →
    (incident.map
        (fun edge => (edge.blockCountWithin endpoint sheet : ℤ))).sum - 2 ≥
      (endpoint.blockCard sheet : ℤ) * ((incident.length : ℤ) - 2)

/-- Global endpoint Riemann--Hurwitz is exactly the conjunction of the local
checks on the canonical blocks of any wall partition.  This is the assembly
step that lets the source's case analysis work one wall class at a time. -/
theorem riemannHurwitzAt_iff_forall_wallBlock
    (wall endpoint : SheetPartition d) (incident : List (SheetPartition d)) :
    SheetPartition.RiemannHurwitzAt endpoint incident ↔
      ∀ anchor, wall.repr anchor = anchor →
        RiemannHurwitzAtBlock wall endpoint incident anchor := by
  constructor
  · intro hGlobal anchor _ sheet _
    exact hGlobal sheet
  · intro hBlocks sheet
    let anchor := wall.repr sheet
    have hAnchor : wall.repr anchor = anchor := wall.repr_idem sheet
    have hSheet : wall.Rel anchor sheet := wall.rel_repr_left sheet
    exact hBlocks anchor hAnchor sheet hSheet

/-- Every one-edge leaf satisfies the blockwise Riemann--Hurwitz inequality,
independently of the endpoint and edge partitions. -/
theorem riemannHurwitzAtBlock_leaf
    (wall endpoint edge : SheetPartition d) (anchor : Fin d) :
    RiemannHurwitzAtBlock wall endpoint [edge] anchor := by
  intro sheet _
  have hCount := edge.blockCountWithin_pos endpoint sheet
  have hCard := endpoint.blockCard_pos sheet
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil]
  omega

/-- Select one prescribed local resolution on a distinguished wall block and
use a background resolution on all other blocks. -/
def onBlock (wall : SheetPartition d) (distinguished : Fin d)
    (selected : LocalResolution d)
    (background : Fin d → LocalResolution d) (anchor : Fin d) :
    LocalResolution d :=
  if wall.Rel distinguished anchor then selected else background anchor

@[simp] theorem onBlock_of_rel (wall : SheetPartition d)
    (distinguished : Fin d) (selected : LocalResolution d)
    (background : Fin d → LocalResolution d) (anchor : Fin d)
    (hRel : wall.Rel distinguished anchor) :
    onBlock wall distinguished selected background anchor = selected := by
  rw [onBlock, ite_eq_left hRel]

theorem onBlock_of_not_rel (wall : SheetPartition d)
    (distinguished : Fin d) (selected : LocalResolution d)
    (background : Fin d → LocalResolution d) (anchor : Fin d)
    (hRel : ¬wall.Rel distinguished anchor) :
    onBlock wall distinguished selected background anchor = background anchor := by
  rw [onBlock, ite_eq_right hRel]

/-- Common contraction is preserved when one wall block replaces the
background resolution. -/
theorem onBlock_contracts (wall : SheetPartition d)
    (distinguished : Fin d) (selected : LocalResolution d)
    (background : Fin d → LocalResolution d)
    (hSelected : selected.ContractsTo wall)
    (hBackground : ∀ anchor, (background anchor).ContractsTo wall) :
    ∀ anchor,
      (onBlock wall distinguished selected background anchor).ContractsTo wall := by
  intro anchor
  by_cases hRel : wall.Rel distinguished anchor
  · rw [onBlock, ite_eq_left hRel]
    exact hSelected
  · rw [onBlock, ite_eq_right hRel]
    exact hBackground anchor

end LocalResolution

/-- Figure 32, resolutions 1 and 2, on the distinguished two-sheet block.
Their local partitions coincide; the two global candidates differ by the
remote branch pairing of the singleton sheets. -/
def splitResolution : LocalResolution 2 where
  left := SheetPartition.indiscrete 2
  right := SheetPartition.discrete 2
  newEdge := SheetPartition.discrete 2
  edge_refines_left := SheetPartition.refines_indiscrete _
  edge_refines_right := SheetPartition.Refines.refl _

/-- Figure 32, resolution 3, whose new edge has index two. -/
def joinedResolution : LocalResolution 2 where
  left := SheetPartition.indiscrete 2
  right := SheetPartition.indiscrete 2
  newEdge := SheetPartition.indiscrete 2
  edge_refines_left := SheetPartition.Refines.refl _
  edge_refines_right := SheetPartition.Refines.refl _

/-! ### The same local resolutions inside an arbitrary sheet set -/

/-- The split M-11 pattern on one selected wall block.  That entire block is
split into singleton sheets at the trivalent endpoint and on the new edge;
all other wall blocks are unchanged. -/
def splitResolutionAt (wall : SheetPartition d) (anchor : Fin d) :
    LocalResolution d where
  left := wall
  right := wall.splitBlock anchor
  newEdge := wall.splitBlock anchor
  edge_refines_left := wall.splitBlock_refines anchor
  edge_refines_right := SheetPartition.Refines.refl _

/-- The joined M-11 pattern retains the wall partition at both endpoints and
on the new edge. -/
def joinedResolutionAt (wall : SheetPartition d) : LocalResolution d where
  left := wall
  right := wall
  newEdge := wall
  edge_refines_left := SheetPartition.Refines.refl _
  edge_refines_right := SheetPartition.Refines.refl _

/-- Contracting the split pattern rejoins it to the original wall partition. -/
theorem splitResolutionAt_contracts (wall : SheetPartition d) (anchor : Fin d) :
    (splitResolutionAt wall anchor).ContractsTo wall :=
  SheetPartition.isJoin_left_of_refines (wall.splitBlock_refines anchor)

/-- Contracting the joined pattern also recovers the wall partition. -/
theorem joinedResolutionAt_contracts (wall : SheetPartition d) :
    (joinedResolutionAt wall).ContractsTo wall :=
  SheetPartition.isJoin_left_of_refines (SheetPartition.Refines.refl wall)

/-- Every sheet in the selected M-11 block has unit index on the split new
edge. -/
theorem splitResolutionAt_newEdge_blockCard (wall : SheetPartition d)
    (anchor sheet : Fin d) (hSheet : wall.Rel anchor sheet) :
    (splitResolutionAt wall anchor).newEdge.blockCard sheet = 1 :=
  wall.splitBlock_blockCard_of_rel anchor sheet hSheet

/-- On a two-sheet M-11 wall block, the new leaf endpoint satisfies its local
Riemann--Hurwitz inequality. -/
theorem splitResolutionAt_left_riemannHurwitzAtBlock
    (wall : SheetPartition d) (anchor : Fin d)
    (hCard : wall.blockCard anchor = 2) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (splitResolutionAt wall anchor).left
      [(splitResolutionAt wall anchor).newEdge] anchor := by
  intro sheet hSheet
  have hSheetCard : wall.blockCard sheet = 2 := by
    unfold SheetPartition.blockCard
    rw [← wall.block_eq_of_rel hSheet]
    exact hCard
  have hBlockCount :
      (wall.splitBlock anchor).blockCountWithin wall sheet = 2 := by
    rw [wall.splitBlock_blockCountWithin_of_rel anchor sheet hSheet, hSheetCard]
  simp [splitResolutionAt, hBlockCount, hSheetCard]

/-- At the split candidate's trivalent endpoint, the selected wall block has
become singleton sheets. Hence the new edge and both unchanged incident edge
relations each induce exactly one local block. -/
theorem splitResolutionAt_right_riemannHurwitzAtBlock
    (wall firstExternal secondExternal : SheetPartition d) (anchor : Fin d) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (splitResolutionAt wall anchor).right
      [(splitResolutionAt wall anchor).newEdge, firstExternal, secondExternal]
      anchor := by
  intro sheet hSheet
  have hSingleton := wall.splitBlock_block_of_rel anchor sheet hSheet
  have hFirst := SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton
    firstExternal (wall.splitBlock anchor) sheet hSingleton
  have hSecond := SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton
    secondExternal (wall.splitBlock anchor) sheet hSingleton
  have hCard := wall.splitBlock_blockCard_of_rel anchor sheet hSheet
  simp [splitResolutionAt, hFirst, hSecond, hCard]

/-- The split trivalent-endpoint check is valid when the canonical anchor
used by blockwise assembly is any representative of the selected block. -/
theorem splitResolutionAt_right_riemannHurwitzAtBlock_of_rel
    (wall firstExternal secondExternal : SheetPartition d)
    (distinguished anchor : Fin d) (hAnchor : wall.Rel distinguished anchor) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (splitResolutionAt wall distinguished).right
      [(splitResolutionAt wall distinguished).newEdge,
        firstExternal, secondExternal] anchor := by
  intro sheet hSheet
  have hSelected : wall.Rel distinguished sheet := by
    exact hAnchor.trans hSheet
  have hSingleton := wall.splitBlock_block_of_rel distinguished sheet hSelected
  have hFirst := SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton
    firstExternal (wall.splitBlock distinguished) sheet hSingleton
  have hSecond := SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton
    secondExternal (wall.splitBlock distinguished) sheet hSingleton
  have hCard := wall.splitBlock_blockCard_of_rel distinguished sheet hSelected
  simp [splitResolutionAt, hFirst, hSecond, hCard]

/-- At either endpoint of the joined candidate, the new edge contributes one
wall block. An unchanged exterior edge with two blocks on the selected wall
class then gives the required divalent inequality. -/
theorem joinedResolutionAt_endpoint_riemannHurwitzAtBlock
    (wall external : SheetPartition d) (anchor : Fin d)
    (hExternal : ∀ sheet, wall.Rel anchor sheet →
      external.blockCountWithin wall sheet = 2) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (joinedResolutionAt wall).left
      [(joinedResolutionAt wall).newEdge, external] anchor := by
  intro sheet hSheet
  have hOld := hExternal sheet hSheet
  simp [joinedResolutionAt, hOld]

/-- At a joined divalent endpoint, the new edge contributes one block and
any exterior partition refining the wall contributes at least one. Thus the
Riemann--Hurwitz inequality is automatic; the earlier exact-two-block lemma
records the M-11 determinant geometry but is not needed for validity. -/
theorem joinedResolutionAt_endpoint_riemannHurwitzAtBlock_any
    (wall external : SheetPartition d) (anchor : Fin d) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (joinedResolutionAt wall).left
      [(joinedResolutionAt wall).newEdge, external] anchor := by
  intro sheet _
  have hExternal := external.blockCountWithin_pos wall sheet
  simp [joinedResolutionAt]
  omega

/-- Every sheet retains its wall-block index on the joined new edge. -/
theorem joinedResolutionAt_newEdge_blockCard (wall : SheetPartition d)
    (sheet : Fin d) :
    (joinedResolutionAt wall).newEdge.blockCard sheet = wall.blockCard sheet :=
  rfl

/-- The three candidates of Figure 32.  `first` and `second` have the same
partitions on the distinguished block; their global remote pairings differ. -/
inductive Candidate where
  | first
  | second
  | third
  deriving DecidableEq

/-- The local partition pattern associated to a Figure 32 candidate. -/
def Candidate.resolution : Candidate → LocalResolution 2
  | .first | .second => splitResolution
  | .third => joinedResolution

/-- The split resolution contracts to the two-sheet wall class. -/
theorem splitResolution_contracts :
    splitResolution.ContractsTo (SheetPartition.indiscrete 2) :=
  SheetPartition.isJoin_indiscrete_left _

/-- The joined resolution contracts to the same two-sheet wall class. -/
theorem joinedResolution_contracts :
    joinedResolution.ContractsTo (SheetPartition.indiscrete 2) :=
  SheetPartition.isJoin_indiscrete_left _

/-- Every Figure 32 candidate has the required common wall specialization. -/
theorem Candidate.resolution_contracts (candidate : Candidate) :
    candidate.resolution.ContractsTo (SheetPartition.indiscrete 2) := by
  cases candidate <;> simp only [Candidate.resolution]
  · exact splitResolution_contracts
  · exact splitResolution_contracts
  · exact joinedResolution_contracts

/-- The new edge in the split candidates consists of two singleton lifts. -/
theorem splitResolution_newEdge_blockCard (i : Fin 2) :
    splitResolution.newEdge.blockCard i = 1 := by
  fin_cases i <;> decide

/-- The new edge in the third candidate is one lift of index two. -/
theorem joinedResolution_newEdge_blockCard (i : Fin 2) :
    joinedResolution.newEdge.blockCard i = 2 := by
  fin_cases i <;> decide

/-- Both unchanged incident edge relations refine the trivalent endpoint of
the two split candidates. -/
theorem splitResolution_external_refines_right :
    (SheetPartition.discrete 2).Refines splitResolution.right :=
  SheetPartition.Refines.refl _

/-- The unchanged singleton relation refines either divalent endpoint of the
joined candidate. -/
theorem joinedResolution_external_refines_left :
    (SheetPartition.discrete 2).Refines joinedResolution.left :=
  SheetPartition.refines_indiscrete _

theorem joinedResolution_external_refines_right :
    (SheetPartition.discrete 2).Refines joinedResolution.right :=
  SheetPartition.refines_indiscrete _

/-- At the leaf endpoint of the split candidates, two singleton lifts of the
new edge meet the two-sheet vertex class and satisfy Riemann--Hurwitz. -/
theorem splitResolution_left_riemannHurwitz :
    SheetPartition.RiemannHurwitzAt splitResolution.left
      [splitResolution.newEdge] := by
  intro i
  fin_cases i <;> decide

/-- At the trivalent endpoint of the split candidates, all three incident
relations are singleton partitions on the distinguished block. -/
theorem splitResolution_right_riemannHurwitz :
    SheetPartition.RiemannHurwitzAt splitResolution.right
      [splitResolution.newEdge, SheetPartition.discrete 2,
        SheetPartition.discrete 2] := by
  intro i
  fin_cases i <;> decide

/-- Each endpoint of the joined candidate is divalent: the old incident edge
has two singleton lifts and the new edge has one lift of index two. -/
theorem joinedResolution_endpoint_riemannHurwitz :
    SheetPartition.RiemannHurwitzAt joinedResolution.left
      [joinedResolution.newEdge, SheetPartition.discrete 2] := by
  intro i
  fin_cases i <;> decide

/-! ## Remote sheet transport at the wall block -/

/-- The global form of the M-11 remote pairing change.  Mark any target
region by Boolean vertex/edge predicates and swap the two sheets there.  If
every boundary incidence lies at an indiscrete two-sheet vertex block, the
resulting whole gluing datum remains valid and its quotient source is
adjacency-equivalent to the original one. -/
theorem wallRegionSwap_preserves_valid
    {target : CFGraph} (data : GluingDatum target 2) (hValid : data.Valid)
    (vertexMoved : target.V → Bool) (edgeMoved : target.edges → Bool)
    (hBoundaryLeft : ∀ edge,
      edgeMoved edge ≠ vertexMoved (edge : target.V × target.V).1 →
        data.vertexPartition (edge : target.V × target.V).1 =
          SheetPartition.indiscrete 2)
    (hBoundaryRight : ∀ edge,
      edgeMoved edge ≠ vertexMoved (edge : target.V × target.V).2 →
        data.vertexPartition (edge : target.V × target.V).2 =
          SheetPartition.indiscrete 2) :
    (GluingDatum.SheetRelabeling.ofRegion (data := data) vertexMoved edgeMoved
      (Equiv.swap (0 : Fin 2) 1)
      (fun edge hDifferent sheet ↦ by
        rw [hBoundaryLeft edge hDifferent]
        exact SheetPartition.indiscrete_rel _ _)
      (fun edge hDifferent sheet ↦ by
        rw [hBoundaryRight edge hDifferent]
        exact SheetPartition.indiscrete_rel _ _)).apply.Valid := by
  apply GluingDatum.SheetRelabeling.valid
  exact hValid

/-- Swap two sheets in the same wall block on the component of `root` after
deleting `wall`. Every vertex/edge relabelling mismatch is automatically at
`wall`, where the transposition preserves the partition because the two
sheets lie in one block. This is the remote operation in M-11 at arbitrary
ambient degree, not only in the isolated degree-two local model. -/
def wallBranchSwap
    {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)
    (wall root : target.V) (hRoot : root ≠ wall)
    (first second : Fin degree)
    (hTogether : (data.vertexPartition wall).Rel first second) :
    data.SheetRelabeling :=
  GluingDatum.SheetRelabeling.ofRegion
    (TargetBranchRegion.vertexMoved wall root hRoot)
    (TargetBranchRegion.edgeMoved wall root hRoot)
    (Equiv.swap first second)
    (fun edge hDifferent sheet ↦ by
      rw [TargetBranchRegion.boundary_left wall root hRoot edge hDifferent]
      exact SheetPartition.swap_apply_rel_self_of_rel _ hTogether sheet)
    (fun edge hDifferent sheet ↦ by
      rw [TargetBranchRegion.boundary_right wall root hRoot edge hDifferent]
      exact SheetPartition.swap_apply_rel_self_of_rel _ hTogether sheet)

/-- The component-defined branch swap preserves the validity of the entire
gluing datum, including source connectedness. -/
theorem wallBranchSwap_preserves_valid
    {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)
    (hValid : data.Valid)
    (wall root : target.V) (hRoot : root ≠ wall)
    (first second : Fin degree)
    (hTogether : (data.vertexPartition wall).Rel first second) :
    (wallBranchSwap data wall root hRoot first second hTogether).apply.Valid := by
  exact GluingDatum.SheetRelabeling.valid _ hValid

/-! ## Whole finite local models -/

/-- The leaf--trivalent target of candidates 1 and 2.  Vertex `0` is the new
leaf and vertex `1` is the trivalent endpoint. -/
def splitLocalTarget : CFGraph where
  V := Fin 4
  edges := Multiset.ofList [(0, 1), (1, 2), (1, 3)]
  loopless := by decide

/-- A whole degree-two gluing datum realizing the split local pattern.  The
two candidates differ only in how the two singleton sheets continue into the
remote branches at vertices `2` and `3`. -/
def splitLocalDatum : GluingDatum splitLocalTarget 2 where
  degree_pos := by decide
  vertexPartition := fun (vertex : Fin 4) =>
    if vertex = 0 then SheetPartition.indiscrete 2
    else SheetPartition.discrete 2
  edgePartition := fun _ => SheetPartition.discrete 2
  refines_left := fun _ => SheetPartition.discrete_refines _
  refines_right := fun _ => SheetPartition.discrete_refines _

/-- The divalent--divalent target of candidate 3. -/
def joinedLocalTarget : CFGraph where
  V := Fin 4
  edges := Multiset.ofList [(0, 1), (1, 2), (2, 3)]
  loopless := by decide

/-- A whole degree-two gluing datum realizing the index-two joined local
pattern. -/
def joinedLocalDatum : GluingDatum joinedLocalTarget 2 where
  degree_pos := by decide
  vertexPartition := fun (vertex : Fin 4) =>
    if vertex = 1 ∨ vertex = 2 then SheetPartition.indiscrete 2
    else SheetPartition.discrete 2
  edgePartition := fun edge =>
    if (show Fin 4 × Fin 4 from edge.1) = (1, 2) then
      SheetPartition.indiscrete 2
    else SheetPartition.discrete 2
  refines_left :=
    @of_decide_eq_true _ Fintype.decidableForallFintype (by decide +kernel)
  refines_right :=
    @of_decide_eq_true _ Fintype.decidableForallFintype (by decide +kernel)

/-- The complete split local datum satisfies connectedness and every local
Riemann--Hurwitz inequality, including the two remote leaf endpoints. -/
theorem splitLocalDatum_valid : splitLocalDatum.Valid := by
  exact (GluingDatum.check_eq_true_iff splitLocalDatum).mp (by decide +kernel)

/-- The complete joined local datum satisfies connectedness and every local
Riemann--Hurwitz inequality. -/
theorem joinedLocalDatum_valid : joinedLocalDatum.Valid := by
  exact (GluingDatum.check_eq_true_iff joinedLocalDatum).mp (by decide +kernel)

@[simp] theorem splitLocalTarget_genus : genus splitLocalTarget = 0 := by rfl
@[simp] theorem joinedLocalTarget_genus : genus joinedLocalTarget = 0 := by rfl

@[simp] theorem splitLocalSource_genus : genus splitLocalDatum.sourceGraph = 0 := by
  decide +kernel

@[simp] theorem joinedLocalSource_genus : genus joinedLocalDatum.sourceGraph = 0 := by
  decide +kernel

/-! ## Harmonic and divisor semantics of the local models -/

theorem splitLocalTarget_connected : graph_connected splitLocalTarget :=
  (graphConnectedCheck_eq_true_iff splitLocalTarget).mp (by decide +kernel)

theorem joinedLocalTarget_connected : graph_connected joinedLocalTarget :=
  (graphConnectedCheck_eq_true_iff joinedLocalTarget).mp (by decide +kernel)

/-- The split local quotient map is a checked degree-two unit-indexed
harmonic map. -/
theorem splitLocalHarmonic_check :
    splitLocalDatum.harmonicCertificate.check = true := by decide +kernel

theorem splitLocalHarmonic_unit :
    splitLocalDatum.harmonicCertificate.checkUnitIndexed = true := by decide +kernel

theorem splitLocalHarmonic_degree :
    splitLocalDatum.harmonicCertificate.checkDegree 2 = true := by decide +kernel

/-- The complete split local source carries the expected rank-one divisor of
degree two. -/
theorem splitLocal_bnExists : BNExists splitLocalDatum.sourceGraph 1 2 :=
  MarkedGraphs.IndexedHarmonicData.bnExists_rank_one_of_checked_harmonic_tree
    splitLocalDatum.harmonicCertificate 2 splitLocalHarmonic_check
    splitLocalHarmonic_unit splitLocalHarmonic_degree
    splitLocalTarget_connected splitLocalTarget_genus (show Fin 4 from 0)

/-- The joined local quotient is a valid indexed harmonic map of degree two. -/
theorem joinedLocalHarmonic_check :
    joinedLocalDatum.harmonicCertificate.check = true := by decide +kernel

theorem joinedLocalHarmonic_degree :
    joinedLocalDatum.harmonicCertificate.checkDegree 2 = true := by decide +kernel

/-- Its index-two new edge is genuinely nonunit.  Thus the ordinary finite
source Laplacian cannot soundly lower this candidate via the unit-indexed
theorem; the general Draisma--Vargas theorem needs the weighted/subdivision
adapter. -/
theorem joinedLocalHarmonic_not_unit :
    joinedLocalDatum.harmonicCertificate.checkUnitIndexed = false := by
  decide +kernel

/-- An integral metric realization of the nonunit candidate: the joined
target edge has length two, every other target edge has length one, and every
quotient-source edge has length one.  Thus the joined lift has dilation two
while all singleton lifts have dilation one. -/
def joinedLocalIntegralRealization : joinedLocalDatum.IntegralRealization where
  targetLength := fun edge ↦
    if (show Fin 4 × Fin 4 from edge.1) = (1, 2) then 2 else 1
  targetLength_pos := by
    intro edge
    split <;> omega
  sourceLength := fun _ ↦ 1
  sourceLength_pos := by
    intro edge
    omega
  dilation_length :=
    @of_decide_eq_true _ Fintype.decidableForallFintype (by decide +kernel)

/-- The concrete occurrence-labelled subdivision source of the nonunit
candidate is connected. -/
theorem joinedLocalRealizedSource_connected :
    graph_connected joinedLocalIntegralRealization.sourceSpec.graph :=
  joinedLocalIntegralRealization.sourceSpec_connected joinedLocalDatum_valid.1

/-- Exact target potentials for moving the root fibre at vertex `0` to each
vertex of the realized path with edge lengths `1, 2, 1`. -/
def joinedLocalTargetPotential : Fin 4 → Fin 4 → ℤ :=
  ![![0, 0, 0, 0],
    ![0, -1, -1, -1],
    ![0, -1, -3, -3],
    ![0, -1, -3, -4]]

def joinedLocalRoot : joinedLocalTarget.V :=
  show Fin 4 from 0

/-- The corresponding target-edge slopes, occurrence by occurrence. -/
def joinedLocalTargetSlope (anchor : Fin 4)
    (edge : joinedLocalTarget.edges) : ℤ :=
  if (show Fin 4 × Fin 4 from edge.1) = (0, 1) then
    if anchor = 0 then 0 else -1
  else if (show Fin 4 × Fin 4 from edge.1) = (1, 2) then
    if anchor = 2 ∨ anchor = 3 then -1 else 0
  else if (show Fin 4 × Fin 4 from edge.1) = (2, 3) then
    if anchor = 3 then -1 else 0
  else 0

theorem joinedLocalTargetPotential_rise :
    ∀ (anchor : Fin 4) (edge : joinedLocalTarget.edges),
      joinedLocalTargetPotential anchor
          edge.1.2 -
        joinedLocalTargetPotential anchor
          edge.1.1 =
      joinedLocalTargetSlope anchor edge *
        (joinedLocalIntegralRealization.targetLength edge : ℤ) := by
  decide +kernel

theorem joinedLocalTargetPotential_incidence :
    ∀ (anchor vertex : Fin 4),
      GluingDatum.targetEdgeIncidence (joinedLocalTargetSlope anchor) vertex =
        (if vertex = anchor then 1 else 0) -
          (if vertex = 0 then 1 else 0) := by
  intro anchor vertex
  fin_cases anchor <;> fin_cases vertex <;> decide +kernel

theorem joinedLocalRealizedFibre_degree :
    (∑ vertex : Fin (Fintype.card joinedLocalDatum.sourceGraph.V),
      joinedLocalIntegralRealization.fibreWeight joinedLocalRoot vertex) = 2 := by
  rw [joinedLocalIntegralRealization.sum_fibreWeight_eq_sum_sourceVertices]
  decide +kernel

/-- Direct finite-table check of the nonunit `M-11` subdivision pencil. -/
theorem joinedLocalRealized_bnExists_explicit :
    BNExists joinedLocalIntegralRealization.sourceSpec.graph 1 2 :=
  (joinedLocalIntegralRealization.bnExists_and_effective_of_targetPotentials
    joinedLocalDatum_valid.1 joinedLocalRoot 2 joinedLocalRealizedFibre_degree
    joinedLocalTargetPotential joinedLocalTargetSlope
    joinedLocalTargetPotential_rise joinedLocalTargetPotential_incidence).1

/-- The nonunit `M-11` candidate reaches subdivision-pencil semantics through
the uniform target-tree theorem: its occurrence-labelled integral source
subdivision carries an effective rank-one divisor of degree two. -/
theorem joinedLocalRealized_bnExists :
    BNExists joinedLocalIntegralRealization.sourceSpec.graph 1 2 :=
  (joinedLocalIntegralRealization.bnExists_and_effective_of_connected_genus_zero_target
    joinedLocalDatum_valid.1 joinedLocalTarget_connected
    joinedLocalTarget_genus joinedLocalRoot).1

/-- The validated mathematical harmonic data for the joined model. -/
def joinedLocalHarmonicData :
    MarkedGraphs.IndexedHarmonicData joinedLocalDatum.sourceGraph joinedLocalTarget :=
  joinedLocalDatum.harmonicCertificate.toData
    ((joinedLocalDatum.harmonicCertificate.check_eq_true_iff).mp
      joinedLocalHarmonic_check)

theorem joinedLocalHarmonicData_degree : joinedLocalHarmonicData.HasDegree 2 :=
  MarkedGraphs.IndexedHarmonicData.hasDegree_toData
    joinedLocalDatum.harmonicCertificate
    ((joinedLocalDatum.harmonicCertificate.check_eq_true_iff).mp
      joinedLocalHarmonic_check)
    ((joinedLocalDatum.harmonicCertificate.checkDegree_eq_true_iff 2).mp
      joinedLocalHarmonic_degree)

/-- Partition contraction and determinant balancing for the three candidates
of source case `w2-r2-nd3-M-11`.

The first two candidates use `splitResolution` (with the two possible remote
singleton pairings); the third uses `joinedResolution`. -/
theorem m11_local_resolution {c₁ c₂ c₃ s : ℚ}
    (hleft : c₁ + c₂ + s = 0) (hright : c₃ + s = 0) :
    (∀ candidate : Candidate,
      candidate.resolution.ContractsTo (SheetPartition.indiscrete 2)) ∧
      (SheetPartition.discrete 2).Refines splitResolution.right ∧
      (SheetPartition.discrete 2).Refines joinedResolution.left ∧
      (SheetPartition.discrete 2).Refines joinedResolution.right ∧
      SheetPartition.RiemannHurwitzAt splitResolution.left
        [splitResolution.newEdge] ∧
      SheetPartition.RiemannHurwitzAt splitResolution.right
        [splitResolution.newEdge, SheetPartition.discrete 2,
          SheetPartition.discrete 2] ∧
      SheetPartition.RiemannHurwitzAt joinedResolution.left
        [joinedResolution.newEdge, SheetPartition.discrete 2] ∧
      PositiveBalanceThree ![1, 1, 4]
        ![2 * c₁, 2 * c₂, c₃ / 2 + s] := by
  exact ⟨Candidate.resolution_contracts, splitResolution_external_refines_right,
    joinedResolution_external_refines_left,
    joinedResolution_external_refines_right,
    splitResolution_left_riemannHurwitz, splitResolution_right_riemannHurwitz,
    joinedResolution_endpoint_riemannHurwitz, balance_M_11 hleft hright⟩

/-- The M-11 receipt on a two-sheet block inside an arbitrary ambient sheet
set.  It records exactly the local data needed to assemble the outgoing
global gluing datums: common wall contraction, exterior refinement, all new
endpoint Riemann--Hurwitz inequalities on the selected block, the new-edge
indices, and Equation (6). -/
theorem m11_block_resolution
    {d : ℕ} (wall firstExternal secondExternal : SheetPartition d)
    (anchor : Fin d) (hCard : wall.blockCard anchor = 2)
    (hFirstRefines : firstExternal.Refines (wall.splitBlock anchor))
    (hSecondRefines : secondExternal.Refines (wall.splitBlock anchor))
    {c₁ c₂ c₃ s : ℚ}
    (hleft : c₁ + c₂ + s = 0) (hright : c₃ + s = 0) :
    (splitResolutionAt wall anchor).ContractsTo wall ∧
      (joinedResolutionAt wall).ContractsTo wall ∧
      firstExternal.Refines (splitResolutionAt wall anchor).right ∧
      secondExternal.Refines (splitResolutionAt wall anchor).right ∧
      firstExternal.Refines (joinedResolutionAt wall).left ∧
      secondExternal.Refines (joinedResolutionAt wall).right ∧
      LocalResolution.RiemannHurwitzAtBlock wall
        (splitResolutionAt wall anchor).left
        [(splitResolutionAt wall anchor).newEdge] anchor ∧
      LocalResolution.RiemannHurwitzAtBlock wall
        (splitResolutionAt wall anchor).right
        [(splitResolutionAt wall anchor).newEdge,
          firstExternal, secondExternal] anchor ∧
      LocalResolution.RiemannHurwitzAtBlock wall
        (joinedResolutionAt wall).left
        [(joinedResolutionAt wall).newEdge, firstExternal] anchor ∧
      LocalResolution.RiemannHurwitzAtBlock wall
        (joinedResolutionAt wall).right
        [(joinedResolutionAt wall).newEdge, secondExternal] anchor ∧
      (∀ sheet, wall.Rel anchor sheet →
        (splitResolutionAt wall anchor).newEdge.blockCard sheet = 1 ∧
          (joinedResolutionAt wall).newEdge.blockCard sheet = 2) ∧
      PositiveBalanceThree ![1, 1, 4]
        ![2 * c₁, 2 * c₂, c₃ / 2 + s] := by
  have hSplitToWall := wall.splitBlock_refines anchor
  have hFirstWall : firstExternal.Refines wall :=
    hFirstRefines.trans hSplitToWall
  have hSecondWall : secondExternal.Refines wall :=
    hSecondRefines.trans hSplitToWall
  have hFirstBlocks : ∀ sheet, wall.Rel anchor sheet →
      firstExternal.blockCountWithin wall sheet = 2 := by
    intro sheet hSheet
    rw [SheetPartition.blockCountWithin_eq_blockCard_of_refines_splitBlock
      firstExternal wall anchor sheet hFirstRefines hSheet]
    unfold SheetPartition.blockCard at hCard ⊢
    rw [← wall.block_eq_of_rel hSheet]
    exact hCard
  have hSecondBlocks : ∀ sheet, wall.Rel anchor sheet →
      secondExternal.blockCountWithin wall sheet = 2 := by
    intro sheet hSheet
    rw [SheetPartition.blockCountWithin_eq_blockCard_of_refines_splitBlock
      secondExternal wall anchor sheet hSecondRefines hSheet]
    unfold SheetPartition.blockCard at hCard ⊢
    rw [← wall.block_eq_of_rel hSheet]
    exact hCard
  refine ⟨splitResolutionAt_contracts wall anchor,
    joinedResolutionAt_contracts wall, hFirstRefines, hSecondRefines,
    hFirstWall, hSecondWall,
    splitResolutionAt_left_riemannHurwitzAtBlock wall anchor hCard,
    splitResolutionAt_right_riemannHurwitzAtBlock
      wall firstExternal secondExternal anchor,
    joinedResolutionAt_endpoint_riemannHurwitzAtBlock
      wall firstExternal anchor hFirstBlocks,
    joinedResolutionAt_endpoint_riemannHurwitzAtBlock
      wall secondExternal anchor hSecondBlocks, ?_, balance_M_11 hleft hright⟩
  intro sheet hSheet
  refine ⟨splitResolutionAt_newEdge_blockCard wall anchor sheet hSheet, ?_⟩
  rw [joinedResolutionAt_newEdge_blockCard]
  unfold SheetPartition.blockCard at hCard ⊢
  rw [← wall.block_eq_of_rel hSheet]
  exact hCard

end DraismaVargas.LocalCases.ResolutionM11
