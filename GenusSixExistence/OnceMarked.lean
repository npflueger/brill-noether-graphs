module

public import Utilities.Gluing.VertexWedgeGenusOneCollapse
public import GenusSixExistence.Existence
public import GenusSixExistence.OnceMarked.OnceMarkedGenusFive
public import Utilities.Gluing.CycleRigidity

@[expose] public section

/-!
# Once-marked Brill--Noether existence through genus five, from genus six

For a connected genus-five graph `G`, once-marked Brill--Noether existence at a mark `u` is
equivalent to one diagonal problem: a degree-four divisor of rank at least one containing `2u`
(`MarkedGraphs.onceMarkedBNExistence_iff_markedRankOneCompletion_genus_five`). This is the Young
diagram `(3,2)`, the one case that the partition catalogue does not supply.

It follows from genus six. Attach a cycle at `u`. The wedge is connected of genus six, so
`GenusSixExistence.bnExists` gives it a degree-four pencil, and
`Utilities.bnExists_vertexWedge_one_iff` collapses the cycle to a degree-four pencil on `G`
containing `2u`. This is the tropical elliptic-tail argument. The cycle is the two-edge digon
`TwoPathCycle.spec (fun _ => 1)`, which is pointed rigid of genus one at either vertex
(`TwoPathCycle.pointedGenusOneRigid`).

Headlines:

* `markedRankOneCompletion_diagonal_genus_five`: the `(3,2)` case, at every mark of every
  connected genus-five graph;
* `onceMarkedBNExistence_genus_five`: the full once-marked statement in genus five;
* `onceMarkedBNExistenceThroughFive`: through genus five, with genus at most four from the
  partition catalogue and Atanasov--Ranganathan existence (`BNExists G 1 3` in genus four).
-/

namespace GenusSixExistence

open Utilities MarkedGraphs

universe u

/-- The attached cycle: two parallel unit edges. -/
abbrev digonSpec : Certificate.SubdivisionGraph.Spec 2 2 :=
  TwoPathCycle.spec (fun _ => 1) (fun _ => Nat.one_pos)

/-- The marked vertex of the attached cycle. -/
abbrev digonMark : digonSpec.graph.V := digonSpec.coreVertex (0 : Fin 2)

/-- Attaching a cycle at `x` to a connected genus-five graph gives a connected
genus-six graph. -/
theorem wedgeDigon_connected_genus_six (G : CFGraph.{u}) (hG : graph_connected G)
    (hGenus : genus G = 5) (x : G.V) :
    graph_connected (vertexWedge G digonSpec.graph x digonMark) ∧
      genus (vertexWedge G digonSpec.graph x digonMark) = 6 := by
  refine ⟨graph_connected_vertexWedge G _ x _ hG (TwoPathCycle.connected _ _), ?_⟩
  rw [genus_vertexWedge, hGenus, TwoPathCycle.genus_one]
  norm_num

/-- **The `(3,2)` case in genus five.** Every mark `x` of a connected genus-five
graph lies twice on a degree-four rank-one divisor. -/
theorem markedRankOneCompletion_diagonal_genus_five (G : CFGraph.{u})
    (hG : graph_connected G) (hGenus : genus G = 5) (x : G.V) :
    MarkedRankOneCompletion G x x := by
  obtain ⟨hW, hWGenus⟩ := wedgeDigon_connected_genus_six G hG hGenus x
  have hPencil : BNExists (vertexWedge G digonSpec.graph x digonMark) 1 4 :=
    GenusSixExistence.bnExists _ hW hWGenus (r := 1) (d := 4)
      (by norm_num) (by simp [bnNumber, rectangleWidth, hWGenus])
  obtain ⟨D, hDeg, hRank, hTwo⟩ :=
    (bnExists_vertexWedge_one_iff G digonSpec.graph x digonMark
      (TwoPathCycle.pointedGenusOneRigid _ _ digonMark) 4).mp hPencil
  obtain ⟨E, hEEffective, hEquiv⟩ := hTwo
  refine ⟨E, hEEffective, ?_, ?_⟩
  · rw [← linear_equiv_preserves_deg G _ E hEquiv, deg.map_sub, map_zsmul, deg_one_chip,
      hDeg]
    norm_num
  · have hEquiv' : linear_equiv G D (one_chip x + one_chip x + E) := by
      unfold linear_equiv at hEquiv ⊢
      convert hEquiv using 1
      rw [two_smul]
      abel
    rw [← rank_eq_of_linear_equiv G hEquiv']
    exact hRank

/-- **Once-marked Brill--Noether existence in genus five**, at every mark of
every connected genus-five graph. -/
theorem onceMarkedBNExistence_genus_five (G : CFGraph.{u}) (hG : graph_connected G)
    (hGenus : genus G = 5) (x : G.V) : OnceMarkedBNExistence G x :=
  (onceMarkedBNExistence_iff_markedRankOneCompletion_genus_five G hG hGenus x).mpr
    (markedRankOneCompletion_diagonal_genus_five G hG hGenus x)

/-- **Once-marked Brill--Noether existence through genus five.** Every Young
diagram of size at most the genus occurs in the divisor census of every mark of
every connected graph of genus at most five. -/
theorem onceMarkedBNExistenceThroughFive :
    ∀ (G : CFGraph.{0}), graph_connected G → genus G ≤ 5 →
      ∀ x : G.V, OnceMarkedBNExistence G x := by
  intro G hG hGenus x
  rcases lt_or_ge (genus G) 5 with hLow | hFive
  · apply onceMarkedBNExistence_of_genus_le_four_of_critical G hG x (by omega)
    intro hFour
    obtain ⟨D, hRank, hDeg⟩ :=
      AtanasovRanganathan.brillNoetherExistenceThroughFive G hG hGenus 1 3
        (by rw [hFour]; norm_num)
    exact ⟨D, hDeg, hRank⟩
  · exact onceMarkedBNExistence_genus_five G hG (by omega) x

end GenusSixExistence
