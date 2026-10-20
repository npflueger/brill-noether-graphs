module

public import DiagonalSecant.Parity
public import DiagonalSecant.ClosureH
public import DiagonalSecant.Restrict
public import DiagonalSecant.Model
public import DiagonalSecant.TypedRealisation
public import DiagonalSecant.BridgeLift
public import DiagonalSecant.Descent

@[expose] public section

/-!
# The diagonal secant theorem

> **Theorem A.** Let `G` be a connected finite loopless multigraph of genus `g ≥ 5` with
> `g ≡ 1` or `2 (mod 4)`, and `u` a vertex. Then there is an effective divisor `F` of degree two
> on `V(G)` with `r_G((g − 3)u + F) ≥ 1`. Corollary: `BNExists G 1 (g − 1)`.

`CFGraph` is a finite loopless multigraph (`CFGraph.loopless`; parallel edges are a multiset),
and `genus G = |E| − |V| + 1 : ℤ`, so the hypotheses are exactly those of the statement above.

## The idea

On a general curve of genus `g` with a general point `u`, the pencils of degree `g − 1` with a
`(g − 3)`-fold point at `u` are counted by the once-marked Draisma--Vargas count of type
`g − 4` (`DraismaVargas.Count.MarkedCountGeneral.typedCount_onceMarked`), which is
`N(g; g − 4, 0) = C(g, 2) − g = g(g − 3)/2` (`Parity.lean`): odd exactly when `g ≡ 1, 2 (mod 4)`.
The proof reads this tropically. The count is run on a cubic model of `G` with a mark at `u`;
its oddness leaves a member of odd multiplicity that survives as the edge lengths degenerate to
those of `G`; that member is realised as a divisor of rank at least one on an odd subdivision of
`G`, with `g − 3` chips at `u` and two further chips; and since the scale is odd, the two chips
round to vertices of `G` without loss of rank.

## The assembly (`diagonalOddWitness_of_bridgeless_core`)

For a connected bridgeless `G'` of genus `g` and a vertex `ū` of its unit presentation:

1. a once-marked model `M` of `(G', ū)` (`Model.exists_onceMarkedModel_of_two_le`);
2. the count is odd (`Parity.odd_markedFormula_diagonal`), so the closure on the tailed core
   gives a closed full-type member of odd multiplicity at `M.request`
   (`ClosureH.exists_closed_oddFullType_of_nonneg`, with `a = g − 4`, `d = g − 1`);
3. it restricts to a closed typed member of type `g − 4` of odd typed multiplicity
   (`Restrict.exists_typed_of_fullType`);
4. the realisation gives the completion of `(g − 3)ū` on an odd subdivision of `M.small`
   (`TypedRealisation.witness_of_closed_typed`);
5. `M.transport` moves it to the unit presentation of `G'`: that is `DiagonalOddWitness G' (g − 3) ū`.

Then `BridgeLift.diagonalOddWitness_of_bridgeless` removes the bridgeless hypothesis,
`Descent.exists_completion_on_graph` brings the completion to `G` itself, and
`bnExists_one_genus_sub_one` reads off the pencil.
-/

namespace DiagonalSecant

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open DraismaVargas.Count.SegmentWalls (Frame)

/-- `embed` commutes with `nsmul` (it is additive: `Spec.embed_add`, `Spec.embed_zero`). Stated
for an abstract specification, so no concrete vertex type is unfolded. -/
theorem embed_nsmul {n p : ℕ} (S : Spec n p) (k : ℕ) (hk : 0 < k) (m : ℕ) (D : CFDiv S.graph) :
    S.embed k hk (m • D) = m • S.embed k hk D := by
  induction m with
  | zero => simp only [zero_smul]; exact S.embed_zero k hk
  | succ m ih => rw [succ_nsmul, succ_nsmul, S.embed_add, ih]

/-- **Step 5 of the assembly**: a completion of the mark chips on an odd subdivision of the small
specification of a once-marked model is a diagonal witness on `G`, by the model's transport. -/
theorem diagonalOddWitness_of_model {g : ℕ} {G : CFGraph.{0}}
    {u : (UnitSubdivisionPresentation.spec G).graph.V} (M : OnceMarkedModel g G u) (m : ℕ)
    (h : ∃ (N : ℕ) (hN : 0 < N), Odd N ∧
      ∃ F : CFDiv (M.small.scale N hN).graph, effective F ∧ deg F = 2 ∧
        rank (M.small.scale N hN).graph (M.small.embed N hN (M.markChips m) + F) ≥ 1) :
    DiagonalOddWitness G m u := by
  obtain ⟨N, hN, hodd, F, hF, hFdeg, hrank⟩ := h
  obtain ⟨eqv, heqv⟩ := M.transport N hN
  refine ⟨N, hN, hodd, eqv.mapDiv F, (eqv.effective_mapDiv_iff F).mpr hF,
    by rw [eqv.deg_mapDiv]; exact hFdeg, ?_⟩
  have hmap : eqv.mapDiv (M.small.embed N hN (M.markChips m) + F) =
      (UnitSubdivisionPresentation.spec G).embed N hN (m • one_chip u) + eqv.mapDiv F := by
    rw [eqv.mapDiv_add, OnceMarkedModel.markChips, embed_nsmul, embed_nsmul, ← heqv]
    rfl
  rw [← hmap, eqv.rank_mapDiv_ge_iff]
  exact hrank

/-- **The witness for bridgeless graphs**: the assembly of the five steps. -/
theorem diagonalOddWitness_of_bridgeless_core (G : CFGraph.{0}) (hG : graph_connected G)
    {g : ℕ} (hg : genus G = g) (hg5 : 5 ≤ g) (hmod : g % 4 = 1 ∨ g % 4 = 2)
    (hb : (UnitSubdivisionPresentation.spec G).core.Bridgeless)
    (u : (UnitSubdivisionPresentation.spec G).graph.V) :
    DiagonalOddWitness G (g - 3) u := by
  -- 1. the once-marked model
  obtain ⟨M⟩ := exists_onceMarkedModel_of_two_le G hG hg (by omega) hb u
  -- 2. the closure on the tailed core, at the actual request, type `g − 4`, degree `g − 1`
  have hdeg := diagonal_degree (g := g) (by omega)
  obtain ⟨mem, hClosed, hOdd, hFull⟩ :=
    exists_closed_oddFullType_of_nonneg M.cubic M.connected M.genus_eq hg5 M.slot
      (a := g - 4) (d := g - 1) (by omega) hdeg.1 hdeg.2
      (odd_markedFormula_diagonal (by omega) hmod) M.request M.request_nonneg
  -- 3. the restriction to a closed typed member of type `g − 4`
  obtain ⟨κ, hκClosed, hκOdd⟩ := exists_typed_of_fullType M.cubic M.slot (by omega) mem
    hClosed hOdd hFull
  -- 4. the realisation on an odd subdivision of the small specification, 5. the transport
  exact diagonalOddWitness_of_model M (g - 3) (witness_of_closed_typed M hg5 κ hκClosed hκOdd)

/-- **The diagonal witness on every connected graph** of genus `g ≥ 5`, `g ≡ 1, 2 (mod 4)`. -/
theorem diagonalOddWitness (G : CFGraph.{0}) (hG : graph_connected G) {g : ℕ}
    (hg : genus G = g) (hg5 : 5 ≤ g) (hmod : g % 4 = 1 ∨ g % 4 = 2)
    (u : (UnitSubdivisionPresentation.spec G).graph.V) :
    DiagonalOddWitness G (g - 3) u :=
  diagonalOddWitness_of_bridgeless
    (fun H v hH hgH hbH ↦ diagonalOddWitness_of_bridgeless_core H hH hgH hg5 hmod hbH v)
    G u hG hg

/-- **Theorem A, the diagonal secant theorem.** On every connected graph `G` of genus `g ≥ 5`
with `g ≡ 1` or `2 (mod 4)` and every vertex `u`, some effective divisor `F` of degree two has
`rank ((g − 3) • u + F) ≥ 1`. -/
theorem diagonalSecant (G : CFGraph.{0}) (hG : graph_connected G) (hg5 : 5 ≤ genus G)
    (hmod : genus G % 4 = 1 ∨ genus G % 4 = 2) (u : G.V) :
    ∃ F : CFDiv G, effective F ∧ deg F = 2 ∧ rank G ((genus G - 3) • one_chip u + F) ≥ 1 := by
  set g : ℕ := (genus G).toNat with hgdef
  have hg : genus G = g := by rw [hgdef, Int.toNat_of_nonneg (by omega)]
  have hg5' : 5 ≤ g := by omega
  have hmod' : g % 4 = 1 ∨ g % 4 = 2 := by omega
  have hsmul : (genus G - 3) • one_chip u = (g - 3) • one_chip u := by
    rw [← natCast_zsmul]
    congr 1
    omega
  rw [hsmul]
  exact exists_completion_on_graph u (diagonalOddWitness G hG hg hg5' hmod' _)

/-- **The pencil of degree `g − 1`**: `BNExists G 1 (g − 1)` on every connected graph of genus
`g ≥ 5` with `g ≡ 1` or `2 (mod 4)`. This is Brill--Noether existence in the special range
`ρ(g, 1, g − 1) = g − 4 < d − r`. For `g = 5` and `6` it is also a case of
`GenusSixExistence.brillNoetherExistenceThroughSix`; the next genera are `9` and `10`. -/
theorem bnExists_one_genus_sub_one (G : CFGraph.{0}) (hG : graph_connected G)
    (hg5 : 5 ≤ genus G) (hmod : genus G % 4 = 1 ∨ genus G % 4 = 2) :
    BNExists G 1 (genus G - 1) := by
  obtain ⟨F, -, hdeg, hrank⟩ := diagonalSecant G hG hg5 hmod (Classical.arbitrary G.V)
  refine ⟨(genus G - 3) • one_chip (Classical.arbitrary G.V) + F, ?_, hrank⟩
  rw [deg.map_add, deg.map_zsmul, deg_one_chip, hdeg]
  ring

end DiagonalSecant
