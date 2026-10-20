module

public import DiagonalSecant.Defs
public import GenusSixExistence.BrillNoetherRank.Tripod.TripodModelProof

@[expose] public section

/-!
# Every bridgeless graph with a vertex has a once-marked model

This is the tripod model of `Research/genus-six-brill-noether-rank.md` §6.2, with one mark and
no legs.

The construction is the public `TripodModelProof.tripodModel_of_reduced` with one mark:

1. the reduced model at genus `g`, `TripodModelProof.exists_reducedModel_of_two_le`;
2. one mark placement: `MarkRefinement.exists_markStep` (generic in `n p N Q`) at the vertex
   `φ⁻¹(u)` of the reduced graph, which subdivides one big slot `e` and returns the expansion of
   `subdivide D₀.bigCore e` onto the refined small specification, with the new vertex over a
   small core vertex `w'` that the Laplacian equivalence sends to `u`;
3. the transport at every scale: `Utilities.Subdivision.ScaleLift.exists_scaledEquiv` and
   `mapDiv_embed`, as in the tripod.

What the tripod did not need and this model records: `smallConnected`
(from the Laplacian equivalence with the connected `G`, or from `small.core.Connected` of the
reduced model carried through the split of a slot), and `genus_eq` (from `N = 2(g − 1)` and
`Q = 3(g − 1)`).
-/

namespace DiagonalSecant

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph

open Utilities.Certificate.ExplicitPotential (Core)
open Utilities.Subdivision.CoreExpansion (ExpansionData)
open Utilities.Subdivision.ScaleLift
open GenusSixExistence.Tripod.MarkRefinement
open GenusSixExistence.Tripod.TripodModelProof (exists_reducedModel_of_two_le incident_of_cubic)

/-- **Once-marked models exist** in genus at least two, for every connected bridgeless graph and
every vertex of its unit presentation: the reduced model, one `exists_markStep` at the pull-back
of `u`, and the scale lift of the composite equivalence. This is the form the assembly uses. -/
theorem exists_onceMarkedModel_of_two_le (G : CFGraph.{0}) (hG : graph_connected G) {g : ℕ}
    (hg : genus G = g) (hg2 : 2 ≤ g)
    (hb : (UnitSubdivisionPresentation.spec G).core.Bridgeless)
    (u : (UnitSubdivisionPresentation.spec G).graph.V) :
    Nonempty (OnceMarkedModel g G u) := by
  obtain ⟨n₀, p₀, N, Q, spec₀, D₀, hN, hQ, hCond, hCubic, hConnBig, ⟨φ⟩⟩ :=
    exists_reducedModel_of_two_le G hG hg hg2 hb
  obtain ⟨n₁, p₁, s₁, D₁, e₁, -, w₁, χ₁, hC₁, hB₁, -, hf₁, -, hχ₁, -⟩ :=
    exists_markStep spec₀ D₀ hCond (incident_of_cubic hCubic) (φ.toEquiv.symm u)
  have hGc : graph_connected (UnitSubdivisionPresentation.spec G).graph :=
    (UnitSubdivisionPresentation.laplacianEquiv G).graphConnected hG
  have hΦ : (χ₁.trans φ) (s₁.coreVertex w₁) = u := by
    show φ (χ₁ (s₁.coreVertex w₁)) = u
    rw [hχ₁]
    exact φ.toEquiv.apply_symm_apply _
  refine ⟨{
    N := N
    Q := Q
    core := D₀.bigCore
    cubic := hCubic
    connected := hConnBig
    loopless := ExpansionData.loopless_of_conditions hCond
    genus_eq := by omega
    slot := e₁
    smallVertices := n₁
    smallSlots := p₁
    small := s₁
    smallConnected := Utilities.Certificate.PseudocorePresentation.core_connected_of_graph_connected
      s₁ ((χ₁.trans φ).symm.graphConnected hGc)
    smallMark := w₁
    expansion := D₁
    bigCore_eq := hB₁
    conditions := hC₁
    fib_mark := hf₁
    transport := ?_ }⟩
  intro k hk
  obtain ⟨ψ, hψ⟩ := exists_scaledEquiv (χ₁.trans φ) k hk
  refine ⟨ψ, ?_⟩
  rw [mapDiv_embed (χ₁.trans φ) k hk ψ hψ, LaplacianEquiv.mapDiv_one_chip, hΦ]

end DiagonalSecant
