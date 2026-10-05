module

public import GenusSixExistence.BrillNoetherRank.Tripod.Closure
public import GenusSixExistence.BrillNoetherRank.Tripod.RealisationProof

@[expose] public section

/-!
# Realisation of a closed claw member at an odd scale

Prose proof: `Research/genus-six-brill-noether-rank.md`, §7.3 (The witness divisor E + F),
§7.4 (Odd multiplicity gives an odd scale) and §7.5 (Rounding with E fixed); section and
statement numbers in this file refer to that note.

`witness_of_closed_oddClaw`: a closed claw member of odd multiplicity over the gadget, at the
actual request of a tripod model of `(G, E)`, gives an odd `N` and an effective divisor `F` of
degree two on the `N`-fold subdivision of `G` with `rank (embed E + F) ≥ 1`. That is the
conclusion of `BrillNoetherRank.OddCompletionWitness G 1 2` at `E`.

The proof has six links, the steps of §7.3–§7.5 (Theorem 7.5):

1. odd denominators: `OddDenominator.odd_adjusted_denominator` and
   `Integrality.fdSignedMult_eq_det_clearedMatrix` (degree-generic) at `(5, 14, 21)`;
2. the witness on the subdivision at the member's scale `k = memberScale mem = 2^a u`:
   Proposition 7.4, the repaired fibre over `φ(c)` retracted to `G` is `E + F_k`;
3. `rank ≥ 1` on that subdivision: the discrete form of Lemma 7.2 (an integral tree potential
   pulled back), the discrete form of Lemma 7.3 (retraction of grafted trees), and the
   rank-determining set of points of `G` over target vertices
   (`Spec.rankDeterminingSet_coreVertices`);
4. receipts for the G-part: `RowHairpinPosition.member_weighted_prefix_mem` at the internal root
   `φ(c)`, restricted to the G-slots through `ExpansionSeriesMoment` (over the chains of
   `spec₀`);
5. interior firing on `F` alone: `InteriorFiring.exists_onGrid`;
6. zero-budget rounding with the coarse part `embed E` fixed:
   `Spec.rank_ge_of_rank_scale_ge_nearest` with `D₀ = embed_u E` and two chips.

Then `TripodModel.transport` at scale `u` moves the result to `G`. The branch `u > 1` does not
occur in the computed examples (§7.6); the proof covers it with no extra argument.

`witness_of_closed_oddClaw` here is `RealisationProof.witness_of_closed_oddClaw`, which carries
out links (1)–(6): `sum_gFibre` (the `G′`-part of the fibre over `φ(c)` has degree two),
`exists_slidPencil` (the slid fibres), and the rank-determining set in two halves,
`rankDetermining_of_fib_loopDoubles` and `loopDouble_reach`.
-/

namespace GenusSixExistence.Tripod.Realisation

open DraismaVargas.Count
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Gadget Classification Closure

/-- **The realisation** (Proposition 7.4 and Theorem 7.5). A closed claw member of odd
multiplicity over the gadget, at the actual request of a tripod model of `(G, E)`, completes `E`
by two chips to a divisor of rank at least one on an odd regular subdivision of `G`. -/
theorem witness_of_closed_oddClaw {G : CFGraph.{0}}
    {E : CFDiv (UnitSubdivisionPresentation.spec G).graph} (M : TripodModel G E)
    (mem : FibreMember (tripodCore M.core M.slots) M.request (3 + 2))
    (hClosed : mem.Closed) (hOdd : mem.HasOddMult) (hClaw : MemberIsClaw mem) :
    ∃ (N : ℕ) (hN : 0 < N), Odd N ∧
      ∃ F : CFDiv ((UnitSubdivisionPresentation.spec G).scale N hN).graph,
        effective F ∧ deg F = 2 ∧
          rank ((UnitSubdivisionPresentation.spec G).scale N hN).graph
            ((UnitSubdivisionPresentation.spec G).embed N hN E + F) ≥ 1 :=
  RealisationProof.witness_of_closed_oddClaw M mem hClosed hOdd hClaw

end GenusSixExistence.Tripod.Realisation
