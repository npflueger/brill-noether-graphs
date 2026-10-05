module

public import DraismaVargas.LocalCases.SemanticAtlasMarch
public import DraismaVargas.LocalCases.InteriorGraphTracking
public import DraismaVargas.LocalCases.TrivalenceClosure
public import DraismaVargas.LocalCases.StableSourceWhiteheadChain
public import DraismaVargas.LocalCases.CaterpillarGenericSeed

@[expose] public section

/-!
# The march payload with its row-labelled graph attached

Source: the atlas march of `SemanticAtlasMarch` (Draisma--Vargas Part I), read
against Vargas, Part II, Section 4.4, where crossings inside one trivalent cone
preserve the row-labelled source graph.

`SemanticAtlasMarch.CarriesClearedPencil` retains an actual candidate, its
full-dimensional presentation and its cleared pencil, but all of them under one
existential binder with no graph in it.  The header of `InteriorGraphTracking`
records why that is a loss: a separate existential graph witness at the same
matrix is not a repair,
because a matrix does not determine its candidate.  `TrackedPencil` is
`CarriesClearedPencil` with two further conjuncts **under the same binder**:

* `Nonempty (InteriorGraphTracking.Tracks fullDim graph label)`, the actual
  dart isomorphism from that very cover's constructed stable graph to the
  ambient `graph`, together with its exact row-label formula; and
* `genus candidate.datum.sourceGraph = (graph.genus : ℤ)`, source-graph genus
  invariance, recorded against the ambient graph's own genus.

The second conjunct needs no extra producer work and no further field:
`TrackedPencil.of_tracks` derives it from the first one.  A
full-dimensional presentation satisfies
`TrivalenceClosure.genus_sourceGraph_eq_of_presentation`, which with
`TrivalenceClosure.one_le_stableComponentCount_of_presentation` forces
`2 * degree - 2 ≤ genus data.sourceGraph`, hence positivity as soon as
`2 ≤ degree`; and `StableSourceDarts.genus_ofDatum` then identifies the source
genus with the genus of the constructed dart graph, which `Tracks.iso` carries
to `graph`.  Since `graph` is a *parameter* of the tracked march state, genus
invariance along the march is a consequence of the state's shape rather than a
separate carried equation.

What is proved here: the definition, its projection to `CarriesClearedPencil`
(so everything stated for `CarriesClearedPencil` still applies), the constructor
from a tracking witness, the seed instance -- `SeedCandidate.Seed` and the
literal caterpillar seed of `CaterpillarGenericSeed`, at `Tracks.self` on the
seed's own `ofDatum` graph and literal row labels -- and the interface the
finite Whitehead-chain consumer takes, namely
`StableSourceWhiteheadChain.exists_chain_of_fullDimensional` applied to the
retained presentation, with the chain's initial graph carried to the ambient
`graph` and the terminal core-slot dictionary read in the state's own labels.

What is NOT proved here: nothing about which wall a march crosses, no outer
walk, and no realization of the intermediate graphs of the chain by gluing
covers.  `2 ≤ degree` remains an explicit hypothesis of `of_tracks` and of
everything built from it; `graph.genus = p + 1 - n` and `2 ≤ p + 1 - n` remain
explicit hypotheses of the chain interface, as they are of
`exists_chain_of_fullDimensional`.

Used by: `TrackedState`, which uses `TrackedPencil` as the payload field of the
tracked march state.
-/

namespace DraismaVargas.LocalCases

open Utilities
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StableSourceDarts
open DraismaVargas.LocalCases.InteriorGraphTracking

variable {coordinate D V : Type*} [Fintype coordinate] [DecidableEq coordinate]
  [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- **The march payload with its graph.**  Exactly the five conjuncts of
`SemanticAtlasMarch.CarriesClearedPencil` -- the retained candidate displays
the chart matrix, the incoming datum is valid, its target is connected and a
tree, and the coordinate vector is cleared -- together with an actual tracking
of the ambient row-labelled `graph` by that same full-dimensional presentation,
and the source genus of that same candidate's cover.

All seven conjuncts sit under ONE existential binder.  That is the whole point:
`CarriesClearedPencil` plus a separately quantified graph witness at the same
matrix would not say that the graph presents the retained candidate. -/
def TrackedPencil (degree : ℕ) (graph : CubicDartGraph D V) (label : D → coordinate)
    (matrix : Matrix coordinate coordinate ℚ) (coordinates : coordinate → ℚ) : Prop :=
  ∃ (target : CFGraph.{0}) (data : GluingDatum target degree) (wall : target.V),
    ∃ candidate : Candidate target degree data wall,
      ∃ fullDim : FullDimensionalSourcePresentation candidate.datum coordinate,
        GluingDatum.LengthMatrixPresentation.matrix
            fullDim.labelling.presentation = matrix ∧
        data.Valid ∧
        graph_connected target ∧
        genus target = 0 ∧
        Nonempty (Candidate.ClearedPencil candidate
          fullDim.labelling.presentation coordinates) ∧
        Nonempty (Tracks fullDim graph label) ∧
        genus candidate.datum.sourceGraph = (graph.genus : ℤ)

namespace TrackedPencil

variable {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}

/-- **Forgetting the graph.**  Forgetting the tracking and the genus gives
`CarriesClearedPencil`, so everything stated for it -- the terminal face,
`exists_bnExists`, the whole finite march -- applies verbatim to a tracked
payload. -/
theorem toCarriesClearedPencil {matrix : Matrix coordinate coordinate ℚ}
    {coordinates : coordinate → ℚ}
    (receipt : TrackedPencil degree graph label matrix coordinates) :
    SemanticAtlasMarch.CarriesClearedPencil degree matrix coordinates := by
  obtain ⟨target, data, wall, candidate, fullDim, hmatrix, hvalid, hconnected,
    hgenus, hpencil, -, -⟩ := receipt
  exact ⟨target, data, wall, candidate, fullDim, hmatrix, hvalid, hconnected,
    hgenus, hpencil⟩

/-- A tracked payload still exhibits the required rank-one pencil. -/
theorem exists_bnExists {matrix : Matrix coordinate coordinate ℚ}
    {coordinates : coordinate → ℚ}
    (receipt : TrackedPencil degree graph label matrix coordinates) :
    ∃ source : CFGraph.{0}, BNExists source 1 degree :=
  receipt.toCarriesClearedPencil.exists_bnExists

/-- **Source-graph genus is read off the ambient tracked graph.**  A
full-dimensional presentation forces `genus data.sourceGraph = 2 degree - 5 + 3
c(H)` with `1 ≤ c(H)`, hence positivity once `2 ≤ degree`; positivity is what
`StableSourceDarts.genus_ofDatum` needs to identify the source genus with the
genus of the constructed dart graph, and the tracking isomorphism carries that
to the ambient graph.

This is why no producer needs a genus clause, in particular not
`W3ShiftGraphTracking.TrackedCertifiedExit`: every producer hands over a
full-dimensional presentation and a tracking at it. -/
theorem genus_sourceGraph_eq_of_tracks {target : CFGraph} {degree : ℕ}
    {data : GluingDatum target degree} (hDegree : 2 ≤ degree)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    {graph : CubicDartGraph D V} {label : D → coordinate}
    (tracking : Tracks fullDim graph label) :
    genus data.sourceGraph = (graph.genus : ℤ) := by
  have hCount := TrivalenceClosure.one_le_stableComponentCount_of_presentation fullDim
  have hSum := TrivalenceClosure.genus_sourceGraph_eq_of_presentation fullDim
  have hDeg : (2 : ℤ) ≤ (degree : ℤ) := by exact_mod_cast hDegree
  have hPos : 0 < genus data.sourceGraph := by omega
  have hOf := StableSourceDarts.genus_ofDatum data fullDim.connected fullDim.trivalent
    fullDim.pathEnds hPos
  rw [← hOf, tracking.iso.genus_eq]

/-- **The constructor.**  The five conjuncts of `CarriesClearedPencil` and one
tracking witness give
a tracked payload; the genus conjunct is derived, not demanded. -/
theorem of_tracks {matrix : Matrix coordinate coordinate ℚ}
    {coordinates : coordinate → ℚ} (hDegree : 2 ≤ degree)
    (target : CFGraph.{0}) (data : GluingDatum target degree) (wall : target.V)
    (candidate : Candidate target degree data wall)
    (fullDim : FullDimensionalSourcePresentation candidate.datum coordinate)
    (hmatrix : GluingDatum.LengthMatrixPresentation.matrix
      fullDim.labelling.presentation = matrix)
    (hvalid : data.Valid) (hconnected : graph_connected target)
    (hgenus : genus target = 0)
    (pencil : Candidate.ClearedPencil candidate
      fullDim.labelling.presentation coordinates)
    (tracking : Tracks fullDim graph label) :
    TrackedPencil degree graph label matrix coordinates :=
  ⟨target, data, wall, candidate, fullDim, hmatrix, hvalid, hconnected, hgenus,
    ⟨pencil⟩, ⟨tracking⟩, genus_sourceGraph_eq_of_tracks hDegree fullDim tracking⟩

/-! ## Non-vacuity: the seed -/

/-- The graph a seed tracks: the seed cover's own constructed stable graph. -/
noncomputable def seedGraph (seed : SeedCandidate.Seed degree)
    (fullDim : FullDimensionalSourcePresentation seed.candidate.datum coordinate) :
    CubicDartGraph (Dart seed.candidate.datum) (BranchVertex seed.candidate.datum) :=
  ofDatum seed.candidate.datum fullDim.connected fullDim.trivalent fullDim.pathEnds

/-- The labels a seed tracks: the literal stable rows of its own cover. -/
noncomputable def seedLabel (seed : SeedCandidate.Seed degree)
    (fullDim : FullDimensionalSourcePresentation seed.candidate.datum coordinate) :
    Dart seed.candidate.datum → coordinate :=
  fun d ↦ fullDim.labelling.row (row seed.candidate.datum d)

/-- **The seed inhabits the tracked payload.**  No graph receipt is taken: the
seed tracks its own `ofDatum` graph through `Tracks.self`, and the genus
conjunct is derived. -/
theorem ofSeed (hDegree : 2 ≤ degree) (seed : SeedCandidate.Seed degree)
    (fullDim : FullDimensionalSourcePresentation seed.candidate.datum coordinate)
    (coordinates : coordinate → ℚ) (hPositive : ∀ i, 0 < coordinates i) :
    TrackedPencil degree (seedGraph seed fullDim) (seedLabel seed fullDim)
      (GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation)
      coordinates :=
  of_tracks hDegree seed.target seed.data seed.wall seed.candidate fullDim rfl
    seed.valid seed.targetConnected seed.targetGenus
    (seed.clearedPencil fullDim.labelling.presentation coordinates hPositive)
    (Tracks.self fullDim)

/-- The literal caterpillar seed of `CaterpillarGenericSeed`, tracked.  Its
chart matrix is the one `CaterpillarGenericSeed.matrix` registers, so this is
the seed payload of the first march with the graph attached. -/
theorem caterpillar (m : ℕ) (coordinates : Fin (6 * m + 3) → ℚ)
    (hPositive : ∀ i, 0 < coordinates i) :
    TrackedPencil (m + 2)
      (seedGraph (CaterpillarSeed.seed m)
        (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)))
      (seedLabel (CaterpillarSeed.seed m)
        (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)))
      (CaterpillarGenericSeed.matrix m) coordinates := by
  have h := ofSeed (by omega) (CaterpillarSeed.seed m)
    (CaterpillarSeed.seedFullDim m (CaterpillarRows.fullDim m)) coordinates hPositive
  rwa [CaterpillarSeed.seedFullDim_matrix m (CaterpillarRows.fullDim m)] at h

/-! ## What the finite Whitehead-chain consumer needs

`StableSourceWhiteheadChain.exists_chain_of_fullDimensional` takes a datum, a
requested ordered cubic `Core n p`, a full-dimensional presentation of the
datum, `2 ≤ p + 1 - n`, and `genus data.sourceGraph = ((p + 1 - n : ℕ) : ℤ)`.
The two theorems below say that a tracked payload supplies all of the
source-side inputs, and that the resulting chain's initial graph is the ambient
`graph` of the state up to the tracked isomorphism, with the terminal core-slot
dictionary readable directly in the state's own labels.

Neither theorem builds the outer walk: the chain is the one the graph-level
theorem produces, and no intermediate graph of it is asserted to be realized
by a gluing cover. -/

/-- **The source-side inputs of the chain, in the shape the chain takes.**  The
retained presentation carries `connected`, `trivalent` and `pathEnds`; the
tracking carries the isomorphism to the ambient graph and the exact row map;
and the genus conjunct, read against the ambient graph's genus, is exactly the
`hSameGenus` hypothesis once the ambient genus is the requested one. -/
theorem exists_presentation_of_genus {n p : ℕ}
    {matrix : Matrix coordinate coordinate ℚ} {coordinates : coordinate → ℚ}
    (receipt : TrackedPencil degree graph label matrix coordinates)
    (hGraphGenus : graph.genus = p + 1 - n) :
    ∃ (target : CFGraph.{0}) (data : GluingDatum target degree) (wall : target.V),
      ∃ candidate : Candidate target degree data wall,
        ∃ fullDim : FullDimensionalSourcePresentation candidate.datum coordinate,
          GluingDatum.LengthMatrixPresentation.matrix
              fullDim.labelling.presentation = matrix ∧
          Nonempty (Candidate.ClearedPencil candidate
            fullDim.labelling.presentation coordinates) ∧
          Nonempty (Tracks fullDim graph label) ∧
          genus candidate.datum.sourceGraph = ((p + 1 - n : ℕ) : ℤ) := by
  obtain ⟨target, data, wall, candidate, fullDim, hmatrix, -, -, -, hpencil,
    htracks, hgenus⟩ := receipt
  exact ⟨target, data, wall, candidate, fullDim, hmatrix, hpencil, htracks,
    by rw [hgenus, hGraphGenus]⟩

/-- **The finite Whitehead chain of a tracked payload.**  The chain starts at
the retained cover's own constructed stable graph, which the tracking carries
isomorphically onto the ambient `graph`; its terminal graph is isomorphic to
the requested core; and the terminal core-slot dictionary is a single
`coordinate ≃ Fin p` that reads the ambient graph's own labels.

The outer walk is not built here, and no intermediate graph of the chain is
claimed to be realized by a gluing cover. -/
theorem exists_chain_to_core {n p : ℕ}
    (core : Utilities.Certificate.ExplicitPotential.Core n p)
    (hCubic : core.Cubic) (hCoreConnected : core.Connected)
    {matrix : Matrix coordinate coordinate ℚ} {coordinates : coordinate → ℚ}
    (receipt : TrackedPencil degree graph label matrix coordinates)
    (hChainGenus : 2 ≤ p + 1 - n) (hGraphGenus : graph.genus = p + 1 - n) :
    ∃ (target : CFGraph.{0}) (data : GluingDatum target degree) (wall : target.V),
      ∃ candidate : Candidate target degree data wall,
        ∃ fullDim : FullDimensionalSourcePresentation candidate.datum coordinate,
          GluingDatum.LengthMatrixPresentation.matrix
              fullDim.labelling.presentation = matrix ∧
          Nonempty (Candidate.ClearedPencil candidate
            fullDim.labelling.presentation coordinates) ∧
          ∃ source : CubicDartGraph (Dart candidate.datum)
              (BranchVertex candidate.datum),
            source = ofDatum candidate.datum fullDim.connected fullDim.trivalent
                fullDim.pathEnds ∧
            ∃ ambient : source.Iso graph,
              (∀ d : Dart candidate.datum,
                label (ambient.dart d) =
                  fullDim.labelling.row (row candidate.datum d)) ∧
              ∃ last, ∃ path : List (CubicDartGraph (Dart candidate.datum)
                  (BranchVertex candidate.datum)),
                source.Reaches last ∧
                (source :: path).IsChain CubicDartGraph.Move ∧
                (source :: path).getLast (by simp) = last ∧
                (∀ H ∈ source :: path, H.op = source.op) ∧
                ∃ endpoint : last.Iso
                    (CubicCoreDarts.ofCore core hCubic hCoreConnected),
                  ∃ slots : coordinate ≃ Fin p,
                    (∀ d : Dart candidate.datum,
                      slots (fullDim.labelling.row (row candidate.datum d)) =
                        (endpoint.dart d).1) ∧
                    ∀ d : Dart candidate.datum,
                      slots (label (ambient.dart d)) = (endpoint.dart d).1 := by
  obtain ⟨target, data, wall, candidate, fullDim, hmatrix, hpencil, ⟨tracking⟩,
    hgenus⟩ := receipt.exists_presentation_of_genus hGraphGenus
  obtain ⟨last, path, hReach, hChain, hLast, hOp, endpoint, rows, slots,
    hslots, hrows, hcoords⟩ :=
    StableSourceWhiteheadChain.exists_chain_of_fullDimensional candidate.datum
      core hCubic hCoreConnected fullDim hChainGenus hgenus
  refine ⟨target, data, wall, candidate, fullDim, hmatrix, hpencil, _, rfl,
    tracking.iso, tracking.row_map, last, path, hReach, hChain, hLast, hOp,
    endpoint, slots, hcoords, ?_⟩
  intro d
  rw [tracking.row_map d]
  exact hcoords d

end TrackedPencil

end DraismaVargas.LocalCases
