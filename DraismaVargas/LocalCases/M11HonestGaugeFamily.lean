import DraismaVargas.LocalCases.M11CommonBalance

/-!
# Figure 32 as a `BalancedGlobal.GaugeFamily`

Figure 32 is the M11 case of Draisma--Vargas Part I, Case {w2-r2-nd3-M-11},
with its three members and Equation (6).

`M11CommonBalance.family` is a `BalancedGlobal.Family`: it keeps the three
actual candidates as `CertifiedCandidate data`s and their three square
*matrices*, and forgets the presentations that produced them.  A
`WallProgress.WallInput` wants the other half — the occurrence-level
`BalancedGlobal.Candidate`s and their `LengthMatrixPresentation`s — so the
march cannot be fed from `family` as it stands.

It also cannot be fed from a `BalancedGlobal.PresentedFamily`, and no lemma
can repair that.  `M11RemoteCandidates.candidates` is
`GlobalM11Arbitrary.candidates … = ![first.certified, remoteCertified … second,
third.certified]`, whose **middle** member is assembled from a `SplitPattern`
over the branch-swapped datum
`GlobalM11Arbitrary.SwappedDatum data wall root hRoot distinguished other
hTogether` — i.e. `M11RemoteCandidates.swappedDatum profile hCard` — with
`valid_of_old` routed through `ResolutionM11.wallBranchSwap_preserves_valid`.
`PresentedFamily.candidate` fixes **one** base datum, and the middle member is
not a `Candidate target degree data wall` at all, so the type does not exist.

`BalancedGlobal.GaugeFamily` removes the obstruction: it carries
`base : Fin n → GluingDatum target degree` and its own `valid_of_old`, and
`GaugeFamily.exists_valid_positive_exit_with_pencil` is the positive exit with
each member's validity routed through its own gauge.  This file puts Figure 32
in it.

## What is here, and what it costs

| field | value | why |
|---|---|---|
| `base` | `![data, swappedDatum profile hCard, data]` | the middle split is remote |
| `valid_of_old` | `id`, `wallBranchSwap_preserves_valid`, `id` | `M11RemoteCandidates.secondSplit_valid`'s proof |
| `candidate` | `firstSplitPattern`, `secondSplitPattern`, `joinedPattern`, each `.candidate` | the occurrence-level members `M11RemoteCandidates.candidates` certifies |
| `presentation` | `M11CommonBalance.labelling … initial i` | the *honest* labellings, retained |
| `wallColumn`, `weight`, `positiveBalance`, `agreeOffWall` | `M11CommonBalance`'s | Equation (6), unchanged |

**No hypothesis is added** beyond the ones `M11CommonBalance.family` takes
(`hConnected`, `hGenus` and one honest square labelling `initial` of member
`0`).  Every field is `rfl`-level against `M11CommonBalance`:
`presentation_matrix` is `fin_cases i <;> rfl`, which is what makes
`positiveBalance` and `agreeOffWall` one `simpa`/`rw` each, and what makes the
`presentation_eq` field of `A04FourTags.FullDimSupply` literal downstream.

`candidate i`'s outgoing datum is *definitionally* the certified member's:
`(candidate input profile hCard i).datum` and
`(M11RemoteCandidates.candidates input profile hCard i).datum` agree at each of
the three literals, because `SplitPattern.certified`/`JoinedPattern.certified`
are `Candidate.certified` of exactly these candidates and
`GlobalM11Arbitrary.remoteCertified`'s `datum` field is
`pattern.candidate.datum`.  That is why `presentation` typechecks with
`M11CommonBalance`'s labellings unmodified, and it is the whole reason this
packaging is mechanical.

Write `candidate` and `presentation` with term-mode equations, as
`W2MkkArbitraryExit.firstCandidate`/`firstPresentation` do: a tactic-mode
`intro i; match i with …` does not refine the expected type per branch, and the
`isDefEq` it then poses on `M11CommonBalance.squareMatrix` is the expensive one.

This file does not import `WallProgress`; the wall input, the full-dimensional
supply and the routed wall are in `A04M11Wiring`.
-/

namespace DraismaVargas.LocalCases.M11HonestGaugeFamily

open DraismaVargas.Infrastructure
open W4Assembly W4StableSource W2R1Target SecondEquation
open ResolutionM11 GlobalM11Arbitrary
open M11SourceCandidates M11RemoteCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Figure 32's three base data: the incoming datum, the branch-swapped copy
carrying the remote second split, the incoming datum. -/
noncomputable def base (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    Fin 3 → GluingDatum target degree
  | 0 => data
  | 1 => swappedDatum profile hCard
  | 2 => data

/-- Its three occurrence-level candidates, each over its own base.  These are
the members `M11RemoteCandidates.candidates` certifies, before the passage to
`BalancedGlobal.CertifiedCandidate` forgets which datum each was built on. -/
noncomputable def candidate (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    ∀ i : Fin 3, BalancedGlobal.Candidate target degree (base profile hCard i) wall
  | 0 => (firstSplitPattern input profile hCard).candidate
  | 1 => (secondSplitPattern input profile hCard).candidate
  | 2 => (joinedPattern data star block hCard).candidate

/-- The three retained honest presentations, typed at those candidates.  They
are `M11CommonBalance.labelling`'s, unchanged: the middle one typechecks over
the remote member only because `candidate … 1`'s outgoing datum is the remote
certified member's datum by definition. -/
noncomputable def presentation (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (initial : StableLengthMatrixLabelling
      (M11RemoteCandidates.candidates input profile hCard 0).datum coordinate) :
    ∀ i : Fin 3,
      (candidate input profile hCard i).datum.LengthMatrixPresentation coordinate
  | 0 => (M11CommonBalance.labelling input profile hCard initial 0).presentation
  | 1 => (M11CommonBalance.labelling input profile hCard initial 1).presentation
  | 2 => (M11CommonBalance.labelling input profile hCard initial 2).presentation

omit [Fintype coordinate] in
/-- and their matrices are `M11CommonBalance`'s own square matrices. -/
theorem presentation_matrix (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (initial : StableLengthMatrixLabelling
      (M11RemoteCandidates.candidates input profile hCard 0).datum coordinate)
    (i : Fin 3) :
    GluingDatum.LengthMatrixPresentation.matrix
        (presentation input profile hCard initial i) =
      M11CommonBalance.squareMatrix input profile hCard initial i := by
  fin_cases i <;> rfl

/-- **Figure 32 as a gauge family.**  The weights are Equation (6)'s
`1, 1, 4`, the balance is `M11CommonBalance.positiveBalance` (no member assumed
nonsingular, the joined one included), the off-wall agreement is
`M11CommonBalance.matrices_agree`, and the middle member's validity is the
branch swap's. -/
noncomputable def gaugeFamily (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (initial : StableLengthMatrixLabelling
      (M11RemoteCandidates.candidates input profile hCard 0).datum coordinate) :
    BalancedGlobal.GaugeFamily (coordinate := coordinate) 3 data wall where
  base := base profile hCard
  valid_of_old := fun i hValid ↦ by
    match i with
    | 0 => exact hValid
    | 1 => exact wallBranchSwap_preserves_valid data hValid wall _ _ _ _ _
    | 2 => exact hValid
  candidate := candidate input profile hCard
  presentation := presentation input profile hCard initial
  wallColumn := M11CommonBalance.wallColumn input profile hCard initial
  weight := ![1, 1, 4]
  positiveBalance := by
    have h := M11CommonBalance.positiveBalance input profile hCard initial hConnected hGenus
    exact ⟨h.1, by simpa only [presentation_matrix] using h.2⟩
  agreeOffWall := fun first second ↦ by
    rw [presentation_matrix, presentation_matrix]
    exact M11CommonBalance.matrices_agree input profile hCard initial first second

/-- The gauge family's matrices are the balance's, position by position. -/
theorem gaugeFamily_matrix (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (initial : StableLengthMatrixLabelling
      (M11RemoteCandidates.candidates input profile hCard 0).datum coordinate)
    (i : Fin 3) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((gaugeFamily input profile hCard hConnected hGenus initial).presentation i) =
      (M11CommonBalance.family input profile hCard initial hConnected hGenus).matrix i :=
  presentation_matrix input profile hCard initial i

/-- and its regrown column is the balance's. -/
@[simp] theorem gaugeFamily_wallColumn (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (initial : StableLengthMatrixLabelling
      (M11RemoteCandidates.candidates input profile hCard 0).datum coordinate) :
    (gaugeFamily input profile hCard hConnected hGenus initial).wallColumn =
      M11CommonBalance.wallColumn input profile hCard initial := rfl

end DraismaVargas.LocalCases.M11HonestGaugeFamily
