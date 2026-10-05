module

public import DraismaVargas.LocalCases.ClassInjectivity
public import DraismaVargas.LocalCases.TerminalExhausts

@[expose] public section

/-!
# The certified march payload

A terminal state of the march is completed to a terminal face from data the
state itself carries, and `TerminalExhausts.TerminalCertificate` is exactly
what suffices for that.  `SemanticAtlasMarch.CarriesClearedPencil`, the
payload a `SemanticAtlasMarch.State` carries, supplies the target, the gluing
datum, the wall, the candidate, `presentation_matrix`, `valid`, `connected`
and `targetGenus`.  Missing are a `TraversalPresentation.StrongPresentation`,
an `InputRefinementData.InputInterface`, an `OrientedTraversal.RowDictionary`
with its spanning and injectivity halves, and
`TerminalExhausts.SourceGenusMatches`.  `CarriesCertifiedPencil` below is
`CarriesClearedPencil` with those adjoined, and
`nonempty_terminalCertificate_of_certified` assembles the certificate at a
terminal state.

## Why they go inside the same binder group

A completed terminal face is data (a `Type`), so extracting it from a
`Prop`-valued payload goes through `Classical.choice` (compare the note on
candidate provenance in `ZeroFreeTerminalFace`).  A receipt carried *outside*
the payload's existential would therefore have to hold for **every** candidate
realising the chart matrix, and one bad candidate defeats it.  So the strong
presentation, the interface, the dictionary and the three receipts are bound
by the *same* `∃` as the candidate, and `carriesClearedPencil_of_certified` is
the projection back onto `CarriesClearedPencil`.

## The two coordinate vectors

A `SemanticAtlasMarch.State` carries its pencil at `currentStart`, but the
cleared *face* of a terminal state is at `currentFinish`
(`SemanticAtlasMarch.State.clearedFace`,
`ZeroFreeTerminalFace.clearedFaceOfTerminal`), and the interface and the row
dictionary are stated at the face.  `CarriesCertifiedPencil` therefore takes
both vectors: the pencil is at `start`, and the certificate half is at
`finish`.  Since `Candidate.clearedFace` needs nonnegativity — which only a
terminal state has — the certificate half is stated *under* that hypothesis,
but still inside the candidate's binder group, so the certificate is about the
very candidate the pencil half bound.  The predicate is meaningful at every
state, terminal or not, which is what a field of `State` has to be.

## Two presentations of one candidate

`SemanticAtlasMarch.CarriesClearedPencil` carries a
`FullDimensionalSource.FullDimensionalSourcePresentation` of its candidate,
because the continuation of the march classifies the incoming cover through
`IncomingSourceCases.exists_classification`, which takes one.
`CarriesCertifiedPencil` carries **both** that full-dimensional presentation
and a strong one, over the same candidate and with the same matrix.  It does
*not* derive the strong one as `TraversalPresentation.ofFullDimensional fullDim`,
even though that map exists: `ofFullDimensional` fixes the row orientations to
the generic traversal's, while a certified terminal face may need *chosen*
orientations, for instance when its `OrientedTraversal.RowDictionary` names
the two poles of a stable theta graph explicitly.  Carrying both is therefore
not redundancy: the continuation of the march reads the full-dimensional
presentation, and the completion of the terminal face reads the strong one.
-/

namespace DraismaVargas.LocalCases.CertifiedPencil

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.OrientedTraversal
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.RefinementCore
open DraismaVargas.LocalCases.SemanticAtlasMarch
open DraismaVargas.LocalCases.TerminalExhausts
open DraismaVargas.LocalCases.TraversalPresentation

/-! ## 1.  The payload -/

section Payload

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The certified pencil.**  `SemanticAtlasMarch.CarriesClearedPencil`
extended, *in the same binder group*, by everything
`TerminalExhausts.TerminalCertificate` asks for beyond the cleared pencil:

* a `TraversalPresentation.StrongPresentation` displaying the same chart matrix
  as the payload's full-dimensional presentation — so the matrix
  identification, the pencil and the traversal structure are all about one
  candidate, and the continuation of the march and the completion of the
  terminal face read the two presentations they respectively need off one
  binder;
* `TerminalExhausts.SourceGenusMatches`, the datum-level genus receipt, which
  mentions no face and so sits outside the nonnegativity hypothesis;
* and, at a nonnegative `finish`, an `InputInterface` at `finish` **and at the
  forest `F`**, a `RowDictionary` (which mentions no face), and the two local
  receipts `StrongRefinement.Faithful` and `StrongRefinement.Spanning`.

`F` is the expansion forest, the slot set on which the requested metric
vanishes (`RequestedExpandedEndpoints`); it defaults to `∅`.

The last group is stated under the hypothesis `∀ i, 0 ≤ finish i`, which is
what `Candidate.clearedFace` needs.  The three-field dictionary mentions no
face, so the body does not use the hypothesis, which is why it is not named;
it records that the certificate half is asked for only at a nonnegative
`finish`.  This is not a quantifier over candidates: the candidate, the
presentation and the pencil are bound once, outside. -/
def CarriesCertifiedPencil {n p : ℕ} (spec : Spec n p) (degree : ℕ)
    (matrix : Matrix coordinate coordinate ℚ)
    (start finish : coordinate → ℚ)
    (F : Finset (Fin p) := ∅) : Prop :=
  ∃ (target : CFGraph.{0}) (data : GluingDatum target degree) (wall : target.V)
      (candidate : Candidate target degree data wall)
      (fullDim : FullDimensionalSourcePresentation candidate.datum coordinate)
      (strong : StrongPresentation candidate.datum coordinate),
    GluingDatum.LengthMatrixPresentation.matrix
        fullDim.labelling.presentation = matrix ∧
      GluingDatum.LengthMatrixPresentation.matrix strong.toPresentation =
        matrix ∧
      data.Valid ∧
      graph_connected target ∧
      genus target = 0 ∧
      Nonempty (Candidate.ClearedPencil candidate
        fullDim.labelling.presentation start) ∧
      SourceGenusMatches spec candidate.datum ∧
      ((∀ i, 0 ≤ finish i) →
        ∃ (iface : InputInterface spec strong.toPresentation finish F)
            (dict : RowDictionary strong spec iface),
          StrongRefinement.Faithful (RowDictionary.coreDictionary dict) ∧
            StrongRefinement.Spanning (RowDictionary.coreDictionary dict))

/-- **The certified payload implies the cleared one.**  Forgetting the strong
presentation and the whole certificate half leaves exactly
`SemanticAtlasMarch.CarriesClearedPencil`, so a state field of the certified
type can stand wherever one of the cleared type is expected. -/
theorem carriesClearedPencil_of_certified {n p : ℕ} {spec : Spec n p}
    {degree : ℕ} {matrix : Matrix coordinate coordinate ℚ}
    {start finish : coordinate → ℚ} {F : Finset (Fin p)}
    (certified : CarriesCertifiedPencil spec degree matrix start finish F) :
    CarriesClearedPencil degree matrix start := by
  obtain ⟨target, data, wall, candidate, fullDim, strong, hMatrix, -, hValid,
    hConnected, hGenus, hPencil, -, -⟩ := certified
  exact ⟨target, data, wall, candidate, fullDim, hMatrix, hValid,
    hConnected, hGenus, hPencil⟩

end Payload

/-! ## 2.  The payoff: a certified state completes its terminal face -/

section Payoff

variable {coordinate chart : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ} {matrix : chart → Matrix coordinate coordinate ℚ}
  {baseStart baseFinish : coordinate → ℚ}

/-- **The certificate, assembled.**  Every field of
`TerminalExhausts.TerminalCertificate` is read off the payload: eight from the
`CarriesClearedPencil` part, the genus receipt from its own conjunct, and the
strong presentation, interface, dictionary and injectivity from the
certificate half at `currentFinish`, whose nonnegativity hypothesis is the
state's own `Terminal`.

Injectivity is `ClassInjectivity.injective_vertexClass_of_faithful`, whose two
hypotheses are exactly the two receipts the payload carries. -/
theorem nonempty_terminalCertificate_of_certified {n p : ℕ} {spec : Spec n p}
    {state : State degree matrix baseStart baseFinish} (hTerminal : state.Terminal)
    (certified : CarriesCertifiedPencil spec degree
      (matrix state.toMatrixState.label) state.toMatrixState.currentStart
      state.toMatrixState.currentFinish) :
    Nonempty (TerminalCertificate spec state hTerminal) := by
  obtain ⟨target, data, wall, candidate, fullDim, strong, -, hMatrix, hValid,
    hConnected, hGenus, -, hSource, hCert⟩ := certified
  obtain ⟨iface, dict, hFaithful, hSpanning⟩ := hCert hTerminal
  exact ⟨{ target := target
           gluing := data
           wall := wall
           candidate := candidate
           strong := strong
           iface := iface
           dict := dict
           spanning := hSpanning
           injective := fun topology ↦
             ClassInjectivity.injective_vertexClass_of_faithful dict topology
               hFaithful hSpanning
           sourceGenus := hSource
           presentation_matrix := hMatrix
           valid := hValid
           connected := hConnected
           targetGenus := hGenus }⟩

end Payoff

end DraismaVargas.LocalCases.CertifiedPencil
