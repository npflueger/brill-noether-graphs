import DraismaVargas.LocalCases.GlobalBookends
import DraismaVargas.LocalCases.GlobalCoarseFine
import DraismaVargas.LocalCases.GlobalM11Arbitrary
import DraismaVargas.LocalCases.GlobalM1k
import DraismaVargas.LocalCases.GlobalMkk
import DraismaVargas.LocalCases.GlobalP

/-!
# The finite endpoint of the Draisma--Vargas local classification

The source's local analysis ends in ten determinant-balance shapes, Equations
(1)--(10).  Several equations group multiple prose subcases, and Equation (3)
is used here in its stronger independently balanced two-candidate pair form.

`SourceCase` is the exact finite tag set.  `WallEvent` packages the globally
assembled family, its incoming member, and the compatible rational velocity
systems needed by `ConeWall`.  The theorem `WallEvent.exists_valid_positive_exit`
is therefore the single local-continuation endpoint.  The exhaustion of the
source case analysis then has a precise statement shape: construct a
`WallEvent` from every admissible codimension-one Draisma--Vargas wall datum.

`PresentedWallEvent` is the semantic refinement: it retains the actual
length-matrix presentations and returns a cleared rank-one pencil at the
selected positive outgoing step.

Both `systems` fields are **gated on nonsingularity of the outgoing member**.
A signed balance permits a zero determinant, so for a degenerate member the
system `M_in · v = M_out · v'` need not be solvable at all; the balancing
argument only ever uses the system at the member it selects, which has
nonzero determinant.  Section `SingularMember` at the end of this file shows
that the gate is not hygiene: it exhibits a `BalancedGlobal.PresentedFamily`
with a provably singular member and a nonsingular incoming member.
-/

namespace DraismaVargas.LocalCases.ClassifiedContinuation

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancingValencyTwo
open DraismaVargas.LocalCases.BalancedGlobal

/-- The ten determinant-balance shapes at the end of the source case tree. -/
inductive SourceCase where
  | w4
  | w3Four
  | w3Shift
  | w3Nd3CoarseFine
  | w3Nd2CoarseFine
  | w2M11
  | w2M1k
  | w2Mkk
  | w2P
  | w2R1
  deriving DecidableEq

namespace SourceCase

/-- Number of outgoing candidates in the global family used for each case.
Equation (3) uses one independently balanced shift pair. -/
def arity : SourceCase → ℕ
  | .w4 => 3
  | .w3Four => 4
  | .w3Shift => 2
  | .w3Nd3CoarseFine => 2
  | .w3Nd2CoarseFine => 2
  | .w2M11 => 3
  | .w2M1k => 3
  | .w2Mkk => 3
  | .w2P => 3
  | .w2R1 => 2

end SourceCase

variable {target : CFGraph} {degree : ℕ}
  {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- A completely classified codimension-one wall event.  Candidate validity
is part of `Family` through actual globally assembled gluing data; the fields
below contain only the rational one-column crossing information. -/
structure WallEvent (data : GluingDatum target degree) (coordinate : Type*)
    [Fintype coordinate] [DecidableEq coordinate] where
  sourceCase : SourceCase
  family : Family (coordinate := coordinate) sourceCase.arity data
  incoming : Fin sourceCase.arity
  incomingNonzero : (family.matrix incoming).det ≠ 0
  wallPoint : coordinate → ℚ
  incomingVelocity : coordinate → ℚ
  outgoingVelocity : Fin sourceCase.arity → coordinate → ℚ
  wallPoint_zero : wallPoint family.wallColumn = 0
  wallPoint_positive : ∀ i, i ≠ family.wallColumn → 0 < wallPoint i
  systems : ∀ outgoing, (family.matrix outgoing).det ≠ 0 →
    (family.matrix incoming).mulVec incomingVelocity =
      (family.matrix outgoing).mulVec (outgoingVelocity outgoing)
  incomingDirection : incomingVelocity family.wallColumn < 0

/-- A classified wall event that retains the actual globally assembled
candidates and their length-matrix presentations.  Unlike `WallEvent`, this
form can lower the selected positive outgoing point to a subdivision pencil. -/
structure PresentedWallEvent (data : GluingDatum target degree)
    (wall : target.V) (coordinate : Type*)
    [Fintype coordinate] [DecidableEq coordinate] where
  sourceCase : SourceCase
  family : PresentedFamily (coordinate := coordinate) sourceCase.arity data wall
  incoming : Fin sourceCase.arity
  incomingNonzero :
    (GluingDatum.LengthMatrixPresentation.matrix
      (family.presentation incoming)).det ≠ 0
  wallPoint : coordinate → ℚ
  incomingVelocity : coordinate → ℚ
  outgoingVelocity : Fin sourceCase.arity → coordinate → ℚ
  wallPoint_zero : wallPoint family.wallColumn = 0
  wallPoint_positive : ∀ i, i ≠ family.wallColumn → 0 < wallPoint i
  systems : ∀ outgoing,
    (GluingDatum.LengthMatrixPresentation.matrix
      (family.presentation outgoing)).det ≠ 0 →
    (GluingDatum.LengthMatrixPresentation.matrix
      (family.presentation incoming)).mulVec incomingVelocity =
    (GluingDatum.LengthMatrixPresentation.matrix
      (family.presentation outgoing)).mulVec (outgoingVelocity outgoing)
  incomingDirection : incomingVelocity family.wallColumn < 0

/-! ## The nonsingularity gate lives in `BalancedGlobal`

`BalancedGlobal.Family.exists_valid_positive_exit` and
`BalancedGlobal.PresentedFamily.exists_valid_positive_exit_with_pencil` ask
for the compatible velocity system only at the **nonsingular** members of the
family.  Both proofs use it only at the member the balance selects, and that
member has nonzero determinant because `exists_opposite_of_positiveBalance`
returns `dᵢₙ * dₒᵤₜ < 0`.

The two theorems below call them directly.  `det_ne_zero_of_mul_det_neg` is
re-exported here from `BalancedGlobal`, so that
`ClassifiedContinuation.det_ne_zero_of_mul_det_neg` resolves for the march
files. -/

export DraismaVargas.LocalCases.BalancedGlobal (det_ne_zero_of_mul_det_neg)

namespace WallEvent

/-- Every classified wall event has an actual globally valid candidate on the
opposite determinant side and a positive rational step into its cone. -/
theorem exists_valid_positive_exit
    (event : WallEvent data coordinate) (hValid : data.Valid) :
    ∃ outgoing,
      (event.family.candidate outgoing).datum.Valid ∧
      (event.family.matrix event.incoming).det *
          (event.family.matrix outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (event.wallPoint +
          t • event.outgoingVelocity outgoing) i) ∧
        (event.family.matrix outgoing).mulVec
            (event.wallPoint + t • event.outgoingVelocity outgoing) =
          (event.family.matrix event.incoming).mulVec event.wallPoint +
            t • (event.family.matrix event.incoming).mulVec
              event.incomingVelocity := by
  exact event.family.exists_valid_positive_exit hValid
    event.incoming event.incomingNonzero event.wallPoint
    event.incomingVelocity event.outgoingVelocity event.wallPoint_zero
    event.wallPoint_positive event.systems event.incomingDirection

end WallEvent

namespace PresentedWallEvent

/-- Forget presentations, for a continuation that needs only the matrices. -/
noncomputable def toWallEvent
    (event : PresentedWallEvent data wall coordinate) :
    WallEvent data coordinate where
  sourceCase := event.sourceCase
  family := event.family.toFamily
  incoming := event.incoming
  incomingNonzero := event.incomingNonzero
  wallPoint := event.wallPoint
  incomingVelocity := event.incomingVelocity
  outgoingVelocity := event.outgoingVelocity
  wallPoint_zero := event.wallPoint_zero
  wallPoint_positive := event.wallPoint_positive
  systems := event.systems
  incomingDirection := event.incomingDirection

/-- Every presented classified wall event selects an actual valid outgoing
candidate and carries a cleared rank-one pencil at every sufficiently small
positive step. -/
theorem exists_valid_positive_exit_with_pencil
    (event : PresentedWallEvent data wall coordinate)
    (hValid : data.Valid)
    (hTargetConnected : graph_connected target)
    (hTargetGenus : genus target = 0) (root : target.V) :
    ∃ outgoing,
      (event.family.candidate outgoing).datum.Valid ∧
      (GluingDatum.LengthMatrixPresentation.matrix
          (event.family.presentation event.incoming)).det *
        (GluingDatum.LengthMatrixPresentation.matrix
          (event.family.presentation outgoing)).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (event.wallPoint +
          t • event.outgoingVelocity outgoing) i) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            (event.family.presentation outgoing)).mulVec
              (event.wallPoint + t • event.outgoingVelocity outgoing) =
          (GluingDatum.LengthMatrixPresentation.matrix
            (event.family.presentation event.incoming)).mulVec
              event.wallPoint +
            t • (GluingDatum.LengthMatrixPresentation.matrix
              (event.family.presentation event.incoming)).mulVec
                event.incomingVelocity ∧
        Nonempty (Candidate.ClearedPencil
          (event.family.candidate outgoing)
          (event.family.presentation outgoing)
          (event.wallPoint + t • event.outgoingVelocity outgoing)) := by
  exact event.family.exists_valid_positive_exit_with_pencil hValid
    hTargetConnected hTargetGenus root event.incoming event.incomingNonzero
    event.wallPoint event.incomingVelocity event.outgoingVelocity
    event.wallPoint_zero event.wallPoint_positive event.systems
    event.incomingDirection

end PresentedWallEvent


/-! ## A presented family with a provably singular member

The classifier interface quantifies over `BalancedGlobal.PresentedFamily`, and
that structure constrains its members only through `positiveBalance` (a
*signed* balance, which explicitly permits a zero determinant) and
`agreeOffWall`.  `GluingDatum.LengthMatrixPresentation` in turn carries no
axiom at all relating its `path` field to the source graph.

The construction below turns one actual candidate resolution and one
presentation of it into a three-member family — the arity of
`SourceCase.w4` — whose middle member has determinant `0` while members `0`
and `2` are nonzero of opposite signs.  Member `0` is therefore a perfectly
good `incoming` member, so the family is not excluded by `incomingNonzero`:
it is exactly the situation the ungated `outgoingLabel`/`outgoingMatrix`
obligation cannot survive.

The three members are the *same* resolution displayed with three different
stable path systems: `pathZero` uses the path `[e_b, e_a]` in row `a` and
`[e_c]` in every other row; `pathOne` deletes the occurrence over the wall
edge `a`, which empties the wall column; `pathTwo` interchanges rows `a` and
`b`, which negates the determinant.  All three agree off the wall column
`a`, because rows `a` and `b` of the first differ only there. -/

namespace SingularMember


section Presentation

variable {expanded : CFGraph}

/-- The canonical source-edge occurrence over the target edge named by `c`. -/
noncomputable def edgeOver (datum : GluingDatum expanded degree)
    (label : coordinate ≃ expanded.edges) (c : coordinate) : datum.SourceEdge :=
  datum.sourceEdge (label c) ⟨0, datum.degree_pos⟩

/-- The reciprocal dilation index of `edgeOver`. -/
noncomputable def weightOver (datum : GluingDatum expanded degree)
    (label : coordinate ≃ expanded.edges) (c : coordinate) : ℚ :=
  1 / (datum.sourceEdgeIndex (edgeOver datum label c) : ℚ)

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem weightOver_ne_zero (datum : GluingDatum expanded degree)
    (label : coordinate ≃ expanded.edges) (c : coordinate) :
    weightOver datum label c ≠ 0 := by
  have hpos := datum.sourceEdgeIndex_pos (edgeOver datum label c)
  have : (datum.sourceEdgeIndex (edgeOver datum label c) : ℚ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  simpa [weightOver] using this

/-- A presentation with a prescribed path family. -/
def presOf (datum : GluingDatum expanded degree)
    (label : coordinate ≃ expanded.edges)
    (path : coordinate → List datum.SourceEdge) :
    datum.LengthMatrixPresentation coordinate where
  targetEdge := label
  path := path

omit [Fintype coordinate] in
theorem coefficient_edgeOver (datum : GluingDatum expanded degree)
    (label : coordinate ≃ expanded.edges)
    (path : coordinate → List datum.SourceEdge) (c col : coordinate) :
    GluingDatum.LengthMatrixPresentation.coefficient (presOf datum label path)
        (edgeOver datum label c) col =
      if col = c then weightOver datum label c else 0 := by
  by_cases h : col = c
  · subst h
    have hmul := GluingDatum.LengthMatrixPresentation.coefficient_mul_eq_cofactor_div
      (presentation := presOf datum label path) (edge := edgeOver datum label col)
      (column := col) (cofactor := 1) rfl
    simpa [weightOver, one_div] using hmul
  · have hne : (presOf datum label path).targetEdge col ≠
        (edgeOver datum label c).1.1 := by
      simpa [presOf, edgeOver] using fun hc => h (label.injective hc)
    simp [GluingDatum.LengthMatrixPresentation.coefficient_eq_zero_of_target_ne
      _ _ _ hne, h]

/-! ### The three path families -/

omit [Fintype coordinate] in
theorem matrix_presOf_apply (datum : GluingDatum expanded degree)
    (label : coordinate ≃ expanded.edges)
    (path : coordinate → List datum.SourceEdge) (r col : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix (presOf datum label path)
        r col =
      ((path r).map (fun e =>
        GluingDatum.LengthMatrixPresentation.coefficient
          (presOf datum label path) e col)).sum := rfl

variable (datum : GluingDatum expanded degree)
  (label : coordinate ≃ expanded.edges) (a b : coordinate)

/-- Paths of the nonsingular first member. -/
noncomputable def pathZero : coordinate → List datum.SourceEdge := fun c =>
  if c = a then [edgeOver datum label b, edgeOver datum label a]
  else [edgeOver datum label c]

/-- Paths of the singular middle member: the first member's paths with every
occurrence over the target edge `a` deleted. -/
noncomputable def pathOne : coordinate → List datum.SourceEdge := fun c =>
  if c = a then [edgeOver datum label b] else [edgeOver datum label c]

/-- Paths of the third member: the first member's paths with the two rows `a`
and `b` interchanged. -/
noncomputable def pathTwo : coordinate → List datum.SourceEdge := fun c =>
  pathZero datum label a b (Equiv.swap a b c)

/-- The common diagonal part of all three length matrices. -/
noncomputable def base : Matrix coordinate coordinate ℚ :=
  Matrix.of fun r col => if col = r then weightOver datum label r else 0

omit [Fintype coordinate] in
theorem base_eq_diagonal :
    base datum label = Matrix.diagonal (weightOver datum label) := by
  funext r col
  simp [base, Matrix.diagonal_apply, eq_comm]

omit [Fintype coordinate] in
theorem matrixZero_eq :
    GluingDatum.LengthMatrixPresentation.matrix
        (presOf datum label (pathZero datum label a b)) =
      Matrix.updateRow (base datum label) a
        (base datum label a + Pi.single b (weightOver datum label b)) := by
  funext r col
  rw [matrix_presOf_apply]
  by_cases hr : r = a
  · subst hr
    rw [Matrix.updateRow_self]
    simp only [pathZero, if_true, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, coefficient_edgeOver, Pi.add_apply,
      Pi.single_apply, base, Matrix.of_apply]
    ring
  · rw [Matrix.updateRow_ne hr]
    simp only [pathZero, if_neg hr, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, coefficient_edgeOver, base, Matrix.of_apply]
    ring

omit [Fintype coordinate] in
theorem matrixOne_eq :
    GluingDatum.LengthMatrixPresentation.matrix
        (presOf datum label (pathOne datum label a b)) =
      Matrix.updateRow (base datum label) a
        (Pi.single b (weightOver datum label b)) := by
  funext r col
  rw [matrix_presOf_apply]
  by_cases hr : r = a
  · subst hr
    rw [Matrix.updateRow_self]
    simp only [pathOne, if_true, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, coefficient_edgeOver, Pi.single_apply]
    ring
  · rw [Matrix.updateRow_ne hr]
    simp only [pathOne, if_neg hr, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, coefficient_edgeOver, base, Matrix.of_apply]
    ring

omit [Fintype coordinate] in
theorem matrixTwo_eq :
    GluingDatum.LengthMatrixPresentation.matrix
        (presOf datum label (pathTwo datum label a b)) =
      Matrix.submatrix (GluingDatum.LengthMatrixPresentation.matrix
        (presOf datum label (pathZero datum label a b)))
          (Equiv.swap a b) id := rfl

/-! ### The three determinants -/

theorem det_base_ne_zero : (base datum label).det ≠ 0 := by
  rw [base_eq_diagonal, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr
    (fun c _ => weightOver_ne_zero datum label c)

theorem det_updateRow_single_eq_zero (hab : a ≠ b) :
    (Matrix.updateRow (base datum label) a
      (Pi.single b (weightOver datum label b))).det = 0 := by
  refine Matrix.det_eq_zero_of_column_eq_zero a (fun r => ?_)
  by_cases hr : r = a
  · subst hr
    simp [Matrix.updateRow_self, hab]
  · simp [Matrix.updateRow_ne hr, base, Ne.symm hr]

theorem det_matrixOne (hab : a ≠ b) :
    (GluingDatum.LengthMatrixPresentation.matrix
      (presOf datum label (pathOne datum label a b))).det = 0 := by
  rw [matrixOne_eq]
  exact det_updateRow_single_eq_zero datum label a b hab

theorem det_matrixZero (hab : a ≠ b) :
    (GluingDatum.LengthMatrixPresentation.matrix
        (presOf datum label (pathZero datum label a b))).det =
      (base datum label).det := by
  rw [matrixZero_eq, Matrix.det_updateRow_add, Matrix.updateRow_eq_self,
    det_updateRow_single_eq_zero datum label a b hab, add_zero]

theorem det_matrixTwo (hab : a ≠ b) :
    (GluingDatum.LengthMatrixPresentation.matrix
        (presOf datum label (pathTwo datum label a b))).det =
      -(base datum label).det := by
  rw [matrixTwo_eq, Matrix.det_permute, Equiv.Perm.sign_swap hab,
    det_matrixZero datum label a b hab]
  simp

/-! ### The three presentations -/

/-- The three presentations of the singular-member family. -/
noncomputable def singularPresentation :
    Fin 3 → datum.LengthMatrixPresentation coordinate :=
  ![presOf datum label (pathZero datum label a b),
    presOf datum label (pathOne datum label a b),
    presOf datum label (pathTwo datum label a b)]

theorem det_singularPresentation_zero (hab : a ≠ b) :
    (GluingDatum.LengthMatrixPresentation.matrix
      (singularPresentation datum label a b 0)).det =
      (base datum label).det :=
  det_matrixZero datum label a b hab

theorem det_singularPresentation_one (hab : a ≠ b) :
    (GluingDatum.LengthMatrixPresentation.matrix
      (singularPresentation datum label a b 1)).det = 0 :=
  det_matrixOne datum label a b hab

theorem det_singularPresentation_two (hab : a ≠ b) :
    (GluingDatum.LengthMatrixPresentation.matrix
      (singularPresentation datum label a b 2)).det =
      -(base datum label).det :=
  det_matrixTwo datum label a b hab

omit [Fintype coordinate] in
/-- Off the wall column `a`, rows `a` and `b` of the first matrix agree. -/
theorem matrixZero_row_agree (hab : a ≠ b) (col : coordinate) (hcol : col ≠ a) :
    GluingDatum.LengthMatrixPresentation.matrix
        (presOf datum label (pathZero datum label a b)) a col =
      GluingDatum.LengthMatrixPresentation.matrix
        (presOf datum label (pathZero datum label a b)) b col := by
  rw [matrixZero_eq, Matrix.updateRow_self, Matrix.updateRow_ne (Ne.symm hab)]
  simp [base, hcol, Pi.single_apply]

omit [Fintype coordinate] in
theorem agree_one_zero (col : coordinate) (hcol : col ≠ a) (r : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (presOf datum label (pathOne datum label a b)) r col =
      GluingDatum.LengthMatrixPresentation.matrix
        (presOf datum label (pathZero datum label a b)) r col := by
  rw [matrixOne_eq, matrixZero_eq]
  by_cases hr : r = a
  · subst hr
    simp [Matrix.updateRow_self, base, hcol]
  · simp [Matrix.updateRow_ne hr]

omit [Fintype coordinate] in
theorem agree_two_zero (hab : a ≠ b) (col : coordinate) (hcol : col ≠ a)
    (r : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (presOf datum label (pathTwo datum label a b)) r col =
      GluingDatum.LengthMatrixPresentation.matrix
        (presOf datum label (pathZero datum label a b)) r col := by
  simp only [matrixTwo_eq, Matrix.submatrix_apply, id_eq]
  by_cases hr : r = a
  · rw [hr, Equiv.swap_apply_left]
    exact (matrixZero_row_agree datum label a b hab col hcol).symm
  · by_cases hr' : r = b
    · rw [hr', Equiv.swap_apply_right]
      exact matrixZero_row_agree datum label a b hab col hcol
    · rw [Equiv.swap_apply_of_ne_of_ne hr hr']

omit [Fintype coordinate] in
/-- Off the wall column `a` all three matrices agree with the first. -/
theorem singularPresentation_agree (hab : a ≠ b) (i : Fin 3)
    (r col : coordinate) (hcol : col ≠ a) :
    GluingDatum.LengthMatrixPresentation.matrix
        (singularPresentation datum label a b i) r col =
      GluingDatum.LengthMatrixPresentation.matrix
        (singularPresentation datum label a b 0) r col := by
  fin_cases i
  · rfl
  · exact agree_one_zero datum label a b col hcol r
  · exact agree_two_zero datum label a b hab col hcol r

end Presentation

section Family

variable {wall : target.V}

/-- A three-member balanced presented family whose middle member is singular.

The three members are one and the same actual resolution; only their
displayed stable paths differ.  `PresentedFamily` constrains the members
solely through `positiveBalance` and `agreeOffWall`, and
`GluingDatum.LengthMatrixPresentation` carries no axiom relating its `path`
field to the source graph, so this is a genuine inhabitant of the type over
which the classifier interface quantifies. -/
noncomputable def singularFamily
    (candidate : Candidate target degree data wall)
    (presentation : candidate.datum.LengthMatrixPresentation coordinate)
    (a b : coordinate) (hab : a ≠ b) :
    PresentedFamily (coordinate := coordinate) 3 data wall where
  candidate := fun _ => candidate
  presentation := fun i =>
    singularPresentation candidate.datum presentation.targetEdge a b i
  wallColumn := a
  weight := ![1, 1, 1]
  positiveBalance := by
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> norm_num
    · simp only [Fin.sum_univ_three,
        det_singularPresentation_zero candidate.datum
          presentation.targetEdge a b hab,
        det_singularPresentation_one candidate.datum
          presentation.targetEdge a b hab,
        det_singularPresentation_two candidate.datum
          presentation.targetEdge a b hab]
      simp
  agreeOffWall := by
    intro first second r col hcol
    exact (singularPresentation_agree candidate.datum presentation.targetEdge
        a b hab first r col hcol).trans
      (singularPresentation_agree candidate.datum presentation.targetEdge
        a b hab second r col hcol).symm

theorem singularFamily_det_one
    (candidate : Candidate target degree data wall)
    (presentation : candidate.datum.LengthMatrixPresentation coordinate)
    (a b : coordinate) (hab : a ≠ b) :
    (GluingDatum.LengthMatrixPresentation.matrix
      ((singularFamily candidate presentation a b hab).presentation 1)).det
      = 0 :=
  det_singularPresentation_one candidate.datum presentation.targetEdge a b hab

theorem singularFamily_det_zero_ne_zero
    (candidate : Candidate target degree data wall)
    (presentation : candidate.datum.LengthMatrixPresentation coordinate)
    (a b : coordinate) (hab : a ≠ b) :
    (GluingDatum.LengthMatrixPresentation.matrix
      ((singularFamily candidate presentation a b hab).presentation 0)).det
      ≠ 0 := by
  intro hzero
  refine det_base_ne_zero candidate.datum presentation.targetEdge ?_
  rw [← det_singularPresentation_zero candidate.datum presentation.targetEdge
    a b hab]
  exact hzero

theorem singularFamily_sign
    (candidate : Candidate target degree data wall)
    (presentation : candidate.datum.LengthMatrixPresentation coordinate)
    (a b : coordinate) (hab : a ≠ b) :
    (GluingDatum.LengthMatrixPresentation.matrix
        ((singularFamily candidate presentation a b hab).presentation 0)).det *
      (GluingDatum.LengthMatrixPresentation.matrix
        ((singularFamily candidate presentation a b hab).presentation 2)).det
      < 0 := by
  have hzero := det_singularPresentation_zero candidate.datum
    presentation.targetEdge a b hab
  have htwo := det_singularPresentation_two candidate.datum
    presentation.targetEdge a b hab
  have hne := det_base_ne_zero candidate.datum presentation.targetEdge
  show (GluingDatum.LengthMatrixPresentation.matrix
      (singularPresentation candidate.datum presentation.targetEdge a b 0)).det *
    (GluingDatum.LengthMatrixPresentation.matrix
      (singularPresentation candidate.datum presentation.targetEdge a b 2)).det
      < 0
  rw [hzero, htwo]
  have hsq : 0 < (base candidate.datum presentation.targetEdge).det ^ 2 :=
    pow_two_pos_of_ne_zero hne
  have hexpand : (base candidate.datum presentation.targetEdge).det *
      -(base candidate.datum presentation.targetEdge).det =
      -((base candidate.datum presentation.targetEdge).det ^ 2) := by ring
  rw [hexpand]
  linarith

/-- **Every presented family the tree builds yields one with a singular
member.**  The inputs are exactly one member of an existing
`PresentedFamily` — its candidate and its presentation — and two distinct
coordinates, so the hypotheses are satisfied wherever this tree produces a
family at all on a target with at least two edges. -/
theorem exists_singular_member_of_presentedFamily {n : ℕ}
    (family : PresentedFamily (coordinate := coordinate) n data wall)
    (member : Fin n) {a b : coordinate} (hab : a ≠ b) :
    ∃ singular : PresentedFamily (coordinate := coordinate) 3 data wall,
      (GluingDatum.LengthMatrixPresentation.matrix
        (singular.presentation 0)).det ≠ 0 ∧
      (GluingDatum.LengthMatrixPresentation.matrix
        (singular.presentation 1)).det = 0 ∧
      (GluingDatum.LengthMatrixPresentation.matrix
          (singular.presentation 0)).det *
        (GluingDatum.LengthMatrixPresentation.matrix
          (singular.presentation 2)).det < 0 :=
  ⟨singularFamily (family.candidate member) (family.presentation member) a b
      hab,
    singularFamily_det_zero_ne_zero _ _ a b hab,
    singularFamily_det_one _ _ a b hab,
    singularFamily_sign _ _ a b hab⟩

/-- **The registration obligation of the ungated interface is unsatisfiable.**

A total `outgoingLabel` into a catalogue of nonsingular chart matrices,
together with a total `outgoingMatrix`, contradicts the existence of the
family above; yet member `0` is a perfectly good incoming member, with an
opposite-sign partner at index `2`. -/
theorem no_total_registration_of_singularFamily
    {chart : Type*} (atlas : chart → Matrix coordinate coordinate ℚ)
    (hdet : ∀ l, (atlas l).det ≠ 0)
    (candidate : Candidate target degree data wall)
    (presentation : candidate.datum.LengthMatrixPresentation coordinate)
    (a b : coordinate) (hab : a ≠ b) :
    ¬ ∃ outgoingLabel : Fin 3 → chart, ∀ i,
        atlas (outgoingLabel i) =
          GluingDatum.LengthMatrixPresentation.matrix
            ((singularFamily candidate presentation a b hab).presentation i) := by
  rintro ⟨outgoingLabel, hregister⟩
  refine hdet (outgoingLabel 1) ?_
  rw [hregister 1]
  exact singularFamily_det_one candidate presentation a b hab

end Family


end SingularMember

end DraismaVargas.LocalCases.ClassifiedContinuation
