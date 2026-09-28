import DraismaVargas.LocalCases.StableSourceDartsTransport
import Utilities.CubicGraphs.CubicCoreDarts

/-!
# A finite Whitehead chain from an actual source to a requested core

This is the graph-level connection on the route of Vargas, Part II: from the
stable source of the seed to the requested core by Whitehead moves.
Universal Whitehead connectivity is applied to the constructed stable source
of the actual input datum and to the requested ordered cubic core. A finite
list of genuine non-loop moves is returned, on the original occurrence-flag
type, with its precise initial graph and a terminal graph isomorphic to that
core. Each move keeps the opposite pairs fixed.

The terminal row equivalence is NOT chosen from a cardinality equality.
It is induced by the terminal dart isomorphism: two initial flags have the
same stable row exactly when their images have the same core slot. Hence the
original matrix-coordinate dictionary also has an exact terminal slot map.

This realizes the ordinary graph linkage of Caporaso Theorem 2.4.3, through
the proved genus induction, for the actual source. It does not realize the
intermediate graph types by gluing covers: each prescribed type-changing exit
is constructed separately (`OuterWalk.TypeChangeLink`), and the graph/row
dictionary attached to the same candidate is carried through every inner
march by the outer walk (`OuterWalk`). In particular a row can change its
loop status along the graph chain, so a later non-loop move does not assert
that its original source row was non-loop. No such realization or tracking
is taken as an assumption in the existence theorem here.
-/

namespace DraismaVargas.LocalCases.StableSourceWhiteheadChain

open DraismaVargas.Infrastructure CubicDarts CubicDartGraph
open W4StableSource StableGraphIncidence StableSourceDarts
open Utilities.Certificate ExplicitPotential

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- Whitehead moves change vertex incidence but preserve literal edge pairs. -/
theorem op_eq_of_reaches {G H : CubicDartGraph D V} (h : Reaches G H) : H.op = G.op := by
  induction h with
  | refl => rfl
  | tail _ hStep ih =>
    obtain ⟨m, rfl⟩ := hStep
    exact ih

variable {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)
  (hConnected : data.Connected) (hTrivalent : ∀ v, nonDanglingValency data v ≤ 3)
  (hEnds : HasPathEnds data)
  {n p : ℕ} (core : Core n p) (hCubic : core.Cubic) (hCoreConnected : core.Connected)
  {last : CubicDartGraph (Dart data) (BranchVertex data)}
  (hReach : Reaches (ofDatum data hConnected hTrivalent hEnds) last)
  (endpoint : Iso last (CubicCoreDarts.ofCore core hCubic hCoreConnected))

include hReach

theorem endpoint_slot_eq_of_row_eq {d e : Dart data} (h : row data d = row data e) :
    (endpoint.dart d).1 = (endpoint.dart e).1 := by
  rcases (row_eq_iff data hConnected hEnds d e).mp h with rfl | rfl
  · rfl
  · have hOp := endpoint.op_map d
    have hFixed := congrFun (op_eq_of_reaches hReach) d
    change last.op d = opposite data hConnected hEnds d at hFixed
    rw [hFixed] at hOp
    have hSlot := congrArg (fun x : Fin p × Bool ↦ x.1) hOp
    exact hSlot

theorem row_eq_of_endpoint_slot_eq {d e : Dart data}
    (h : (endpoint.dart d).1 = (endpoint.dart e).1) : row data d = row data e := by
  have hPair : endpoint.dart e = endpoint.dart d ∨
      endpoint.dart e = CubicCoreDarts.opposite (endpoint.dart d) := by
    rcases hd : endpoint.dart d with ⟨i, b⟩
    rcases he : endpoint.dart e with ⟨j, c⟩
    simp only [hd, he] at h
    subst j
    cases b <;> cases c <;> simp [CubicCoreDarts.opposite]
  apply (row_eq_iff data hConnected hEnds d e).mpr
  rcases hPair with hPair | hPair
  · exact Or.inl (endpoint.dart.injective hPair)
  · right
    have hOp := endpoint.op_map d
    have hFixed := congrFun (op_eq_of_reaches hReach) d
    change last.op d = opposite data hConnected hEnds d at hFixed
    rw [hFixed] at hOp
    exact endpoint.dart.injective (hPair.trans hOp)

/-- The terminal slot map is induced by the actual terminal dart isomorphism. -/
noncomputable def terminalSlot (r : StablePath data) : Fin p :=
  (endpoint.dart (rowDart data hConnected hEnds r)).1

theorem terminalSlot_row (d : Dart data) :
    terminalSlot data hConnected hEnds core hCubic hCoreConnected endpoint (row data d) = (endpoint.dart d).1 :=
  endpoint_slot_eq_of_row_eq data hConnected hTrivalent hEnds core hCubic hCoreConnected
    hReach endpoint (row_rowDart data hConnected hEnds (row data d))

noncomputable def terminalRow : StablePath data ≃ Fin p :=
  Equiv.ofBijective (terminalSlot data hConnected hEnds core hCubic hCoreConnected endpoint) (by
    constructor
    · intro r s h
      have hRows := row_eq_of_endpoint_slot_eq data hConnected hTrivalent hEnds
        core hCubic hCoreConnected hReach endpoint h
      simpa only [row_rowDart] using hRows
    · intro i
      obtain ⟨d, hd⟩ := endpoint.dart.surjective (i, false)
      exact ⟨row data d, (terminalSlot_row data hConnected hTrivalent hEnds
        core hCubic hCoreConnected hReach endpoint d).trans (congrArg Prod.fst hd)⟩)

omit hReach in
/-- A finite graph-level Whitehead chain from the actual stable source to
the requested core. Every graph keeps the original occurrence-flag type and
opposite pairs. The terminal core-slot dictionary comes from the actual Iso.
No intermediate graph is asserted to be realized by a gluing cover. -/
theorem exists_chain_to_core (hGenus : 2 ≤ p + 1 - n)
    (hSameGenus : genus data.sourceGraph = ((p + 1 - n : ℕ) : ℤ)) :
    ∃ last : CubicDartGraph (Dart data) (BranchVertex data),
      ∃ path : List (CubicDartGraph (Dart data) (BranchVertex data)),
        Reaches (ofDatum data hConnected hTrivalent hEnds) last ∧
        (ofDatum data hConnected hTrivalent hEnds :: path).IsChain Move ∧
        (ofDatum data hConnected hTrivalent hEnds :: path).getLast (by simp) = last ∧
        (∀ H ∈ ofDatum data hConnected hTrivalent hEnds :: path,
          H.op = (ofDatum data hConnected hTrivalent hEnds).op) ∧
        ∃ endpoint : Iso last (CubicCoreDarts.ofCore core hCubic hCoreConnected),
          ∃ rows : StablePath data ≃ Fin p, ∀ d : Dart data,
            rows (row data d) = (endpoint.dart d).1 := by
  have hSource := genus_ofDatum data hConnected hTrivalent hEnds (by omega)
  have hSourceGenus : (ofDatum data hConnected hTrivalent hEnds).genus = p + 1 - n := by
    omega
  obtain ⟨last, hReach, ⟨endpoint⟩⟩ := reachesIso_of_genus_eq
    (ofDatum data hConnected hTrivalent hEnds) (CubicCoreDarts.ofCore core hCubic hCoreConnected)
    (by omega) (by rw [hSourceGenus, CubicCoreDarts.genus_ofCore])
  obtain ⟨path, hChain, hLast⟩ := List.exists_isChain_cons_of_relationReflTransGen hReach
  refine ⟨last, path, hReach, hChain, hLast, ?_, endpoint,
    terminalRow data hConnected hTrivalent hEnds core hCubic hCoreConnected hReach endpoint, ?_⟩
  · apply hChain.induction (fun H ↦ H.op = (ofDatum data hConnected hTrivalent hEnds).op)
    · intro G H hMove hEq
      obtain ⟨m, rfl⟩ := hMove
      exact hEq
    · intro _
      rfl
  · exact terminalSlot_row data hConnected hTrivalent hEnds core hCubic hCoreConnected hReach endpoint

omit hReach in
/-- The full-dimensional source supplies the genuine construction inputs.
The output is graph linkage with exact row endpoints, not a realization of the
intermediate types by covers. -/
theorem exists_chain_of_fullDimensional
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSource.FullDimensionalSourcePresentation data coordinate)
    (hGenus : 2 ≤ p + 1 - n)
    (hSameGenus : genus data.sourceGraph = ((p + 1 - n : ℕ) : ℤ)) :
    ∃ last : CubicDartGraph (Dart data) (BranchVertex data),
      ∃ path : List (CubicDartGraph (Dart data) (BranchVertex data)),
        Reaches (ofDatum data fd.connected fd.trivalent fd.pathEnds) last ∧
        (ofDatum data fd.connected fd.trivalent fd.pathEnds :: path).IsChain Move ∧
        (ofDatum data fd.connected fd.trivalent fd.pathEnds :: path).getLast (by simp) = last ∧
        (∀ H ∈ ofDatum data fd.connected fd.trivalent fd.pathEnds :: path,
          H.op = (ofDatum data fd.connected fd.trivalent fd.pathEnds).op) ∧
        ∃ endpoint : Iso last (CubicCoreDarts.ofCore core hCubic hCoreConnected),
          ∃ rows : StablePath data ≃ Fin p, ∃ coordinates : coordinate ≃ Fin p,
            coordinates = fd.labelling.row.symm.trans rows ∧
            (∀ d : Dart data, rows (row data d) = (endpoint.dart d).1) ∧
            (∀ d : Dart data, coordinates (fd.labelling.row (row data d)) = (endpoint.dart d).1) := by
  obtain ⟨last, path, hReach, hChain, hLast, hOp, endpoint, rows, hRows⟩ :=
    exists_chain_to_core data fd.connected fd.trivalent fd.pathEnds core hCubic hCoreConnected
      hGenus hSameGenus
  refine ⟨last, path, hReach, hChain, hLast, hOp, endpoint, rows,
    fd.labelling.row.symm.trans rows, rfl, hRows, ?_⟩
  intro d
  simpa using hRows d

end DraismaVargas.LocalCases.StableSourceWhiteheadChain
