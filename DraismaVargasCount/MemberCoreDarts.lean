import DraismaVargasCount.Fibre
import Utilities.CubicGraphs.CubicCoreDarts
import DraismaVargas.LocalCases.StableSourceDarts

/-!
# The stable graph of a labelled fibre member, as the requested cubic core

**Source.**  Draisma--Vargas Part I (arXiv:1909.12924): the construction of the stable
graph `H(M)` of a gluing datum (section `sec-gluing-datum`) and the labelling of its edges
by occurrences (section `section-inherited-properties`); and Vargas, Part II
(arXiv:2609.09109), the labelled fibre.  This file supplies the oriented core
identification the endgame needs to produce a pencil from a fibre member.

## What this file adds

`DraismaVargas.Count.CoreIdentification` (`Count/Fibre.lean`) records the
identification of the stable graph of a gluing datum with a requested core as
*three unoriented pieces of data*: a bijection of branch vertices with core
vertices, a bijection of stable rows with core slots, and equality of every
incidence multiplicity.  What the endgame consumes -- through
`DraismaVargas.LocalCases.TerminalIdentification.carriesCertifiedPencil_of_tracked`
-- is an **oriented** object: an isomorphism of cubic dart graphs from
`StableSourceDarts.ofDatum` onto `CubicCoreDarts.ofCore`, which must send the
two darts of a stable row to the two *named ends* of the core slot in the right
order.  A `CoreIdentification` carries no such order, so the orientation has to
be produced, and that is what this file does.

## What is proved

* `incidenceCount_eq_card_darts`, `incidenceCount_eq_indicator` -- the surviving
  occurrences of a stable row at a branch vertex are exactly the darts of that
  row sitting there, and a stable row has exactly the two darts
  `firstDart`/`secondDart` (`StableSourceDarts.rowDart` and its opposite), so the
  incidence multiplicity is the sum of two indicators.  A stable loop still
  contributes two at its one branch vertex.
* `ends_of_indicator` -- two indicator pairs with the same profile over `Fin n`
  name the same unordered pair, in either order.  This is where the matched
  incidence multiplicities of a `CoreIdentification` become an equality of the
  two ends.
* `tailDart`, `headDart`, `vertex_tailDart`, `vertex_headDart` -- the *oriented*
  choice: of the two darts of a stable row, the one sitting at the tail of the
  core slot it names, and the one sitting at its head.  The choice is made by a
  decidable test on the first dart, and both identities are then theorems, in
  the loop case as well (both ends are then the same core vertex).
* `dartEquiv`, `coreIso` -- the dart bijection and the resulting
  `CubicDarts.CubicDartGraph.Iso` from the constructed stable source of the
  datum onto the requested core.  `dartEquiv_fst` records that a dart's slot is
  read off `CoreIdentification.row`, which is the form the consumer's `hslots`
  hypothesis takes.

## What is not proved here

* `data.Connected`, `HasPathEnds data` and trivalence
  (`nonDanglingValency data v ≤ 3`) remain explicit hypotheses throughout; they
  are the three hypotheses `StableSourceDarts.ofDatum` itself needs, and a
  `FullDimensionalSource.FullDimensionalSourcePresentation` supplies all three.
* `core.Cubic` and `core.Connected` remain explicit hypotheses of `coreIso`;
  they are what `CubicCoreDarts.ofCore` needs, and nothing here derives them
  from the datum.
* Nothing here is a statement about a march, a candidate, a pencil or a
  multiplicity.  In particular no `Spec` appears: the core is a bare
  `ExplicitPotential.Core`, so loops in the core are allowed and handled.

## Consumers

`Count/MemberCertifiedPencil.lean`, which feeds
`coreIso` to `TerminalIdentification.carriesCertifiedPencil_of_tracked` as its
`endpoint` argument.
-/

namespace DraismaVargas.Count.MemberCoreDarts

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.StableSourceDarts
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.LocalCases.StablePathCount (incidenceCount incidentEdges mem_incidentEdges)
open DraismaVargas.LocalCases.W4StableSource
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {target : CFGraph.{0}} {data : GluingDatum target degree}

theorem incidenceCount_eq_card_darts (b : BranchVertex data) (r : StablePath data) :
    incidenceCount data b.1 r =
      (Finset.univ.filter
        (fun d : Dart data ↦ row data d = r ∧ vertex data d = b)).card := by
  classical
  unfold incidenceCount
  refine Finset.card_bij'
    (fun e he ↦ (⟨b, ⟨e, (mem_incidentEdges data b.1 e).mp
      (Finset.mem_filter.mp he).1⟩⟩ : Dart data))
    (fun d _ ↦ d.2.1) ?_ ?_ ?_ ?_
  · intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2, rfl⟩
  · rintro ⟨v, ⟨e, hInc⟩⟩ hd
    have hmem := Finset.mem_filter.mp hd
    have hv : v = b := hmem.2.2
    subst hv
    exact Finset.mem_filter.mpr ⟨(mem_incidentEdges data v.1 e).mpr hInc, hmem.2.1⟩
  · intro e he
    rfl
  · rintro ⟨v, ⟨e, hInc⟩⟩ hd
    have hv : v = b := (Finset.mem_filter.mp hd).2.2
    subst hv
    rfl

theorem ends_of_indicator {u w s t : Fin n}
    (H : ∀ v : Fin n, (if u = v then 1 else 0) + (if w = v then 1 else 0)
        = (if s = v then 1 else 0) + (if t = v then (1 : ℕ) else 0)) :
    (u = s ∧ w = t) ∨ (u = t ∧ w = s) := by
  by_cases hus : u = s
  · refine Or.inl ⟨hus, ?_⟩
    by_contra hwt
    have h1 := H t
    rw [if_neg hwt, if_pos (rfl : t = t)] at h1
    by_cases hst : s = t
    · rw [if_pos hst, if_pos (hus.trans hst)] at h1
      omega
    · rw [if_neg hst, if_neg (fun h : u = t ↦ hst (hus ▸ h))] at h1
      omega
  · have hws : w = s := by
      by_contra hw
      have h1 := H s
      rw [if_neg hus, if_neg hw, if_pos (rfl : s = s)] at h1
      split_ifs at h1 <;> omega
    have hts : ¬ (t = s) := by
      intro h
      have h1 := H s
      rw [if_neg hus, if_pos hws, if_pos (rfl : s = s), if_pos h] at h1
      omega
    refine Or.inr ⟨?_, hws⟩
    by_contra hut
    have h1 := H t
    rw [if_neg hut, if_pos (rfl : t = t),
      if_neg (fun h : w = t ↦ hts (hws ▸ h).symm),
      if_neg (fun h : s = t ↦ hts h.symm)] at h1
    omega

section Darts

variable (hConnected : data.Connected) (hEnds : HasPathEnds data)

/-- The dart of the stable row `r` named by `rowDart`. -/
noncomputable def firstDart (r : StablePath data) : Dart data :=
  rowDart data hConnected hEnds r

/-- The other dart of the stable row `r`. -/
noncomputable def secondDart (r : StablePath data) : Dart data :=
  opposite data hConnected hEnds (firstDart hConnected hEnds r)

theorem row_firstDart (r : StablePath data) :
    row data (firstDart hConnected hEnds r) = r :=
  row_rowDart data hConnected hEnds r

theorem row_secondDart (r : StablePath data) :
    row data (secondDart hConnected hEnds r) = r := by
  rw [secondDart, row_opposite, row_firstDart]

theorem firstDart_ne_secondDart (r : StablePath data) :
    firstDart hConnected hEnds r ≠ secondDart hConnected hEnds r :=
  Ne.symm (opposite_ne data hConnected hEnds _)

theorem incidenceCount_eq_indicator (b : BranchVertex data) (r : StablePath data) :
    incidenceCount data b.1 r =
      (if vertex data (firstDart hConnected hEnds r) = b then 1 else 0) +
        (if vertex data (secondDart hConnected hEnds r) = b then 1 else 0) := by
  classical
  rw [incidenceCount_eq_card_darts b r]
  have hset : (Finset.univ.filter
      (fun d : Dart data ↦ row data d = r ∧ vertex data d = b)) =
      ({firstDart hConnected hEnds r, secondDart hConnected hEnds r} :
        Finset (Dart data)).filter (fun d ↦ vertex data d = b) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hr, hv⟩
      refine ⟨?_, hv⟩
      have hrow : row data (firstDart hConnected hEnds r) = row data d := by
        rw [row_firstDart, hr]
      rcases (row_eq_iff data hConnected hEnds _ d).mp hrow with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro ⟨hd, hv⟩
      refine ⟨?_, hv⟩
      rcases hd with rfl | rfl
      · exact row_firstDart hConnected hEnds r
      · exact row_secondDart hConnected hEnds r
  rw [hset, Finset.card_filter,
    Finset.sum_pair (firstDart_ne_secondDart hConnected hEnds r)]

/-- Every dart of a stable row is one of its two named darts. -/
theorem eq_first_or_second {d : Dart data} {r : StablePath data} (hd : row data d = r) :
    d = firstDart hConnected hEnds r ∨ d = secondDart hConnected hEnds r := by
  have hrow : row data (firstDart hConnected hEnds r) = row data d := by
    rw [row_firstDart, hd]
  exact (row_eq_iff data hConnected hEnds _ d).mp hrow

end Darts

/-! ## The oriented dart dictionary of a core identification -/

section Orientation

variable {core : Core n p} (hConnected : data.Connected) (hEnds : HasPathEnds data)
  (ident : CoreIdentification core data)

/-- The two ends of a stable row carry the two ends of the core slot it names. -/
theorem ends_of_ident (r : StablePath data) :
    (ident.vertex (vertex data (firstDart hConnected hEnds r)) =
        core.tail (ident.row r) ∧
      ident.vertex (vertex data (secondDart hConnected hEnds r)) =
        core.head (ident.row r)) ∨
    (ident.vertex (vertex data (firstDart hConnected hEnds r)) =
        core.head (ident.row r) ∧
      ident.vertex (vertex data (secondDart hConnected hEnds r)) =
        core.tail (ident.row r)) := by
  refine ends_of_indicator (fun v ↦ ?_)
  have hIdent := ident.incidence (ident.vertex.symm v) (ident.row r)
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply,
    incidenceCount_eq_indicator hConnected hEnds] at hIdent
  have hIte : ∀ d : Dart data,
      (if vertex data d = ident.vertex.symm v then (1 : ℕ) else 0) =
        (if ident.vertex (vertex data d) = v then 1 else 0) := by
    intro d
    by_cases h : ident.vertex (vertex data d) = v
    · rw [if_pos h, if_pos (by rw [← h, Equiv.symm_apply_apply])]
    · refine (if_neg ?_).trans (if_neg h).symm
      intro hh
      exact h (by rw [hh, Equiv.apply_symm_apply])
  rw [hIte, hIte] at hIdent
  rw [hIdent, coreIncidence]

/-- The dart of the stable row `r` sitting at the tail of the core slot. -/
noncomputable def tailDart (r : StablePath data) : Dart data :=
  if ident.vertex (vertex data (firstDart hConnected hEnds r)) =
      core.tail (ident.row r) then firstDart hConnected hEnds r
    else secondDart hConnected hEnds r

/-- The dart of the stable row `r` sitting at the head of the core slot. -/
noncomputable def headDart (r : StablePath data) : Dart data :=
  opposite data hConnected hEnds (tailDart hConnected hEnds ident r)

theorem row_tailDart (r : StablePath data) :
    row data (tailDart hConnected hEnds ident r) = r := by
  unfold tailDart
  split_ifs
  · exact row_firstDart hConnected hEnds r
  · exact row_secondDart hConnected hEnds r

theorem row_headDart (r : StablePath data) :
    row data (headDart hConnected hEnds ident r) = r := by
  rw [headDart, row_opposite, row_tailDart]

theorem headDart_ne_tailDart (r : StablePath data) :
    headDart hConnected hEnds ident r ≠ tailDart hConnected hEnds ident r :=
  opposite_ne data hConnected hEnds _

theorem opposite_headDart (r : StablePath data) :
    opposite data hConnected hEnds (headDart hConnected hEnds ident r) =
      tailDart hConnected hEnds ident r :=
  opposite_opposite data hConnected hEnds _

theorem vertex_tailDart (r : StablePath data) :
    ident.vertex (vertex data (tailDart hConnected hEnds ident r)) =
      core.tail (ident.row r) := by
  unfold tailDart
  split_ifs with h
  · exact h
  · rcases ends_of_ident hConnected hEnds ident r with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact absurd h1 h
    · exact h2

theorem vertex_headDart (r : StablePath data) :
    ident.vertex (vertex data (headDart hConnected hEnds ident r)) =
      core.head (ident.row r) := by
  unfold headDart tailDart
  split_ifs with h
  · show ident.vertex (vertex data (secondDart hConnected hEnds r)) = core.head (ident.row r)
    rcases ends_of_ident hConnected hEnds ident r with ⟨_, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exact h2.trans (h.symm.trans h1)
  · rw [show secondDart hConnected hEnds r =
        opposite data hConnected hEnds (firstDart hConnected hEnds r) from rfl,
      opposite_opposite]
    rcases ends_of_ident hConnected hEnds ident r with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact absurd h1 h
    · exact h1

/-! ### The dart bijection -/

/-- `false` on the tail dart of its own stable row, `true` on the head dart. -/
noncomputable def dartFlag (d : Dart data) : Bool :=
  if d = tailDart hConnected hEnds ident (row data d) then false else true

theorem dartFlag_tailDart (r : StablePath data) :
    dartFlag hConnected hEnds ident (tailDart hConnected hEnds ident r) = false := by
  unfold dartFlag
  rw [row_tailDart]
  exact if_pos rfl

theorem dartFlag_headDart (r : StablePath data) :
    dartFlag hConnected hEnds ident (headDart hConnected hEnds ident r) = true := by
  unfold dartFlag
  rw [row_headDart]
  exact if_neg (headDart_ne_tailDart hConnected hEnds ident r)

theorem eq_headDart_of_ne {d : Dart data}
    (h : d ≠ tailDart hConnected hEnds ident (row data d)) :
    d = headDart hConnected hEnds ident (row data d) :=
  opposite_eq_of_row_eq data hConnected hEnds (row_tailDart hConnected hEnds ident _).symm h

theorem dartFlag_opposite (d : Dart data) :
    dartFlag hConnected hEnds ident (opposite data hConnected hEnds d) =
      !dartFlag hConnected hEnds ident d := by
  by_cases h : d = tailDart hConnected hEnds ident (row data d)
  · have hFlag : dartFlag hConnected hEnds ident d = false := by
      unfold dartFlag; exact if_pos h
    rw [hFlag, Bool.not_false]
    conv_lhs => rw [h]
    exact dartFlag_headDart hConnected hEnds ident _
  · have hFlag : dartFlag hConnected hEnds ident d = true := by
      unfold dartFlag; exact if_neg h
    rw [hFlag, Bool.not_true]
    conv_lhs => rw [eq_headDart_of_ne hConnected hEnds ident h]
    rw [opposite_headDart]
    exact dartFlag_tailDart hConnected hEnds ident _

/-- **The dart bijection.**  A dart of the stable source is the core slot its
stable row names, together with the end of that slot it sits at. -/
noncomputable def dartEquiv : Dart data ≃ Fin p × Bool where
  toFun d := (ident.row (row data d), dartFlag hConnected hEnds ident d)
  invFun x := if x.2 then headDart hConnected hEnds ident (ident.row.symm x.1)
    else tailDart hConnected hEnds ident (ident.row.symm x.1)
  left_inv d := by
    simp only [Equiv.symm_apply_apply]
    by_cases h : d = tailDart hConnected hEnds ident (row data d)
    · have hFlag : dartFlag hConnected hEnds ident d = false := by
        unfold dartFlag; exact if_pos h
      rw [hFlag]
      exact h.symm
    · have hFlag : dartFlag hConnected hEnds ident d = true := by
        unfold dartFlag; exact if_neg h
      rw [hFlag]
      exact (eq_headDart_of_ne hConnected hEnds ident h).symm
  right_inv x := by
    obtain ⟨i, b⟩ := x
    cases b
    · simp only [Bool.false_eq_true, if_false]
      rw [row_tailDart, Equiv.apply_symm_apply,
        dartFlag_tailDart hConnected hEnds ident]
    · simp only [if_true]
      rw [row_headDart, Equiv.apply_symm_apply,
        dartFlag_headDart hConnected hEnds ident]

@[simp] theorem dartEquiv_fst (d : Dart data) :
    (dartEquiv hConnected hEnds ident d).1 = ident.row (row data d) := rfl

/-- **The stable graph of a core identification is the requested core.** -/
noncomputable def coreIso (hTrivalent : ∀ v, nonDanglingValency data v ≤ 3)
    (hCubic : core.Cubic) (hCoreConnected : core.Connected) :
    CubicDartGraph.Iso (ofDatum data hConnected hTrivalent hEnds)
      (CubicCoreDarts.ofCore core hCubic hCoreConnected) where
  dart := dartEquiv hConnected hEnds ident
  vtx := ident.vertex
  op_map x := by
    refine Prod.ext ?_ ?_
    · show ident.row (row data x) = ident.row (row data (opposite data hConnected hEnds x))
      rw [row_opposite]
    · show (!dartFlag hConnected hEnds ident x) =
        dartFlag hConnected hEnds ident (opposite data hConnected hEnds x)
      rw [dartFlag_opposite]
  vert_map x := by
    show CubicCoreDarts.vertex core (ident.row (row data x),
        dartFlag hConnected hEnds ident x) = ident.vertex (vertex data x)
    by_cases h : x = tailDart hConnected hEnds ident (row data x)
    · have hFlag : dartFlag hConnected hEnds ident x = false := by
        unfold dartFlag; exact if_pos h
      rw [hFlag]
      show core.tail (ident.row (row data x)) = ident.vertex (vertex data x)
      conv_rhs => rw [h]
      exact (vertex_tailDart hConnected hEnds ident _).symm
    · have hFlag : dartFlag hConnected hEnds ident x = true := by
        unfold dartFlag; exact if_neg h
      rw [hFlag]
      show core.head (ident.row (row data x)) = ident.vertex (vertex data x)
      conv_rhs => rw [eq_headDart_of_ne hConnected hEnds ident h]
      exact (vertex_headDart hConnected hEnds ident _).symm

end Orientation


end DraismaVargas.Count.MemberCoreDarts
