import DraismaVargas.LocalCases.W3ShiftClosure
import DraismaVargas.LocalCases.RelabelFullDimensional
import DraismaVargas.LocalCases.W3ShiftIncomingMatching

/-!
# The Position II.a branch-swap transport of the incoming datum

Source: Draisma--Vargas Part I, Case {w3-r1-nd3-t2-(a>k4)} (the `w3Shift`
case), Figure 29 and Equation (3).  Part I works with isomorphism classes of
gluing datums, so its branch-swaps are free; for fixed Lean data they have to
be performed explicitly, and this file performs one on the incoming datum.

When the incoming cover is Figure 29's **Position II.a** member and no shrink
sheet exists on its own wall datum, `W3ShiftClosure.exists_gauge_shift_pair`
produces Equation (3)'s pair over a branch-swapped copy of the *wall* datum,
and the incoming cover is not a member over that copy: the swap has moved the
very partitions the identification compares.  What handles that case is the
**same swap performed one level up**, on the incoming datum itself, before the
contraction.

## What is proved

1. **The relabelling** (`branchRelabel`, `swappedDatum`).  The branch region of
   `TargetBranchRegion` at the contracted wall `⟨a, hab⟩` is pulled back along
   the contraction: `movedVertex v := TargetBranchRegion.vertexMoved ⟨a,hab⟩
   root hRoot (fold target hab v)` and an occurrence is moved when either
   endpoint is.  The wall vertex is never in a branch
   (`TargetBranchRegion.vertexMoved_wall`), so `movedVertex a = movedVertex b =
   false` and `movedEdge contracted = false`: the wall occurrence and both its
   ends sit outside the moved region.  `boundary_left` / `boundary_right` then
   say that every selected/unselected incidence of the pulled-back region sits
   at `a` or at `b`, which is exactly where
   `GluingDatum.SheetRelabeling.ofRegion` asks for a block-preservation proof.
   `EndsCompatible` is that hypothesis and nothing more: *at each end of the
   wall occurrence the moved branch actually touches, the permutation preserves
   that end's own blocks*.

2. **The commutation** (`contract_swappedDatum`), as a literal `GluingDatum`
   equality:

       contractDatum (branchRelabel …).apply hc hab hOne
         = (branchSwapOfPerm (contractDatum data hc hab hOne) ⟨a,hab⟩ root hRoot
             permutation hFixWall).apply

   Swapping above a branch of the incoming target and then contracting the wall
   occurrence is the *same datum* as contracting first and then swapping.  At
   the merged vertex both sides are the untouched join `A₀`
   (`W3ShiftClosure.branchSwap_vertexPermutation_wall` is the contracted-level
   half of this); away from it `fold` is the identity; and on occurrences the
   two regions agree because `fold_unfoldEdge` matches the endpoints.
   `gluingDatum_ext` is the (proof-irrelevant) extensionality used.

3. **The consequences.**  `swappedFullDim` is
   `RelabelFullDimensional.sheetPresentation` of the incoming cover's own
   full-dimensional presentation: `swappedFullDim_matrix` gives the length
   matrix **literally equal** to `fullDim`'s and `swappedFullDim_targetEdge` the
   same column labelling, by `rfl`.  `contractionForest_swappedDatum`,
   `swappedDatum_mergedPartition` and `selectedCensus_swappedDatum` carry the
   contraction hypothesis and the selected-block census across unchanged -- all
   four partitions they mention (`vp a`, `vp b`, `edgePartition contracted`,
   the merged one) are literally the incoming cover's.
   `divalentOccurrence_congr` says the divalent wall occurrence does not depend
   on the cover at all, its characterisation being a condition on the target.
   `swappedIncidence` is `StableGraphIncidence.sheetRelabel`, the dictionary
   pair for any relabelling.

With these, the exit of the `w3Shift` case can be run over the swapped cover
and restated in the **original** cover's coordinates -- same length matrix,
same wall column, and a `StableGraphIncidence.Equivalence` between the
*original* incoming cover and the identified member, obtained by composing
`swappedIncidence` with the one the exit returns (see `W3ShiftClosureFinal`).
So the transport changes nothing a consumer reads off the statement.

## The endpoint compatibility

`EndsCompatible` is **strictly stronger** than preserving the blocks of the
*merged* wall partition `A₀ = join (vp a) (vp b)` -- `contract_fix` is the
(easy) implication in the available direction -- because a relabelling of the
**incoming** datum needs the blocks of an endpoint partition preserved, and
`vp a` is strictly finer than `A₀` whenever the contracted occurrence's fibre
is not a single class.

`endsCompatible_of_fixLeft_of_rightFixed` reduces `EndsCompatible` to its `a`
half alone, on the geometric hypothesis that no wall occurrence over the `b` end
lies in the moved branch: in Figure 29 the moving direction `t_α` *is* the
divalent occurrence (`hMoving`), so the branches actually swapped -- those
through the retained `t_β`, `t_γ` -- attach at the trivalent endpoint, and
`TargetSeparation.edgeMoved_eq_false` puts `t_α` outside each of them.  The `a`
half is supplied by choosing the clearing permutation inside a block of the
*endpoint* partition, which `W3ShiftClosure.exists_branchSwapPerm_clearing_endpoint`
does, with `k_β < (data.vertexPartition a).blockCard anchor` in place of
`k_β < |A₀|`.
-/

namespace DraismaVargas.LocalCases.W3ShiftIncomingTransport

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open W4Assembly W4StableSource StableLocalProperties FullDimensionalSource
open ThirdEquation TargetExpansion
open W3FourDisjointness

noncomputable local instance {target : CFGraph} : DecidableEq target.edges :=
  Classical.decEq _

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

section Region

variable (hab : a ≠ b) (hOne : num_edges target a b = 1)
  (root : (contract target hab hOne).V) (hRoot : root ≠ ⟨a, hab⟩)

/-- The incoming-level branch region, pulled back along the contraction. -/
def movedVertex (v : target.V) : Bool :=
  TargetBranchRegion.vertexMoved (⟨a, hab⟩ : (contract target hab hOne).V) root hRoot
    (fold target hab v)

/-- An incoming target occurrence is moved when either endpoint is. -/
def movedEdge (f : target.edges) : Bool :=
  movedVertex hab hOne root hRoot (f : target.V × target.V).1 ||
    movedVertex hab hOne root hRoot (f : target.V × target.V).2

@[simp] theorem movedVertex_left : movedVertex hab hOne root hRoot a = false := by
  unfold movedVertex
  rw [fold_a]
  exact TargetBranchRegion.vertexMoved_wall _ _ _

@[simp] theorem movedVertex_right : movedVertex hab hOne root hRoot b = false := by
  unfold movedVertex
  rw [fold_self]
  exact TargetBranchRegion.vertexMoved_wall _ _ _

theorem fold_eq_wall_iff {v : target.V} (h : fold target hab v = ⟨a, hab⟩) :
    v = a ∨ v = b := by
  by_cases hv : v = b
  · exact Or.inr hv
  · rw [fold_of_ne target hab hv] at h
    exact Or.inl (congrArg Subtype.val h)

theorem movedEdge_contracted (hc : (contracted : target.V × target.V) = (a, b)) :
    movedEdge hab hOne root hRoot contracted = false := by
  unfold movedEdge
  rw [congrArg Prod.fst hc, congrArg Prod.snd hc, movedVertex_left, movedVertex_right]
  rfl

theorem movedEdge_unfoldEdge (hc : (contracted : target.V × target.V) = (a, b))
    (e : (contract target hab hOne).edges) :
    movedEdge hab hOne root hRoot (unfoldEdge hc hab hOne e) =
      TargetBranchRegion.edgeMoved (⟨a, hab⟩ : (contract target hab hOne).V) root hRoot e := by
  have h1 : fold target hab
      ((unfoldEdge hc hab hOne e : target.edges) : target.V × target.V).1 =
      ((e : (contract target hab hOne).edges) :
        (contract target hab hOne).V × (contract target hab hOne).V).1 :=
    congrArg Prod.fst (fold_unfoldEdge hc hab hOne e)
  have h2 : fold target hab
      ((unfoldEdge hc hab hOne e : target.edges) : target.V × target.V).2 =
      ((e : (contract target hab hOne).edges) :
        (contract target hab hOne).V × (contract target hab hOne).V).2 :=
    congrArg Prod.snd (fold_unfoldEdge hc hab hOne e)
  unfold movedEdge movedVertex
  rw [h1, h2]
  rfl


theorem boundary_left (hc : (contracted : target.V × target.V) = (a, b))
    (f : target.edges)
    (hDiff : movedEdge hab hOne root hRoot f ≠
      movedVertex hab hOne root hRoot (f : target.V × target.V).1) :
    (f : target.V × target.V).1 = a ∨ (f : target.V × target.V).1 = b := by
  by_cases hf : f = contracted
  · subst hf
    rw [movedEdge_contracted hab hOne root hRoot hc, congrArg Prod.fst hc,
      movedVertex_left] at hDiff
    exact absurd rfl hDiff
  · have hE : TargetBranchRegion.edgeMoved (⟨a, hab⟩ : (contract target hab hOne).V)
        root hRoot (foldEdge hc hab hOne ⟨f, hf⟩) ≠
        TargetBranchRegion.vertexMoved (⟨a, hab⟩ : (contract target hab hOne).V)
          root hRoot ((foldEdge hc hab hOne ⟨f, hf⟩ :
            (contract target hab hOne).edges) :
            (contract target hab hOne).V × (contract target hab hOne).V).1 := hDiff
    have hWall := TargetBranchRegion.boundary_left
      (⟨a, hab⟩ : (contract target hab hOne).V) root hRoot
      (foldEdge hc hab hOne ⟨f, hf⟩) hE
    rw [coe_foldEdge] at hWall
    exact fold_eq_wall_iff hab hWall

theorem boundary_right (hc : (contracted : target.V × target.V) = (a, b))
    (f : target.edges)
    (hDiff : movedEdge hab hOne root hRoot f ≠
      movedVertex hab hOne root hRoot (f : target.V × target.V).2) :
    (f : target.V × target.V).2 = a ∨ (f : target.V × target.V).2 = b := by
  by_cases hf : f = contracted
  · subst hf
    rw [movedEdge_contracted hab hOne root hRoot hc, congrArg Prod.snd hc,
      movedVertex_right] at hDiff
    exact absurd rfl hDiff
  · have hE : TargetBranchRegion.edgeMoved (⟨a, hab⟩ : (contract target hab hOne).V)
        root hRoot (foldEdge hc hab hOne ⟨f, hf⟩) ≠
        TargetBranchRegion.vertexMoved (⟨a, hab⟩ : (contract target hab hOne).V)
          root hRoot ((foldEdge hc hab hOne ⟨f, hf⟩ :
            (contract target hab hOne).edges) :
            (contract target hab hOne).V × (contract target hab hOne).V).2 := hDiff
    have hWall := TargetBranchRegion.boundary_right
      (⟨a, hab⟩ : (contract target hab hOne).V) root hRoot
      (foldEdge hc hab hOne ⟨f, hf⟩) hE
    rw [coe_foldEdge] at hWall
    exact fold_eq_wall_iff hab hWall

/-- **The endpoint compatibility the incoming-level swap needs.**  At each end
of the wall occurrence that the moved branch actually touches, the permutation
must preserve that end's own blocks.  Every selected/unselected incidence of the
pulled-back region sits at `a` or at `b` (`boundary_left`, `boundary_right`),
and this is exactly the hypothesis `GluingDatum.SheetRelabeling.ofRegion` asks
for there.

It is **strictly stronger** than the contracted-level hypothesis
`W3ShiftClosure.exists_branchSwapPerm_clearing` returns, which only preserves
the blocks of the *merged* partition `A₀ = join (vp a) (vp b)`. -/
def EndsCompatible (data : GluingDatum target degree)
    (permutation : Equiv.Perm (Fin degree)) : Prop :=
  ∀ v : target.V, (v = a ∨ v = b) →
    (∃ f : target.edges, movedEdge hab hOne root hRoot f = true ∧
      (((f : target.V × target.V).1 = v) ∨ ((f : target.V × target.V).2 = v))) →
    ∀ sheet, (data.vertexPartition v).Rel (permutation sheet) sheet

/-- Preserving both endpoint partitions is enough. -/
theorem endsCompatible_of_fix (data : GluingDatum target degree)
    (permutation : Equiv.Perm (Fin degree))
    (hFixLeft : ∀ sheet, (data.vertexPartition a).Rel (permutation sheet) sheet)
    (hFixRight : ∀ sheet, (data.vertexPartition b).Rel (permutation sheet) sheet) :
    EndsCompatible hab hOne root hRoot data permutation := by
  rintro v (rfl | rfl) - sheet
  · exact hFixLeft sheet
  · exact hFixRight sheet

/-- When the moved branch does not touch `b`, only `a`'s own partition is
constrained.  This is Figure 29's situation: the moving direction `t_α` is the
divalent occurrence (`hMoving`), so the two retained directions `t_β`, `t_γ`
whose branches are swapped sit at the *other* endpoint of the wall occurrence,
and the branch through either of them meets the wall edge only there. -/
theorem endsCompatible_of_fixLeft (data : GluingDatum target degree)
    (permutation : Equiv.Perm (Fin degree))
    (hFixLeft : ∀ sheet, (data.vertexPartition a).Rel (permutation sheet) sheet)
    (hAway : ∀ f : target.edges,
      (((f : target.V × target.V).1 = b) ∨ ((f : target.V × target.V).2 = b)) →
      movedEdge hab hOne root hRoot f = false) :
    EndsCompatible hab hOne root hRoot data permutation := by
  rintro v (rfl | rfl) hTouch sheet
  · exact hFixLeft sheet
  · obtain ⟨f, hMoved, hIncident⟩ := hTouch
    rw [hAway f hIncident] at hMoved
    exact absurd hMoved (by simp)

/-- The mirror, when the moved branch does not touch `a`. -/
theorem endsCompatible_of_fixRight (data : GluingDatum target degree)
    (permutation : Equiv.Perm (Fin degree))
    (hFixRight : ∀ sheet, (data.vertexPartition b).Rel (permutation sheet) sheet)
    (hAway : ∀ f : target.edges,
      (((f : target.V × target.V).1 = a) ∨ ((f : target.V × target.V).2 = a)) →
      movedEdge hab hOne root hRoot f = false) :
    EndsCompatible hab hOne root hRoot data permutation := by
  rintro v (rfl | rfl) hTouch sheet
  · obtain ⟨f, hMoved, hIncident⟩ := hTouch
    rw [hAway f hIncident] at hMoved
    exact absurd hMoved (by simp)
  · exact hFixRight sheet

/-- A boundary mismatch forces the occurrence into the moved region. -/
theorem movedEdge_eq_true_of_mismatch_left {f : target.edges}
    (hDiff : movedEdge hab hOne root hRoot f ≠
      movedVertex hab hOne root hRoot (f : target.V × target.V).1) :
    movedEdge hab hOne root hRoot f = true := by
  cases hE : movedEdge hab hOne root hRoot f
  · exact absurd (hE.trans (Bool.or_eq_false_iff.mp hE).1.symm) hDiff
  · rfl

theorem movedEdge_eq_true_of_mismatch_right {f : target.edges}
    (hDiff : movedEdge hab hOne root hRoot f ≠
      movedVertex hab hOne root hRoot (f : target.V × target.V).2) :
    movedEdge hab hOne root hRoot f = true := by
  cases hE : movedEdge hab hOne root hRoot f
  · exact absurd (hE.trans (Bool.or_eq_false_iff.mp hE).2.symm) hDiff
  · rfl

end Region

section Sides

variable (hab : a ≠ b) (hOne : num_edges target a b = 1)
  (root : (contract target hab hOne).V) (hRoot : root ≠ ⟨a, hab⟩)
  (hc : (contracted : target.V × target.V) = (a, b))

/-- A surviving incoming occurrence is moved exactly when its image is. -/
theorem movedEdge_foldEdge (f : {f : target.edges // f ≠ contracted}) :
    movedEdge hab hOne root hRoot f.1 =
      TargetBranchRegion.edgeMoved (⟨a, hab⟩ : (contract target hab hOne).V) root hRoot
        (foldEdge hc hab hOne f) := by
  have hStep := movedEdge_unfoldEdge hab hOne root hRoot hc (foldEdge hc hab hOne f)
  rwa [unfoldEdge_foldEdge] at hStep

/-- **The `b`-side hypothesis, read at the contracted level.**  If every wall
occurrence lying over the `b` end of the wall edge is outside the moved branch,
then the moved branch never touches `b`, and only `a`'s own partition is
constrained.  In Figure 29 the one such occurrence is the divalent one
`shift.movingTarget`, and `TargetSeparation.edgeMoved_eq_false` puts it outside
the branch through `t_β` (resp. `t_γ`). -/
theorem endsCompatible_of_fixLeft_of_rightFixed
    (data : GluingDatum target degree) (permutation : Equiv.Perm (Fin degree))
    (hFixLeft : ∀ sheet, (data.vertexPartition a).Rel (permutation sheet) sheet)
    (hRightFixed : ∀ e : (contract target hab hOne).edges,
      IncomingTargetExpansion.right hc hab hOne e = true →
      TargetBranchRegion.edgeMoved (⟨a, hab⟩ : (contract target hab hOne).V) root hRoot
        e = false) :
    EndsCompatible hab hOne root hRoot data permutation := by
  refine endsCompatible_of_fixLeft hab hOne root hRoot data permutation hFixLeft
    fun f hIncident ↦ ?_
  by_cases hf : f = contracted
  · subst hf
    exact movedEdge_contracted hab hOne root hRoot hc
  · rw [movedEdge_foldEdge hab hOne root hRoot hc ⟨f, hf⟩]
    refine hRightFixed (foldEdge hc hab hOne ⟨f, hf⟩) ?_
    show decide _ = true
    rw [decide_eq_true_eq, unfoldEdge_foldEdge]
    exact hIncident

end Sides

section Relabel

variable (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (root : (contract target hab hOne).V) (hRoot : root ≠ ⟨a, hab⟩)
  (permutation : Equiv.Perm (Fin degree))
  (hEnds : EndsCompatible hab hOne root hRoot data permutation)

/-- **The incoming-level branch swap.** -/
def branchRelabel : data.SheetRelabeling :=
  GluingDatum.SheetRelabeling.ofRegion (movedVertex hab hOne root hRoot)
    (movedEdge hab hOne root hRoot) permutation
    (fun f hDiff sheet ↦
      hEnds _ (boundary_left hab hOne root hRoot hc f hDiff)
        ⟨f, movedEdge_eq_true_of_mismatch_left hab hOne root hRoot hDiff, Or.inl rfl⟩ sheet)
    (fun f hDiff sheet ↦
      hEnds _ (boundary_right hab hOne root hRoot hc f hDiff)
        ⟨f, movedEdge_eq_true_of_mismatch_right hab hOne root hRoot hDiff, Or.inr rfl⟩ sheet)

/-- The relabelled incoming datum: the swapped incoming cover. -/
noncomputable def swappedDatum : GluingDatum target degree :=
  (branchRelabel data hc hab hOne root hRoot permutation hEnds).apply

theorem swappedDatum_vertexPartition (v : target.V) :
    (swappedDatum data hc hab hOne root hRoot permutation hEnds).vertexPartition
        v =
      (data.vertexPartition v).relabel
        (GluingDatum.SheetRelabeling.togglePermutation
          (movedVertex hab hOne root hRoot v) permutation) := rfl

theorem swappedDatum_edgePartition (f : target.edges) :
    (swappedDatum data hc hab hOne root hRoot permutation hEnds).edgePartition
        f =
      (data.edgePartition f).relabel
        (GluingDatum.SheetRelabeling.togglePermutation
          (movedEdge hab hOne root hRoot f) permutation) := rfl

@[simp] theorem swappedDatum_vertexPartition_left :
    (swappedDatum data hc hab hOne root hRoot permutation hEnds).vertexPartition
        a = data.vertexPartition a := by
  rw [swappedDatum_vertexPartition, movedVertex_left]
  cases hP : data.vertexPartition a
  rfl

@[simp] theorem swappedDatum_vertexPartition_right :
    (swappedDatum data hc hab hOne root hRoot permutation hEnds).vertexPartition
        b = data.vertexPartition b := by
  rw [swappedDatum_vertexPartition, movedVertex_right]
  cases hP : data.vertexPartition b
  rfl

@[simp] theorem swappedDatum_edgePartition_contracted :
    (swappedDatum data hc hab hOne root hRoot permutation hEnds).edgePartition
        contracted = data.edgePartition contracted := by
  rw [swappedDatum_edgePartition, movedEdge_contracted hab hOne root hRoot hc]
  cases hP : data.edgePartition contracted
  rfl

end Relabel

section Commutation

variable (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (root : (contract target hab hOne).V) (hRoot : root ≠ ⟨a, hab⟩)
  (permutation : Equiv.Perm (Fin degree))
  (hEnds : EndsCompatible hab hOne root hRoot data permutation)
  (hFixWall : ∀ sheet,
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
      (permutation sheet) sheet)

/-- Two gluing data over the same target and degree agree as soon as both
partition assignments do: the remaining three fields are propositions. -/
theorem gluingDatum_ext {first second : GluingDatum target degree}
    (hVertex : first.vertexPartition = second.vertexPartition)
    (hEdge : first.edgePartition = second.edgePartition) : first = second := by
  revert hVertex hEdge
  obtain ⟨-, vertexFirst, edgeFirst, -, -⟩ := first
  obtain ⟨-, vertexSecond, edgeSecond, -, -⟩ := second
  intro hVertex hEdge
  have hV : vertexFirst = vertexSecond := hVertex
  have hE : edgeFirst = edgeSecond := hEdge
  subst hV
  subst hE
  rfl

/-- A permutation preserving either endpoint partition preserves the
**contracted** wall's own blocks, because the endpoint partition refines the
merged one.  The converse fails, and that is the whole cost of the transport. -/
theorem contract_fix
    (hFixLeft : ∀ sheet, (data.vertexPartition a).Rel (permutation sheet) sheet)
    (sheet : Fin degree) :
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
      (permutation sheet) sheet := by
  rw [contractDatum_vertexPartition_merge]
  exact (vertexPartition_refines_mergedPartition data a b).rel (hFixLeft sheet)

/-- The vertex half of the commutation. -/
theorem contract_swappedDatum_vertexPartition (y : GraphContraction.Vertex target b) :
    (contractDatum
        (swappedDatum data hc hab hOne root hRoot permutation hEnds)
        hc hab hOne).vertexPartition y =
      (branchSwapOfPerm (contractDatum data hc hab hOne) ⟨a, hab⟩ root hRoot
        permutation
        hFixWall).apply.vertexPartition y := by
  have hRight : (branchSwapOfPerm (contractDatum data hc hab hOne) ⟨a, hab⟩ root hRoot
      permutation
      hFixWall).apply.vertexPartition y =
      ((contractDatum data hc hab hOne).vertexPartition y).relabel
        (GluingDatum.SheetRelabeling.togglePermutation
          (TargetBranchRegion.vertexMoved (⟨a, hab⟩ : (contract target hab hOne).V)
            root hRoot y) permutation) := rfl
  by_cases hy : (y : target.V) = a
  · have hyWall : y = (⟨a, hab⟩ : GraphContraction.Vertex target b) := Subtype.ext hy
    have hFalse : TargetBranchRegion.vertexMoved
        (⟨a, hab⟩ : (contract target hab hOne).V) root hRoot
        (⟨a, hab⟩ : (contract target hab hOne).V) = false :=
      TargetBranchRegion.vertexMoved_wall _ _ _
    have hLeft : (contractDatum
        (swappedDatum data hc hab hOne root hRoot permutation hEnds)
        hc hab hOne).vertexPartition ⟨a, hab⟩ = mergedPartition data a b := by
      rw [contractDatum_vertexPartition_merge]
      show SheetPartition.join
        ((swappedDatum data hc hab hOne root hRoot permutation hEnds).vertexPartition a)
        ((swappedDatum data hc hab hOne root hRoot permutation hEnds).vertexPartition b) = _
      rw [swappedDatum_vertexPartition_left, swappedDatum_vertexPartition_right]
      rfl
    rw [hRight, hyWall, hFalse, hLeft, contractDatum_vertexPartition_merge]
    cases hP : mergedPartition data a b
    rfl
  · rw [hRight]
    show contractVertexPartition
      (swappedDatum data hc hab hOne root hRoot permutation hEnds) a b y = _
    rw [contractVertexPartition_of_ne _ a b hy, swappedDatum_vertexPartition,
      contractDatum_vertexPartition, contractVertexPartition_of_ne data a b hy]
    congr 1
    show GluingDatum.SheetRelabeling.togglePermutation
      (TargetBranchRegion.vertexMoved (⟨a, hab⟩ : (contract target hab hOne).V) root hRoot
        (fold target hab (y : target.V))) permutation = _
    rw [fold_coe]

/-- The edge half of the commutation. -/
theorem contract_swappedDatum_edgePartition (e : (contract target hab hOne).edges) :
    (contractDatum
        (swappedDatum data hc hab hOne root hRoot permutation hEnds)
        hc hab hOne).edgePartition e =
      (branchSwapOfPerm (contractDatum data hc hab hOne) ⟨a, hab⟩ root hRoot
        permutation
        hFixWall).apply.edgePartition e := by
  show (swappedDatum data hc hab hOne root hRoot permutation hEnds).edgePartition
    (unfoldEdge hc hab hOne e) = _
  rw [swappedDatum_edgePartition, movedEdge_unfoldEdge hab hOne root hRoot hc e]
  rfl

/-- **The commutation.**  Swapping above a branch of the incoming target and
then contracting the wall occurrence is the *same gluing datum* as contracting
first and then swapping above the image branch.  The branch is rooted away from
the wall, and the contraction only merges `a` and `b`. -/
theorem contract_swappedDatum :
    contractDatum
        (swappedDatum data hc hab hOne root hRoot permutation hEnds)
        hc hab hOne =
      (branchSwapOfPerm (contractDatum data hc hab hOne) ⟨a, hab⟩ root hRoot
        permutation hFixWall).apply :=
  gluingDatum_ext
    (funext (contract_swappedDatum_vertexPartition data hc hab hOne root hRoot
      permutation hEnds hFixWall))
    (funext (contract_swappedDatum_edgePartition data hc hab hOne root hRoot
      permutation hEnds hFixWall))

end Commutation



section Transport

variable (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (root : (contract target hab hOne).V) (hRoot : root ≠ ⟨a, hab⟩)
  (permutation : Equiv.Perm (Fin degree))
  (hEnds : EndsCompatible hab hOne root hRoot data permutation)

/-- The merged wall partition is literally unchanged. -/
theorem swappedDatum_mergedPartition :
    mergedPartition
        (swappedDatum data hc hab hOne root hRoot permutation hEnds) a b =
      mergedPartition data a b := by
  show SheetPartition.join
    ((swappedDatum data hc hab hOne root hRoot permutation hEnds).vertexPartition a)
    ((swappedDatum data hc hab hOne root hRoot permutation hEnds).vertexPartition b) = _
  rw [swappedDatum_vertexPartition_left, swappedDatum_vertexPartition_right]
  rfl

/-- The contraction receipt survives the swap: all four partitions it mentions
are literally unchanged. -/
theorem contractionForest_swappedDatum
    (hForest : ContractionForest data a b contracted) :
    ContractionForest
      (swappedDatum data hc hab hOne root hRoot permutation hEnds)
      a b contracted := by
  unfold ContractionForest
  rw [swappedDatum_mergedPartition, swappedDatum_edgePartition_contracted,
    swappedDatum_vertexPartition_left, swappedDatum_vertexPartition_right]
  exact hForest

/-- **The divalent wall occurrence does not depend on the cover.**  Its
characterisation is a condition on the target alone, and it is unique. -/
theorem divalentOccurrence_congr {coordinateFirst coordinateSecond : Type*}
    [Fintype coordinateFirst] [DecidableEq coordinateFirst]
    [Fintype coordinateSecond] [DecidableEq coordinateSecond]
    (first second : GluingDatum target degree)
    (fullDimFirst : FullDimensionalSourcePresentation first coordinateFirst)
    (fullDimSecond : FullDimensionalSourcePresentation second coordinateSecond)
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩) :
    W3Nd2IncomingTargetPlacement.divalentOccurrence second hc hab hOne fullDimSecond
        star =
      W3Nd2IncomingTargetPlacement.divalentOccurrence first hc hab hOne fullDimFirst
        star :=
  W3Nd2IncomingTargetPlacement.divalentOccurrence_unique first hc hab hOne fullDimFirst
    star _
    (W3Nd2IncomingTargetPlacement.divalentOccurrence_spec second hc hab hOne
      fullDimSecond star)

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The swapped incoming cover's full-dimensional presentation**, in the
incoming cover's own coordinates. -/
noncomputable def swappedFullDim
    (fullDim : FullDimensionalSourcePresentation data coordinate) :
    FullDimensionalSourcePresentation
      (swappedDatum data hc hab hOne root hRoot permutation hEnds)
      coordinate :=
  RelabelFullDimensional.sheetPresentation
    (branchRelabel data hc hab hOne root hRoot permutation hEnds) fullDim

/-- Its length matrix is **literally** the incoming cover's. -/
theorem swappedFullDim_matrix
    (fullDim : FullDimensionalSourcePresentation data coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (swappedFullDim data hc hab hOne root hRoot permutation hEnds
          fullDim).labelling.presentation =
      GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation :=
  RelabelFullDimensional.sheet_matrix_eq _ fullDim.valid.1 fullDim.labelling

/-- And its column labelling is the incoming cover's, as a term. -/
theorem swappedFullDim_targetEdge
    (fullDim : FullDimensionalSourcePresentation data coordinate) :
    (swappedFullDim data hc hab hOne root hRoot permutation hEnds
        fullDim).labelling.targetEdge = fullDim.labelling.targetEdge := rfl

/-- The stable-incidence dictionary between the incoming cover and its swap. -/
noncomputable def swappedIncidence
    (fullDim : FullDimensionalSourcePresentation data coordinate) :
    StableGraphIncidence.Equivalence data
      (swappedDatum data hc hab hOne root hRoot permutation hEnds) :=
  StableGraphIncidence.sheetRelabel
    (branchRelabel data hc hab hOne root hRoot permutation hEnds)
    fullDim.valid.1

end Transport

section WallDatum

variable (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (root : (contract target hab hOne).V) (hRoot : root ≠ ⟨a, hab⟩)
  (permutation : Equiv.Perm (Fin degree))
  (hEnds : EndsCompatible hab hOne root hRoot data permutation)
  (hFixWall : ∀ sheet,
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
      (permutation sheet) sheet)

include hFixWall

/-- `A₀` is the same partition on the contracted copy, as a term. -/
theorem contract_swappedDatum_vertexPartition_wall :
    (contractDatum
        (swappedDatum data hc hab hOne root hRoot permutation hEnds)
        hc hab hOne).vertexPartition ⟨a, hab⟩ =
      (contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩ := by
  rw [contract_swappedDatum data hc hab hOne root hRoot permutation hEnds hFixWall]
  exact branchSwapOfPerm_vertexPartition_wall _ _ _ _ _ _

/-- Validity of the wall datum survives. -/
theorem contract_swappedDatum_valid
    (hValid : (contractDatum data hc hab hOne).Valid) :
    (contractDatum
      (swappedDatum data hc hab hOne root hRoot permutation hEnds)
      hc hab hOne).Valid := by
  rw [contract_swappedDatum data hc hab hOne root hRoot permutation hEnds hFixWall]
  exact GluingDatum.SheetRelabeling.valid _ hValid

/-- Every target occurrence outside the moved branch keeps its partition on the
contracted copy. -/
theorem contract_swappedDatum_edgePartition_of_fixed
    (e : (contract target hab hOne).edges)
    (hFixed : TargetBranchRegion.edgeMoved
      (⟨a, hab⟩ : (contract target hab hOne).V) root hRoot e = false) :
    (contractDatum
        (swappedDatum data hc hab hOne root hRoot permutation hEnds)
        hc hab hOne).edgePartition e =
      (contractDatum data hc hab hOne).edgePartition e := by
  rw [contract_swappedDatum data hc hab hOne root hRoot permutation hEnds hFixWall]
  exact branchSwapOfPerm_edgePartition_of_fixed _ _ _ _ _ _ e hFixed

end WallDatum

section Census

open W3ShiftIncomingMatching (SelectedCensus)

variable (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (root : (contract target hab hOne).V) (hRoot : root ≠ ⟨a, hab⟩)
  (permutation : Equiv.Perm (Fin degree))
  (hEnds : EndsCompatible hab hOne root hRoot data permutation)

/-- **The selected-block census is blind to the branch swap.**  Every partition
`W3ShiftIncomingMatching.SelectedCensus` mentions -- the two endpoint
partitions, the contracted occurrence's partition and the merged wall partition
-- is literally unchanged, so the selected-block census is stated over the
swapped incoming cover by exactly the same three sheet partitions. -/
theorem selectedCensus_swappedDatum
    (star : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (inputOld : W3SourceInput (contractDatum data hc hab hOne) star)
    (inputNew : W3SourceInput (contractDatum
      (swappedDatum data hc hab hOne root hRoot permutation hEnds)
      hc hab hOne) star)
    (hBlock : inputNew.distinguishedBlock.1 = inputOld.distinguishedBlock.1)
    (selectedLeft selectedRight selectedNew : SheetPartition degree)
    (hCensus : SelectedCensus data hc hab hOne star inputOld selectedLeft selectedRight
      selectedNew) :
    SelectedCensus
      (swappedDatum data hc hab hOne root hRoot permutation hEnds)
      hc hab hOne star inputNew selectedLeft selectedRight selectedNew := by
  constructor
  · intro hDivalent
    obtain ⟨hLeft, hRight, hNew⟩ := hCensus.divalentLeft hDivalent
    refine ⟨fun sheet hRel ↦ ?_, fun sheet hRel ↦ ?_, fun sheet hRel ↦ ?_⟩ <;>
      rw [swappedDatum_mergedPartition, hBlock] at hRel
    · rw [swappedDatum_vertexPartition_left]
      exact hLeft sheet hRel
    · rw [swappedDatum_vertexPartition_right]
      exact hRight sheet hRel
    · rw [swappedDatum_edgePartition_contracted]
      exact hNew sheet hRel
  · intro hDivalent
    obtain ⟨hLeft, hRight, hNew⟩ := hCensus.divalentRight hDivalent
    refine ⟨fun sheet hRel ↦ ?_, fun sheet hRel ↦ ?_, fun sheet hRel ↦ ?_⟩ <;>
      rw [swappedDatum_mergedPartition, hBlock] at hRel
    · rw [swappedDatum_vertexPartition_right]
      exact hLeft sheet hRel
    · rw [swappedDatum_vertexPartition_left]
      exact hRight sheet hRel
    · rw [swappedDatum_edgePartition_contracted]
      exact hNew sheet hRel

end Census

end DraismaVargas.LocalCases.W3ShiftIncomingTransport
