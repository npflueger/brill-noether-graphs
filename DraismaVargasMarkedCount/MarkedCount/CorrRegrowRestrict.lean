module

public import DraismaVargasMarkedCount.MarkedCount.CorrRestrictRegrow

@[expose] public section

/-!
# The lollipop correspondence, part 2: regrowth after restriction

For a frame `f` over the lollipop core, the regrowth of its restriction is isomorphic to `f` over
the lollipop core.

**The isomorphism** (`regrowRestrictIso`). On the target it sends the old vertices and edges of the
restriction to themselves (`vIncl`, `edgeIncl`), and the branch `(t_b, u', t_l, v_C)` of regrowth to
the branch `(tb, uP, tl, vC)` of `f` found by restriction. On sheets it is the identity over the old
part. Over the branch of mark `j` the four partitions of `f` are the partition `{P_f} ∪ singletons`,
`P_f = {r, s}` the sheets of `e_b` (by the bridge-and-loop lemma), over `tb`, `uP` and `vC`
(`sameBlocks_uP`, `sameBlocks_tb`, `sameBlocks_vC`), and discrete over `tl` (`tl_discrete`); but
each of the first three may name its block by `r` or by `s`. Regrowth used `pair a b` (`a` the sheet
of the mark, `b` a chosen second sheet of its block `S`). So the sheet permutation over each piece
is `pairPerm a b r s` (moving `a ↦ r`, `b ↦ s` by two transpositions inside `S`), preceded by
`swap a b` when that piece names its block by `s` (`adjPerm`). All of them move sheets only inside
`S`, and two of them differ by at most `swap a b`, which is what compatibility needs (`rel_adjPerm`,
`pair_rel_adjPerm`).

This is the independence of `P` in the form the inverse law needs: the regrowth's second sheet `b`
need not be a sheet of `e_b`, and `a` need not be one either. The isomorphism `Regrow.regrowIso`
with `ι = refl` would not do here, since it only changes `b` and keeps the representative `a`, while
`f` may name `P_f` by any of its sheets.
-/

namespace DraismaVargas.Count.MarkedCount.CorrRegrowRestrict

noncomputable section

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count (GeometricDatumIso UnorderedEnds)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.GeometricSegmentWalls (FrameIso)
open DraismaVargas.Count.MarkedCount.Restrict
open DraismaVargas.Count.MarkedCount.Regrow
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open GenusSixExistence.Tripod.Gluing (SheetOps.pair)
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 1.  Sheet partitions -/

section Sheets

variable {d : ℕ}

/-- A refinement with as many blocks as the coarse partition has the same blocks. -/
theorem sameBlocks_of_refines_of_card {fine coarse : SheetPartition d} (h : fine.Refines coarse)
    (hCard : Fintype.card fine.Blocks = Fintype.card coarse.Blocks) : fine.SameBlocks coarse := by
  let g : fine.Blocks → coarse.Blocks := fun b ↦ coarse.toBlock b.1
  have hSurj : Function.Surjective g := by
    intro c
    refine ⟨fine.toBlock c.1, Subtype.ext ?_⟩
    change coarse.repr (fine.repr c.1) = c.1
    have hc : coarse.repr (fine.repr c.1) = coarse.repr c.1 := h.rel (fine.rel_repr_left c.1)
    exact hc.trans c.2
  have hInj : Function.Injective g :=
    ((Fintype.bijective_iff_surjective_and_card g).mpr ⟨hSurj, hCard⟩).1
  intro i j
  refine ⟨fun hij ↦ h.rel hij, fun hij ↦ ?_⟩
  have hg : g (fine.toBlock i) = g (fine.toBlock j) := by
    apply Subtype.ext
    change coarse.repr (fine.repr i) = coarse.repr (fine.repr j)
    have hi : coarse.repr (fine.repr i) = coarse.repr i := h.rel (fine.rel_repr_left i)
    have hj : coarse.repr (fine.repr j) = coarse.repr j := h.rel (fine.rel_repr_left j)
    have hij' : coarse.repr i = coarse.repr j := hij
    exact hi.trans (hij'.trans hj.symm)
  exact congrArg Subtype.val (hInj hg)

theorem eq_pair_of_sameBlocks {Q : SheetPartition d} {r s : Fin d} (hrs : r ≠ s)
    (hQ : Q.SameBlocks (SheetOps.pair r s)) (hr : Q.repr r = r) : Q = SheetOps.pair r s := by
  apply SheetPartition.ext_repr
  funext i
  rw [pair_repr]
  by_cases hi : i = s
  · subst hi
    rw [ite_eq_left rfl]
    have h : Q.repr r = Q.repr i := (hQ r i).mpr (pair_rel_self r i)
    exact h.symm.trans hr
  · rw [ite_eq_right hi]
    have h := (hQ (Q.repr i) i).mp (Q.rel_repr_left i)
    rw [pair_rel_iff hrs] at h
    rcases h with h | ⟨-, h | h⟩
    · exact h
    · subst h; exact hr
    · exact absurd h hi

theorem pair_sameBlocks_swap {r s : Fin d} (hrs : r ≠ s) :
    (SheetOps.pair s r).SameBlocks (SheetOps.pair r s) := by
  intro i j
  rw [pair_rel_iff hrs.symm, pair_rel_iff hrs]
  tauto

theorem eq_discrete_of_card {Q : SheetPartition d} (h : Fintype.card Q.Blocks = d) :
    Q = SheetPartition.discrete d := by
  apply SheetPartition.ext_repr
  funext i
  change Q.repr i = i
  by_contra hi
  have hlt := Fintype.card_subtype_lt (p := fun i ↦ Q.repr i = i) hi
  have hEq : Fintype.card {i // Q.repr i = i} = Fintype.card Q.Blocks := rfl
  rw [hEq, h, Fintype.card_fin] at hlt
  exact lt_irrefl _ hlt

/-- Two transpositions moving `a ↦ r` and `b ↦ s`. -/
def pairPerm (a b r s : Fin d) : Equiv.Perm (Fin d) :=
  (Equiv.swap a r).trans (Equiv.swap (Equiv.swap a r b) s)

theorem pairPerm_a {a b r s : Fin d} (hab : a ≠ b) (hrs : r ≠ s) : pairPerm a b r s a = r := by
  unfold pairPerm
  rw [Equiv.trans_apply, Equiv.swap_apply_left]
  refine Equiv.swap_apply_of_ne_of_ne ?_ hrs
  intro h
  apply hab
  have h' := congrArg (Equiv.swap a r) h
  rwa [Equiv.swap_apply_right, Equiv.swap_apply_self] at h'

theorem pairPerm_b (a b r s : Fin d) : pairPerm a b r s b = s := by
  unfold pairPerm
  rw [Equiv.trans_apply, Equiv.swap_apply_left]

theorem rel_pairPerm (Q : SheetPartition d) {a b r s : Fin d} (hb : Q.Rel a b) (hr : Q.Rel a r)
    (hs : Q.Rel a s) (i : Fin d) : Q.Rel (pairPerm a b r s i) i := by
  have hc : Q.Rel (Equiv.swap a r b) b := Q.swap_apply_rel_self_of_rel hr b
  have hcs : Q.Rel (Equiv.swap a r b) s := by
    have hc' : Q.repr (Equiv.swap a r b) = Q.repr b := hc
    have hb' : Q.repr a = Q.repr b := hb
    have hs' : Q.repr a = Q.repr s := hs
    exact hc'.trans (hb'.symm.trans hs')
  have h1 := Q.swap_apply_rel_self_of_rel hr i
  have h2 := Q.swap_apply_rel_self_of_rel hcs (Equiv.swap a r i)
  unfold pairPerm
  rw [Equiv.trans_apply]
  have h1' : Q.repr (Equiv.swap a r i) = Q.repr i := h1
  have h2' : Q.repr (Equiv.swap (Equiv.swap a r b) s (Equiv.swap a r i)) =
      Q.repr (Equiv.swap a r i) := h2
  exact h2'.trans h1'

/-- `pairPerm`, preceded by `swap a b` when `Q` names the block `{r, s}` by `s`. -/
def adjPerm (Q : SheetPartition d) (a b r s : Fin d) : Equiv.Perm (Fin d) :=
  (if Q.repr r = r then Equiv.refl _ else Equiv.swap a b).trans (pairPerm a b r s)

variable {Q : SheetPartition d} {a b r s : Fin d}

theorem repr_cases (hrs : r ≠ s) (hQ : Q.SameBlocks (SheetOps.pair r s)) :
    Q.repr r = r ∨ (Q.repr r = s ∧ Q.repr s = s) := by
  have h := (hQ (Q.repr r) r).mp (Q.rel_repr_left r)
  rw [pair_rel_iff hrs] at h
  rcases h with h | ⟨h | h, -⟩
  · exact Or.inl h
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    have := Q.repr_idem r
    rw [h] at this
    exact this

theorem adjPerm_relabel (hab : a ≠ b) (hrs : r ≠ s) (hQ : Q.SameBlocks (SheetOps.pair r s)) :
    Q = (SheetOps.pair a b).relabel (adjPerm Q a b r s) := by
  rw [pair_relabel]
  rcases repr_cases hrs hQ with h | ⟨h, hs⟩
  · have ha : adjPerm Q a b r s a = r := by
      simp only [adjPerm, ite_eq_left h, Equiv.trans_apply, Equiv.refl_apply]
      exact pairPerm_a hab hrs
    have hb : adjPerm Q a b r s b = s := by
      simp only [adjPerm, ite_eq_left h, Equiv.trans_apply, Equiv.refl_apply]
      exact pairPerm_b a b r s
    rw [ha, hb]
    exact eq_pair_of_sameBlocks hrs hQ h
  · have hne : Q.repr r ≠ r := by rw [h]; exact hrs.symm
    have ha : adjPerm Q a b r s a = s := by
      simp only [adjPerm, ite_eq_right hne, Equiv.trans_apply, Equiv.swap_apply_left]
      exact pairPerm_b a b r s
    have hb : adjPerm Q a b r s b = r := by
      simp only [adjPerm, ite_eq_right hne, Equiv.trans_apply, Equiv.swap_apply_right]
      exact pairPerm_a hab hrs
    rw [ha, hb]
    exact eq_pair_of_sameBlocks hrs.symm (fun i j ↦ (hQ i j).trans
      ((pair_sameBlocks_swap hrs) i j).symm) hs

theorem adjPerm_a (hab : a ≠ b) (hrs : r ≠ s) (hQ : Q.SameBlocks (SheetOps.pair r s)) :
    adjPerm Q a b r s a = Q.repr r := by
  rcases repr_cases hrs hQ with h | ⟨h, -⟩
  · simp only [adjPerm, ite_eq_left h, Equiv.trans_apply, Equiv.refl_apply]
    rw [h]
    exact pairPerm_a hab hrs
  · have hne : Q.repr r ≠ r := by rw [h]; exact hrs.symm
    simp only [adjPerm, ite_eq_right hne, Equiv.trans_apply, Equiv.swap_apply_left]
    rw [h]
    exact pairPerm_b a b r s

theorem rel_adjPerm (Qx : SheetPartition d) (hb : Qx.Rel a b) (hr : Qx.Rel a r)
    (hs : Qx.Rel a s) (i : Fin d) : Qx.Rel (adjPerm Q a b r s i) i := by
  have hτ : Qx.Rel ((if Q.repr r = r then Equiv.refl _ else Equiv.swap a b) i) i := by
    split_ifs
    · rfl
    · exact Qx.swap_apply_rel_self_of_rel hb i
  have h1 := rel_pairPerm Qx hb hr hs ((if Q.repr r = r then Equiv.refl _ else Equiv.swap a b) i)
  have h1' : Qx.repr (pairPerm a b r s
      ((if Q.repr r = r then Equiv.refl _ else Equiv.swap a b) i)) =
      Qx.repr ((if Q.repr r = r then Equiv.refl _ else Equiv.swap a b) i) := h1
  have hτ' : Qx.repr ((if Q.repr r = r then Equiv.refl _ else Equiv.swap a b) i) = Qx.repr i := hτ
  exact h1'.trans hτ'

theorem pair_rel_adjPerm (Q' : SheetPartition d) (i : Fin d) :
    (SheetOps.pair a b).Rel ((adjPerm Q a b r s).symm (adjPerm Q' a b r s i)) i := by
  have hab : (SheetOps.pair a b).Rel a b := pair_rel_self a b
  unfold adjPerm
  rw [Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
  split_ifs
  · rfl
  · exact (SheetOps.pair a b).swap_apply_rel_self_of_rel hab i
  · rw [Equiv.symm_swap, Equiv.refl_apply]
    exact (SheetOps.pair a b).swap_apply_rel_self_of_rel hab i
  · rw [Equiv.symm_swap, Equiv.swap_apply_self]
    rfl

end Sheets

/-! ## 2.  The branch of a lollipop frame, sheet by sheet -/

section Branch

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n}
  (hc : IsMarkedCubic core mark) (f : Frame (attachLollipops core mark) degree)

/-- The member at the zero request, on which the restriction modules work. -/
abbrev mem : FibreMember (attachLollipops core mark) 0 degree := f.member 0

/-- The restriction. -/
abbrev κ : MarkedFrame core mark degree := restrictFrame hc f

/-- The branching of the restriction (its marks and chosen second sheets). -/
abbrev β : Branching (κ hc f).data k := branching (κ hc f)

variable (j : Fin k)

/-- The partition at `φ(w_j)`. -/
abbrev Qu : SheetPartition degree := f.data.vertexPartition (Lollipops.uP (mem f) j)
/-- The partition over `φ(e_b)`. -/
abbrev Qb : SheetPartition degree := f.data.edgePartition (Lollipops.tb (mem f) j)
/-- The partition at `φ(C_j)`. -/
abbrev Qc : SheetPartition degree := f.data.vertexPartition (Lollipops.vC (mem f) j)
/-- The partition at `φ(u_j)`. -/
abbrev Qx : SheetPartition degree := f.data.vertexPartition (Lollipops.xV (mem f) j)

/-- The sheet of `w_j`. -/
abbrev rr : Fin degree := (Lollipops.loopV (mem f) j).1.2

theorem Qu_repr_rr : (Qu f j).repr (rr f j) = rr f j := (Lollipops.loopV (mem f) j).2

theorem one_lt_blockCard_rr : 1 < (Qu f j).blockCard (rr f j) := by
  have h := LollipopBridgeFibreWitness.blockCard_loopBranch (mem f) (Lollipops.hLoop j)
  change (Qu f j).blockCard (rr f j) = 2 at h
  omega

/-- The second sheet of `w_j`'s block. -/
def ss : Fin degree :=
  ((Qu f j).exists_other_of_one_lt_blockCard _ (one_lt_blockCard_rr f j)).choose

theorem rel_rr_ss : (Qu f j).Rel (rr f j) (ss f j) :=
  ((Qu f j).exists_other_of_one_lt_blockCard _ (one_lt_blockCard_rr f j)).choose_spec.1

theorem rr_ne_ss : rr f j ≠ ss f j :=
  ((Qu f j).exists_other_of_one_lt_blockCard _ (one_lt_blockCard_rr f j)).choose_spec.2

theorem sameBlocks_uP : (Qu f j).SameBlocks (SheetOps.pair (rr f j) (ss f j)) := by
  refine (sameBlocks_of_refines_of_card (pair_refines (rel_rr_ss f j)) ?_).symm
  have h1 := card_blocks_pair (rr_ne_ss f j)
  have h2 := Lollipops.card_blocks_uP (mem f) j
  change Fintype.card (Qu f j).Blocks + 1 = degree at h2
  omega

theorem sameBlocks_tb_uP : (Qb f j).SameBlocks (Qu f j) := by
  refine sameBlocks_of_refines_of_card
    (StableLocalProperties.refines_of_mem_incidentEdges (mem f).data
      (Lollipops.tb_mem_uP (mem f) j)) ?_
  have h1 := Lollipops.card_blocks_tb (mem f) j
  have h2 := Lollipops.card_blocks_uP (mem f) j
  change Fintype.card (Qb f j).Blocks + 1 = degree at h1
  change Fintype.card (Qu f j).Blocks + 1 = degree at h2
  omega

theorem sameBlocks_tb : (Qb f j).SameBlocks (SheetOps.pair (rr f j) (ss f j)) :=
  (sameBlocks_tb_uP f j).trans (sameBlocks_uP f j)

theorem sameBlocks_vC : (Qc f j).SameBlocks (SheetOps.pair (rr f j) (ss f j)) := by
  refine (sameBlocks_of_refines_of_card (Lollipops.refines_vC_uP (mem f) j) ?_).trans
    (sameBlocks_uP f j)
  have h1 := Lollipops.card_blocks_vC (mem f) j
  have h2 := Lollipops.card_blocks_uP (mem f) j
  change Fintype.card (Qc f j).Blocks + 1 = degree at h1
  change Fintype.card (Qu f j).Blocks + 1 = degree at h2
  change Fintype.card (Qc f j).Blocks = Fintype.card (Qu f j).Blocks
  omega

theorem tl_discrete :
    f.data.edgePartition (Lollipops.tl (mem f) j) = SheetPartition.discrete degree :=
  eq_discrete_of_card (Lollipops.card_blocks_tl (mem f) j)

/-- The sheet of the mark. -/
abbrev aa : Fin degree := (β hc f).a j
/-- The chosen second sheet of the mark's block. -/
abbrev bb : Fin degree := (β hc f).other j

theorem aa_ne_bb : aa hc f j ≠ bb hc f j := (β hc f).a_ne j

theorem Qx_rel_bb : (Qx f j).Rel (aa hc f j) (bb hc f j) := (β hc f).rel_a j

theorem Qu_rel_bridge :
    (Qu f j).Rel (rr f j) (Lollipops.bridgeE (mem f) j).1.2 :=
  ((incident_iff_target_mem_and_rel (mem f).data _ _).mp
    (Lollipops.bridgeE_incident_loopV (mem f) j)).2

theorem Qx_rel_rr : (Qx f j).Rel (aa hc f j) (rr f j) := by
  have hu : (Qx f j).repr (aa hc f j) = (Qx f j).repr (Lollipops.bridgeE (mem f) j).1.2 :=
    ((incident_iff_target_mem_and_rel (mem f).data _ _).mp
      (Lollipops.bridgeE_incident_markV (mem f) j)).2
  have hw : (Qx f j).repr (rr f j) = (Qx f j).repr (Lollipops.bridgeE (mem f) j).1.2 :=
    (Lollipops.refines_uP_xV (mem f) j).rel (Qu_rel_bridge f j)
  exact hu.trans hw.symm

theorem Qx_rel_ss : (Qx f j).Rel (aa hc f j) (ss f j) := by
  have h1 : (Qx f j).repr (aa hc f j) = (Qx f j).repr (rr f j) := Qx_rel_rr hc f j
  have h2 : (Qx f j).repr (rr f j) = (Qx f j).repr (ss f j) :=
    (Lollipops.refines_uP_xV (mem f) j).rel (rel_rr_ss f j)
  exact h1.trans h2

/-- The sheet permutation at `u'_j` (and over `t_l`). -/
abbrev πu : Equiv.Perm (Fin degree) := adjPerm (Qu f j) (aa hc f j) (bb hc f j) (rr f j) (ss f j)
/-- The sheet permutation over `t_b`. -/
abbrev πb : Equiv.Perm (Fin degree) := adjPerm (Qb f j) (aa hc f j) (bb hc f j) (rr f j) (ss f j)
/-- The sheet permutation at `v_{C,j}`. -/
abbrev πc : Equiv.Perm (Fin degree) := adjPerm (Qc f j) (aa hc f j) (bb hc f j) (rr f j) (ss f j)

theorem πu_a : πu hc f j (aa hc f j) = rr f j :=
  (adjPerm_a (aa_ne_bb hc f j) (rr_ne_ss f j) (sameBlocks_uP f j)).trans (Qu_repr_rr f j)

theorem πb_a : πb hc f j (aa hc f j) = (Lollipops.bridgeE (mem f) j).1.2 := by
  refine (adjPerm_a (aa_ne_bb hc f j) (rr_ne_ss f j) (sameBlocks_tb f j)).trans ?_
  have h : (Qb f j).Rel (rr f j) (Lollipops.bridgeE (mem f) j).1.2 :=
    ((sameBlocks_tb_uP f j) _ _).mpr (Qu_rel_bridge f j)
  exact h.trans (Lollipops.bridgeE (mem f) j).2

theorem rel_π (Q : SheetPartition degree) (i : Fin degree) :
    (Qx f j).Rel (adjPerm Q (aa hc f j) (bb hc f j) (rr f j) (ss f j) i) i :=
  rel_adjPerm (Qx f j) (Qx_rel_bb hc f j) (Qx_rel_rr hc f j) (Qx_rel_ss hc f j) i

end Branch

/-! ## 3.  The target dictionary -/

section Target

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n}
  (hc : IsMarkedCubic core mark) (f : Frame (attachLollipops core mark) degree)

/-- The regrown target. -/
abbrev RT : CFGraph.{0} := regrowTarget (κ hc f).target (β hc f).x

/-- The target vertex map: old vertices to themselves, the branch to the branch. -/
def tvFun : (RT hc f).V → f.target.V :=
  Sum.elim (fun v : (Lollipops.rTarget (mem f)).V ↦ vIncl v)
    (Sum.elim (Lollipops.uP (mem f)) (Lollipops.vC (mem f)))

theorem tvFun_bijective : Function.Bijective (tvFun hc f) := by
  have hK := Lollipops.Keep_nonempty (mem f)
  constructor
  · intro x y h
    rcases x with v | j | j <;> rcases y with v' | j' | j'
    · exact congrArg Sum.inl (vIncl_injective (hKeep := hK) h)
    · exact (Lollipops.uP_notMem_Keep (mem f) j'
        ((congrArg (· ∈ Lollipops.Keep (mem f)) h).mp (vIncl_mem (hKeep := hK) v))).elim
    · exact (Lollipops.vC_notMem_Keep (mem f) j'
        ((congrArg (· ∈ Lollipops.Keep (mem f)) h).mp (vIncl_mem (hKeep := hK) v))).elim
    · exact (Lollipops.uP_notMem_Keep (mem f) j
        ((congrArg (· ∈ Lollipops.Keep (mem f)) h).mpr (vIncl_mem (hKeep := hK) v'))).elim
    · have h' : Lollipops.uP (mem f) j = Lollipops.uP (mem f) j' := h
      rw [Lollipops.uP_injective (mem f) h']
    · exact absurd h (Lollipops.uP_ne_vC (mem f) j j')
    · exact (Lollipops.vC_notMem_Keep (mem f) j
        ((congrArg (· ∈ Lollipops.Keep (mem f)) h).mpr (vIncl_mem (hKeep := hK) v'))).elim
    · exact absurd h.symm (Lollipops.uP_ne_vC (mem f) j' j)
    · have h' : Lollipops.vC (mem f) j = Lollipops.vC (mem f) j' := h
      rw [Lollipops.vC_injective (mem f) h']
  · intro v
    by_cases hv : v ∈ Lollipops.Keep (mem f)
    · exact ⟨Sum.inl (vRestrict (hKeep := hK) v hv), rfl⟩
    · obtain ⟨j, hj | hj⟩ := Lollipops.exists_branch_of_notMem_Keep (mem f) hv
      · exact ⟨Sum.inr (Sum.inl j), hj⟩
      · exact ⟨Sum.inr (Sum.inr j), hj⟩

/-- **The target vertex dictionary.** -/
def tv : (RT hc f).V ≃ f.target.V := Equiv.ofBijective _ (tvFun_bijective hc f)

@[simp] theorem tv_oldV (v : (κ hc f).target.V) :
    tv hc f (oldV (β hc f).x v) = vIncl (Keep := Lollipops.Keep (mem f))
      (hKeep := Lollipops.Keep_nonempty (mem f)) v := rfl
@[simp] theorem tv_midV (j : Fin k) : tv hc f (midV (β hc f).x j) = Lollipops.uP (mem f) j := rfl
@[simp] theorem tv_tipV (j : Fin k) : tv hc f (tipV (β hc f).x j) = Lollipops.vC (mem f) j := rfl

/-- The occurrence map: old edges to themselves, the branch to the branch. -/
def teFun : Occ (κ hc f).target k → f.target.edges
  | .inl (.inl j) => Lollipops.tb (mem f) j
  | .inl (.inr j) => Lollipops.tl (mem f) j
  | .inr e => edgeIncl (Keep := Lollipops.Keep (mem f)) (hKeep := Lollipops.Keep_nonempty (mem f)) e

theorem not_keptEdge_tb (j : Fin k) :
    ¬ KeptEdge (Lollipops.Keep (mem f)) (Lollipops.tb (mem f) j) :=
  (Lollipops.not_keptEdge_iff (mem f) _).mpr (Or.inl ⟨j, rfl⟩)

theorem not_keptEdge_tl (j : Fin k) :
    ¬ KeptEdge (Lollipops.Keep (mem f)) (Lollipops.tl (mem f) j) :=
  (Lollipops.not_keptEdge_iff (mem f) _).mpr (Or.inr ⟨j, rfl⟩)

theorem teFun_bijective : Function.Bijective (teFun hc f) := by
  have hK := Lollipops.Keep_nonempty (mem f)
  constructor
  · intro x y h
    rcases x with (j | j) | e <;> rcases y with (j' | j') | e'
    · have h' : Lollipops.tb (mem f) j = Lollipops.tb (mem f) j' := h
      rw [Lollipops.tb_injective (mem f) h']
    · exact absurd h (Lollipops.tb_ne_tl' (mem f) j j')
    · exact (not_keptEdge_tb f j
        ((congrArg (KeptEdge (Lollipops.Keep (mem f))) h).mpr (keptEdge_edgeIncl (hKeep := hK) e'))).elim
    · exact absurd h.symm (Lollipops.tb_ne_tl' (mem f) j' j)
    · have h' : Lollipops.tl (mem f) j = Lollipops.tl (mem f) j' := h
      rw [Lollipops.tl_injective (mem f) h']
    · exact (not_keptEdge_tl f j
        ((congrArg (KeptEdge (Lollipops.Keep (mem f))) h).mpr (keptEdge_edgeIncl (hKeep := hK) e'))).elim
    · exact (not_keptEdge_tb f j'
        ((congrArg (KeptEdge (Lollipops.Keep (mem f))) h).mp (keptEdge_edgeIncl (hKeep := hK) e))).elim
    · exact (not_keptEdge_tl f j'
        ((congrArg (KeptEdge (Lollipops.Keep (mem f))) h).mp (keptEdge_edgeIncl (hKeep := hK) e))).elim
    · exact congrArg Sum.inr (edgeIncl_injective (hKeep := hK) h)
  · intro e
    by_cases he : KeptEdge (Lollipops.Keep (mem f)) e
    · exact ⟨Sum.inr (edgeRestrict (hKeep := hK) e he), rfl⟩
    · rcases (Lollipops.not_keptEdge_iff (mem f) e).mp he with ⟨j, hj⟩ | ⟨j, hj⟩
      · exact ⟨Sum.inl (Sum.inl j), hj.symm⟩
      · exact ⟨Sum.inl (Sum.inr j), hj.symm⟩

/-- **The target edge dictionary.** -/
def te : (RT hc f).edges ≃ f.target.edges :=
  (occEquiv (β hc f).x).symm.trans (Equiv.ofBijective _ (teFun_bijective hc f))

@[simp] theorem te_oldE (e : (κ hc f).target.edges) :
    te hc f (oldE (β hc f).x e) = edgeIncl (Keep := Lollipops.Keep (mem f))
      (hKeep := Lollipops.Keep_nonempty (mem f)) e := by
  change teFun hc f ((occEquiv _).symm (occEquiv _ _)) = _
  rw [Equiv.symm_apply_apply]
  rfl
@[simp] theorem te_bridgeE (j : Fin k) :
    te hc f (bridgeE (β hc f).x j) = Lollipops.tb (mem f) j := by
  change teFun hc f ((occEquiv _).symm (occEquiv _ _)) = _
  rw [Equiv.symm_apply_apply]
  rfl
@[simp] theorem te_leafE (j : Fin k) :
    te hc f (leafE (β hc f).x j) = Lollipops.tl (mem f) j := by
  change teFun hc f ((occEquiv _).symm (occEquiv _ _)) = _
  rw [Equiv.symm_apply_apply]
  rfl

end Target

/-! ## 4.  The isomorphism of data -/

section Datum

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n}
  (hc : IsMarkedCubic core mark) (f : Frame (attachLollipops core mark) degree)

/-- The vertex sheet permutations: the identity on the old part. -/
def vpF : (RT hc f).V → Equiv.Perm (Fin degree) :=
  Sum.elim (fun _ ↦ Equiv.refl _) (Sum.elim (πu hc f) (πc hc f))

/-- The occurrence sheet permutations. -/
def occP : Occ (κ hc f).target k → Equiv.Perm (Fin degree)
  | .inl (.inl j) => πb hc f j
  | .inl (.inr j) => πu hc f j
  | .inr _ => Equiv.refl _

/-- The edge sheet permutations. -/
def epF (e : (RT hc f).edges) : Equiv.Perm (Fin degree) := occP hc f ((occEquiv (β hc f).x).symm e)

@[simp] theorem vpF_oldV (v : (κ hc f).target.V) : vpF hc f (oldV (β hc f).x v) = Equiv.refl _ :=
  rfl
@[simp] theorem vpF_midV (j : Fin k) : vpF hc f (midV (β hc f).x j) = πu hc f j := rfl
@[simp] theorem vpF_tipV (j : Fin k) : vpF hc f (tipV (β hc f).x j) = πc hc f j := rfl

@[simp] theorem epF_oldE (e : (κ hc f).target.edges) :
    epF hc f (oldE (β hc f).x e) = Equiv.refl _ := by
  change occP hc f ((occEquiv _).symm (occEquiv _ _)) = _
  rw [Equiv.symm_apply_apply]
  rfl
@[simp] theorem epF_bridgeE (j : Fin k) : epF hc f (bridgeE (β hc f).x j) = πb hc f j := by
  change occP hc f ((occEquiv _).symm (occEquiv _ _)) = _
  rw [Equiv.symm_apply_apply]
  rfl
@[simp] theorem epF_leafE (j : Fin k) : epF hc f (leafE (β hc f).x j) = πu hc f j := by
  change occP hc f ((occEquiv _).symm (occEquiv _ _)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- **The isomorphism of data**: regrowth after restriction is `f`. -/
def datumIso : GeometricDatumIso (Regrow.datum (κ hc f)) f.data where
  targetVertex := tv hc f
  targetEdge := te hc f
  ends e := by
    rcases edge_cases (β hc f).x e with ⟨g, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [te_oldE, oldE_ends]
      exact Or.inl rfl
    · rw [te_bridgeE, bridgeE_ends]
      rcases Lollipops.tb_ends (mem f) j with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (Prod.ext h1 h2)
      · exact Or.inr (Prod.ext h1 h2)
    · rw [te_leafE, leafE_ends]
      rcases Lollipops.tl_ends (mem f) j with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (Prod.ext h1 h2)
      · exact Or.inr (Prod.ext h1 h2)
  vertexPerm := vpF hc f
  edgePerm := epF hc f
  vertexPartition v := by
    rcases vertex_cases (β hc f).x v with ⟨w, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [vpF_oldV, Transport.DatumIso.relabel_refl]
      rfl
    · exact adjPerm_relabel (aa_ne_bb hc f j) (rr_ne_ss f j) (sameBlocks_uP f j)
    · exact adjPerm_relabel (aa_ne_bb hc f j) (rr_ne_ss f j) (sameBlocks_vC f j)
  edgePartition e := by
    rcases edge_cases (β hc f).x e with ⟨g, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [te_oldE, epF_oldE, ep_oldE, Transport.DatumIso.relabel_refl]
      rfl
    · rw [te_bridgeE, epF_bridgeE, ep_bridgeE]
      exact adjPerm_relabel (aa_ne_bb hc f j) (rr_ne_ss f j) (sameBlocks_tb f j)
    · rw [te_leafE, epF_leafE, ep_leafE, SheetPartition.discrete_relabel]
      exact tl_discrete f j
  compatible e v hv s := by
    rcases edge_cases (β hc f).x e with ⟨g, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [oldE_ends] at hv
      rw [epF_oldE]
      rcases vertex_cases (β hc f).x v with ⟨w, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [vpF_oldV]
        rfl
      · simp at hv
      · simp at hv
    · rw [bridgeE_ends] at hv
      rw [epF_bridgeE]
      rcases vertex_cases (β hc f).x v with ⟨w, rfl⟩ | ⟨j', rfl⟩ | ⟨j', rfl⟩
      · simp only [oldV_inj, midV_ne_oldV, or_false] at hv
        subst hv
        rw [vpF_oldV, Equiv.refl_symm, Equiv.refl_apply]
        exact rel_π hc f j _ s
      · simp only [oldV_ne_midV, midV_inj, false_or] at hv
        subst hv
        rw [vpF_midV]
        exact pair_rel_adjPerm _ s
      · simp at hv
    · rw [leafE_ends] at hv
      rw [epF_leafE]
      rcases vertex_cases (β hc f).x v with ⟨w, rfl⟩ | ⟨j', rfl⟩ | ⟨j', rfl⟩
      · simp at hv
      · simp only [midV_inj, tipV_ne_midV, or_false] at hv
        subst hv
        rw [vpF_midV, Equiv.symm_apply_apply]
        rfl
      · simp only [midV_ne_tipV, tipV_inj, false_or] at hv
        subst hv
        rw [vpF_tipV]
        exact pair_rel_adjPerm _ s

end Datum

/-! ## 5.  The frame isomorphism -/

section FrameIsoSection

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n}
  (hc : IsMarkedCubic core mark) (f : Frame (attachLollipops core mark) degree)

theorem P_repr_aa (j : Fin k) : ((β hc f).P j).repr (aa hc f j) = aa hc f j :=
  (pair_repr_eq_self_iff (aa_ne_bb hc f j) _).mpr (aa_ne_bb hc f j)

theorem sve_oldSV (Y : (κ hc f).data.SourceVertex) :
    (datumIso hc f).sourceVertexEquiv (oldSV (β hc f) Y) =
      svIncl (Keep := Lollipops.Keep (mem f)) (hKeep := Lollipops.Keep_nonempty (mem f)) Y :=
  rfl

theorem sve_wSV (j : Fin k) :
    (datumIso hc f).sourceVertexEquiv (wSV (β hc f) j) = Lollipops.loopV (mem f) j := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change πu hc f j (((β hc f).P j).repr (aa hc f j)) = rr f j
    rw [P_repr_aa]
    exact πu_a hc f j

theorem see_oldSE (F : (κ hc f).data.SourceEdge) :
    (datumIso hc f).sourceEdgeEquiv (oldSE (β hc f) F) =
      seIncl (Keep := Lollipops.Keep (mem f)) (hKeep := Lollipops.Keep_nonempty (mem f)) F := by
  apply Subtype.ext
  change (te hc f (oldE (β hc f).x F.1.1), epF hc f (oldE (β hc f).x F.1.1) F.1.2) = _
  rw [te_oldE, epF_oldE]
  rfl

theorem see_ebSE (j : Fin k) :
    (datumIso hc f).sourceEdgeEquiv (ebSE (β hc f) j) = Lollipops.bridgeE (mem f) j := by
  apply Subtype.ext
  apply Prod.ext
  · exact te_bridgeE hc f j
  · change epF hc f (bridgeE (β hc f).x j)
      (((regrowDatum (β hc f)).edgePartition (bridgeE (β hc f).x j)).repr (aa hc f j)) =
      (Lollipops.bridgeE (mem f) j).1.2
    rw [epF_bridgeE, ep_bridgeE, P_repr_aa, πb_a]

/-- **Regrowth after restriction is the identity**, up to isomorphism over the lollipop core. -/
def regrowRestrictIso : FrameIso (regrowFrame hc (κ hc f)) f where
  datum := datumIso hc f
  overCore_vertex branch := by
    have hD := connected (κ hc f)
    have hM := markValency_ne_zero (κ hc f)
    have hI := (κ hc f).ident.markSource_injective hc
    obtain ⟨z, rfl⟩ := (branchVertexEquiv (β hc f) hD hM hI).surjective branch
    change f.ident.vertex ((datumIso hc f).branchVertexEquiv _
        (branchVertexEquiv (β hc f) hD hM hI z)) =
      (ident (κ hc f) hc).vertex (branchVertexEquiv (β hc f) hD hM hI z)
    rw [ident_vertex_apply]
    rcases z with Y | j
    · have hB : (datumIso hc f).branchVertexEquiv (valid (κ hc f) hc).1
          (branchVertexEquiv (β hc f) hD hM hI (.inl Y)) =
          ⟨svIncl Y.1, (Lollipops.branch_iff (mem f) hc Y.1).mp Y.2⟩ :=
        Subtype.ext (sve_oldSV hc f Y.1)
      rw [hB]
      exact (Lollipops.oldVertex_vertexEquiv (mem f) hc Y).symm
    · have hB : (datumIso hc f).branchVertexEquiv (valid (κ hc f) hc).1
          (branchVertexEquiv (β hc f) hD hM hI (.inr j)) =
          ⟨Lollipops.loopV (mem f) j, Lollipops.three_le_loopV (mem f) j⟩ :=
        Subtype.ext (sve_wSV hc f j)
      rw [hB]
      exact Lollipops.ident_loopV (mem f) j
  overCore_row path := by
    have hD := connected (κ hc f)
    have hM := markValency_ne_zero (κ hc f)
    obtain ⟨t, rfl⟩ := (stablePathEquiv (β hc f) hD hM).symm.surjective path
    rw [stablePathEquiv_symm_apply]
    rcases t with P | j | j
    · induction P using Quot.ind with
      | mk F =>
        change f.ident.row ((datumIso hc f).stablePathEquiv (valid (κ hc f) hc).1
            (oldND (β hc f) hD hM F).stablePath) =
          (ident (κ hc f) hc).row (oldND (β hc f) hD hM F).stablePath
        rw [Count.GeometricDatumIso.stablePathEquiv_mk, CorrRestrictRegrow.ident_row_oldND]
        have hE : (datumIso hc f).nonDanglingEdgeEquiv (valid (κ hc f) hc).1
            (oldND (β hc f) hD hM F) = Lollipops.ndIncl' (mem f) hc F :=
          Subtype.ext (see_oldSE hc f F.1)
        rw [hE]
        exact (Lollipops.coreSlot_rowEquiv (mem f) hc F).symm
    · change f.ident.row ((datumIso hc f).stablePathEquiv (valid (κ hc f) hc).1
          (ebND (β hc f) hD hM j).stablePath) =
        (ident (κ hc f) hc).row (ebND (β hc f) hD hM j).stablePath
      rw [Count.GeometricDatumIso.stablePathEquiv_mk, ident_row_stablePath, rowTag_ebND]
      have hE : (datumIso hc f).nonDanglingEdgeEquiv (valid (κ hc f) hc).1
          (ebND (β hc f) hD hM j) =
          ⟨Lollipops.bridgeE (mem f) j, Lollipops.bridgeE_survives (mem f) j⟩ :=
        Subtype.ext (see_ebSE hc f j)
      rw [hE]
      exact Lollipops.ident_row_bridgePath (mem f) j
    · change f.ident.row ((datumIso hc f).stablePathEquiv (valid (κ hc f) hc).1
          (e₁ND (β hc f) hD hM j).stablePath) =
        (ident (κ hc f) hc).row (e₁ND (β hc f) hD hM j).stablePath
      rw [Count.GeometricDatumIso.stablePathEquiv_mk, ident_row_stablePath, rowTag_e₁ND]
      have hT : ((datumIso hc f).nonDanglingEdgeEquiv (valid (κ hc f) hc).1
          (e₁ND (β hc f) hD hM j)).1.1.1 = Lollipops.tl (mem f) j :=
        te_leafE hc f j
      have hRow := Lollipops.onRow_of_over_tl (mem f)
        ((datumIso hc f).nonDanglingEdgeEquiv (valid (κ hc f) hc).1 (e₁ND (β hc f) hD hM j)).2 hT
      refine (congrArg (fun P ↦ f.ident.row P) hRow).trans ?_
      exact (mem f).ident.row.apply_symm_apply (loopSlot p j)

end FrameIsoSection

end

end DraismaVargas.Count.MarkedCount.CorrRegrowRestrict
