module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RegrowChain

@[expose] public section

/-!
# Regrowth, part 4: the regrown datum

A `CatBranching ψ N d c` records, over a datum `ψ` of degree `d'`:

* the sheets `e : Fin d' ⊕ N ≃ Fin d` of the regrowth: the old sheets and the new sheets
  `n_1, …` (the sheets are `[d′] ⊔ {n_1, …, n_j}`);
* the marks (source vertices of `ψ`);
* a valid tail chain at every mark, with `P 0` inside the block of the mark, every sheet entering
  a chain after `P 0` new and entering one chain only, and every new sheet used.

`regrowDatum β` is the datum over `catTarget c T β.x` with the partitions of `ψ` lifted
(`liftPart`: the new sheets are singletons over `T`) and the chain blocks over the tails
(`blockPart`).

Proved here: the source dictionaries (`psiSV`, `newSV`, `tailSV`; `psiSE`, `newSE`, `tailSE`) and
their ends, **Riemann--Hurwitz** (`riemannHurwitz_regrowDatum`: at a mark
`r⁺ = r_ψ - (|P_1| - 1)`, so `r_ψ ≥ s_1 - 1` is what is needed; `0`, `1`, `2` at the spine, bulb
and tip blocks), **connectedness** (`connected_regrowDatum`: through the ascents) and the **genus**
(`genus_regrowDatum`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral.CatRegrow

noncomputable section

open DraismaVargas.Infrastructure CatSlot TailV
open DraismaVargas.LocalCases.W4StableSource

variable {T : CFGraph.{0}} {d' d k : ℕ} {N : Type} {c : Fin k → ℕ}

/-- **The data of a caterpillar regrowth** over `ψ`. -/
structure CatBranching (ψ : GluingDatum T d') (N : Type) (d : ℕ) (c : Fin k → ℕ) where
  /-- The sheets of the regrowth: the old ones and the new ones. -/
  e : Fin d' ⊕ N ≃ Fin d
  /-- The source vertices of the marks. -/
  mark : Fin k → ψ.SourceVertex
  /-- The tail chain at every mark. -/
  chain : ∀ j, TailChain d (c j)
  valid : ∀ j, (chain j).Valid
  /-- `P_1` lies in the block of the mark. -/
  P0_sub : ∀ j, ∀ q ∈ (chain j).P 0, ∃ i, q = old e i ∧
    (ψ.vertexPartition (mark j).1.1).Rel (mark j).1.2 i
  /-- A sheet entering a chain after `P_1` is new. -/
  fresh : ∀ j (i : Fin (c j + 1)) q, q ∈ (chain j).P i → q ∉ (chain j).P 0 → ∃ n, q = new e n
  /-- ... and enters one chain only. -/
  fresh_disjoint : ∀ j j' (i : Fin (c j + 1)) (i' : Fin (c j' + 1)) q, q ∈ (chain j).P i →
    q ∈ (chain j').P i' → q ∉ (chain j).P 0 → j = j'
  /-- Every new sheet is used. -/
  new_used : ∀ n, ∃ j, ∃ i : Fin (c j + 1), new e n ∈ (chain j).P i

namespace CatBranching

variable {ψ : GluingDatum T d'} (β : CatBranching ψ N d c)

/-- The image of mark `j`. -/
def x (j : Fin k) : T.V := (β.mark j).1.1

/-- The representative sheet of mark `j`. -/
def a (j : Fin k) : Fin d' := (β.mark j).1.2

/-- The block at a tail vertex. -/
def vB (w : TV c) : Finset (Fin d) := (β.chain w.1).vB w.2
/-- Its name. -/
def vA (w : TV c) : Fin d := (β.chain w.1).vA w.2
/-- The block over a tail slot. -/
def eB (t : TE c) : Finset (Fin d) := (β.chain t.1).eB t.2
/-- Its name. -/
def eA (t : TE c) : Fin d := (β.chain t.1).eA t.2
/-- The surviving sheets over a tail slot. -/
def rowSet (t : TE c) : Finset (Fin d) := (β.chain t.1).rowSet t.2

theorem vA_anchored (w : TV c) : Anchored (β.vB w) (β.vA w) := (β.valid w.1).vA_anchored w.2
theorem vA_mem (w : TV c) : β.vA w ∈ β.vB w := (β.valid w.1).vA_mem w.2
theorem eA_anchored (t : TE c) : Anchored (β.eB t) (β.eA t) := (β.valid t.1).eA_anchored t.2

theorem eB_sub_vB_head (t : TE c) : β.eB t ⊆ β.vB ⟨t.1, lHead t.2⟩ :=
  (β.valid t.1).eB_sub_vB_head t.2

theorem eB_sub_vB_tail {t : TE c} {w : TailV (c t.1)} (h : lTail t.2 = some w) :
    β.eB t ⊆ β.vB ⟨t.1, w⟩ := (β.valid t.1).eB_sub_vB_tail h

theorem mark_eq (j : Fin k) : β.mark j = ψ.sourceEndpoint (β.x j) (β.a j) :=
  (ψ.sourceEndpoint_self (β.mark j)).symm

theorem a_repr (j : Fin k) : (ψ.vertexPartition (β.x j)).repr (β.a j) = β.a j := (β.mark j).2

/-- The block of `P_1` refines the lifted partition at the mark. -/
theorem P0_rel {j : Fin k} {q q' : Fin d} (hq : q ∈ (β.chain j).P 0) (hq' : q' ∈ (β.chain j).P 0) :
    (liftPart β.e (ψ.vertexPartition (β.x j))).Rel q q' := by
  obtain ⟨i, rfl, hi⟩ := β.P0_sub j q hq
  obtain ⟨i', rfl, hi'⟩ := β.P0_sub j q' hq'
  rw [liftPart_rel_old_old]
  exact hi.symm.trans hi'

/-! ## 1.  The datum -/

/-- The partition at a vertex of the regrown target. -/
def vtxPartition : Vtx c T → SheetPartition d
  | .inl v => liftPart β.e (ψ.vertexPartition v)
  | .inr w => blockPart (β.vB w) (β.vA w)

/-- The partition over an occurrence of the regrown target. -/
def occPartition : Occ c T → SheetPartition d
  | .inl ε => liftPart β.e (ψ.edgePartition ε)
  | .inr t => blockPart (β.eB t) (β.eA t)

theorem refines_tailEnd (t : TE c) :
    (blockPart (β.eB t) (β.eA t)).Refines (β.vtxPartition (attach c β.x t.1 (lTail t.2))) := by
  obtain ⟨j, s⟩ := t
  cases h : lTail s with
  | none =>
    rw [lTail_eq_none_iff] at h
    subst h
    exact blockPart_refines (β.eA_anchored _) fun q hq q' hq' ↦ β.P0_rel hq hq'
  | some w =>
    exact blockPart_refines_blockPart (β.eA_anchored _) (β.eB_sub_vB_tail (t := ⟨j, s⟩) h)

theorem occPartition_refines (o : Occ c T) :
    (β.occPartition o).Refines (β.vtxPartition (occEnds c β.x o).1) ∧
      (β.occPartition o).Refines (β.vtxPartition (occEnds c β.x o).2) := by
  rcases o with ε | t
  · exact ⟨liftPart_refines (ψ.refines_left ε), liftPart_refines (ψ.refines_right ε)⟩
  · exact ⟨β.refines_tailEnd t,
      blockPart_refines_blockPart (β.eA_anchored t) (β.eB_sub_vB_head t)⟩

/-- **The regrown datum**. -/
def regrowDatum : GluingDatum (catTarget c T β.x) d where
  degree_pos := Fin.pos (β.e (Sum.inl ⟨0, ψ.degree_pos⟩))
  vertexPartition := β.vtxPartition
  edgePartition e := β.occPartition ((occEquiv c β.x).symm e)
  refines_left e := by
    obtain ⟨o, rfl⟩ := (occEquiv c β.x).surjective e
    rw [Equiv.symm_apply_apply, occEquiv_ends]
    exact (β.occPartition_refines o).1
  refines_right e := by
    obtain ⟨o, rfl⟩ := (occEquiv c β.x).surjective e
    rw [Equiv.symm_apply_apply, occEquiv_ends]
    exact (β.occPartition_refines o).2

@[simp] theorem vp_oldV (v : T.V) :
    β.regrowDatum.vertexPartition (oldV c β.x v) = liftPart β.e (ψ.vertexPartition v) := rfl
@[simp] theorem vp_tailV (w : TV c) :
    β.regrowDatum.vertexPartition (tailV c β.x w) = blockPart (β.vB w) (β.vA w) := rfl

@[simp] theorem ep_oldE (ε : T.edges) :
    β.regrowDatum.edgePartition (oldE c β.x ε) = liftPart β.e (ψ.edgePartition ε) := by
  change β.occPartition ((occEquiv c β.x).symm (occEquiv c β.x _)) = _
  rw [Equiv.symm_apply_apply]; rfl

@[simp] theorem ep_tailE (t : TE c) :
    β.regrowDatum.edgePartition (tailE c β.x t) = blockPart (β.eB t) (β.eA t) := by
  change β.occPartition ((occEquiv c β.x).symm (occEquiv c β.x _)) = _
  rw [Equiv.symm_apply_apply]; rfl

/-! ## 2.  The source -/

/-- An old source vertex, of an old sheet. -/
def psiSV (Y : ψ.SourceVertex) : β.regrowDatum.SourceVertex :=
  ⟨(oldV c β.x Y.1.1, old β.e Y.1.2), by
    change (liftPart β.e (ψ.vertexPartition Y.1.1)).repr (old β.e Y.1.2) = _
    rw [liftPart_repr_old, Y.2]⟩

/-- The source vertex of a new sheet over an old target vertex (a singleton). -/
def newSV (v : T.V) (n : N) : β.regrowDatum.SourceVertex :=
  ⟨(oldV c β.x v, new β.e n), liftPart_repr_new _ n⟩

/-- A source vertex over a tail vertex. -/
def tailSV (w : TV c) (q : Fin d) : β.regrowDatum.SourceVertex :=
  β.regrowDatum.sourceEndpoint (tailV c β.x w) q

/-- The block vertex over a tail vertex (`B_i`, the bulb `A_i`, the loop vertex `C_i`). -/
def blockSV (w : TV c) : β.regrowDatum.SourceVertex := β.tailSV w (β.vA w)

/-- An old source edge, of an old sheet. -/
def psiSE (F : ψ.SourceEdge) : β.regrowDatum.SourceEdge :=
  ⟨(oldE c β.x F.1.1, old β.e F.1.2), by
    rw [ep_oldE, liftPart_repr_old, F.2]⟩

/-- The source edge of a new sheet over an old target edge. -/
def newSE (ε : T.edges) (n : N) : β.regrowDatum.SourceEdge :=
  ⟨(oldE c β.x ε, new β.e n), by rw [ep_oldE, liftPart_repr_new]⟩

/-- A source edge over a tail slot. -/
def tailSE (t : TE c) (q : Fin d) : β.regrowDatum.SourceEdge :=
  β.regrowDatum.sourceEdge (tailE c β.x t) q

/-- The block edge over a tail slot (`e_i`, a bridge of index two). -/
def blockSE (t : TE c) : β.regrowDatum.SourceEdge := β.tailSE t (β.eA t)

@[simp] theorem psiSV_target (Y : ψ.SourceVertex) : (β.psiSV Y).1.1 = oldV c β.x Y.1.1 := rfl
@[simp] theorem newSV_target (v : T.V) (n : N) : (β.newSV v n).1.1 = oldV c β.x v := rfl
@[simp] theorem tailSV_target (w : TV c) (q : Fin d) : (β.tailSV w q).1.1 = tailV c β.x w := rfl
@[simp] theorem psiSE_target (F : ψ.SourceEdge) : (β.psiSE F).1.1 = oldE c β.x F.1.1 := rfl
@[simp] theorem newSE_target (ε : T.edges) (n : N) : (β.newSE ε n).1.1 = oldE c β.x ε := rfl
@[simp] theorem tailSE_target (t : TE c) (q : Fin d) : (β.tailSE t q).1.1 = tailE c β.x t := rfl

theorem psiSV_injective : Function.Injective β.psiSV := by
  intro X Y h
  have h1 := congrArg (fun Z : β.regrowDatum.SourceVertex ↦ Z.1.1) h
  have h2 := congrArg (fun Z : β.regrowDatum.SourceVertex ↦ Z.1.2) h
  simp only [psiSV_target, oldV_inj] at h1
  exact Subtype.ext (Prod.ext h1 (old_injective h2))

@[simp] theorem psiSV_inj {X Y : ψ.SourceVertex} : β.psiSV X = β.psiSV Y ↔ X = Y :=
  β.psiSV_injective.eq_iff

@[simp] theorem newSV_inj {v v' : T.V} {n n' : N} :
    β.newSV v n = β.newSV v' n' ↔ v = v' ∧ n = n' := by
  constructor
  · intro h
    have h1 := congrArg (fun Z : β.regrowDatum.SourceVertex ↦ Z.1.1) h
    have h2 := congrArg (fun Z : β.regrowDatum.SourceVertex ↦ Z.1.2) h
    simp only [newSV_target, oldV_inj] at h1
    exact ⟨h1, new_injective h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] theorem psiSV_ne_newSV (Y : ψ.SourceVertex) (v : T.V) (n : N) :
    β.psiSV Y ≠ β.newSV v n := fun h ↦
  old_ne_new _ _ (congrArg (fun Z : β.regrowDatum.SourceVertex ↦ Z.1.2) h)
@[simp] theorem newSV_ne_psiSV (Y : ψ.SourceVertex) (v : T.V) (n : N) :
    β.newSV v n ≠ β.psiSV Y := fun h ↦ β.psiSV_ne_newSV Y v n h.symm
@[simp] theorem psiSV_ne_tailSV (Y : ψ.SourceVertex) (w : TV c) (q : Fin d) :
    β.psiSV Y ≠ β.tailSV w q := fun h ↦
  oldV_ne_tailV c β.x _ _ (congrArg (fun Z : β.regrowDatum.SourceVertex ↦ Z.1.1) h)
@[simp] theorem tailSV_ne_psiSV (Y : ψ.SourceVertex) (w : TV c) (q : Fin d) :
    β.tailSV w q ≠ β.psiSV Y := fun h ↦ β.psiSV_ne_tailSV Y w q h.symm
@[simp] theorem newSV_ne_tailSV (v : T.V) (n : N) (w : TV c) (q : Fin d) :
    β.newSV v n ≠ β.tailSV w q := fun h ↦
  oldV_ne_tailV c β.x _ _ (congrArg (fun Z : β.regrowDatum.SourceVertex ↦ Z.1.1) h)
@[simp] theorem tailSV_ne_newSV (v : T.V) (n : N) (w : TV c) (q : Fin d) :
    β.tailSV w q ≠ β.newSV v n := fun h ↦ β.newSV_ne_tailSV v n w q h.symm

theorem tailSV_eq_iff (w w' : TV c) (q q' : Fin d) :
    β.tailSV w q = β.tailSV w' q' ↔ w = w' ∧ (q = q' ∨ (q ∈ β.vB w ∧ q' ∈ β.vB w)) := by
  constructor
  · intro h
    have hw : w = w' :=
      tailV_injective c β.x (congrArg (fun Z : β.regrowDatum.SourceVertex ↦ Z.1.1) h)
    subst hw
    refine ⟨rfl, ?_⟩
    have := (β.regrowDatum.sourceEndpoint_eq_iff (tailV c β.x w) q (β.tailSV w q')).mp h
    rw [← blockPart_rel_iff (β.vA_anchored w)]
    exact this.2.trans ((β.regrowDatum.vertexPartition (tailV c β.x w)).rel_repr_left q')
  · rintro ⟨rfl, h⟩
    unfold tailSV
    apply (β.regrowDatum.sourceEndpoint_eq_iff _ _ _).mpr
    refine ⟨rfl, ?_⟩
    have h' : (blockPart (β.vB w) (β.vA w)).Rel q q' := (blockPart_rel_iff (β.vA_anchored w) _ _).mpr h
    exact h'.trans ((β.regrowDatum.vertexPartition (tailV c β.x w)).rel_repr_right q')

theorem tailSV_eq_blockSV_iff (w w' : TV c) (q : Fin d) :
    β.tailSV w q = β.blockSV w' ↔ w = w' ∧ q ∈ β.vB w := by
  unfold blockSV
  rw [tailSV_eq_iff]
  constructor
  · rintro ⟨rfl, rfl | ⟨h, -⟩⟩
    · exact ⟨rfl, β.vA_mem w⟩
    · exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, Or.inr ⟨h, β.vA_mem w⟩⟩

theorem tailSV_of_mem {w : TV c} {q : Fin d} (hq : q ∈ β.vB w) : β.tailSV w q = β.blockSV w :=
  (β.tailSV_eq_blockSV_iff w w q).mpr ⟨rfl, hq⟩

@[simp] theorem blockSV_inj {w w' : TV c} : β.blockSV w = β.blockSV w' ↔ w = w' := by
  rw [blockSV, tailSV_eq_blockSV_iff]
  constructor
  · exact fun h ↦ h.1
  · rintro rfl; exact ⟨rfl, β.vA_mem w⟩

theorem sourceEndpoint_oldV_old (v : T.V) (i : Fin d') :
    β.regrowDatum.sourceEndpoint (oldV c β.x v) (old β.e i) = β.psiSV (ψ.sourceEndpoint v i) := by
  apply Subtype.ext
  change (oldV c β.x v, (liftPart β.e (ψ.vertexPartition v)).repr (old β.e i)) = _
  rw [liftPart_repr_old]
  rfl

theorem sourceEndpoint_oldV_new (v : T.V) (n : N) :
    β.regrowDatum.sourceEndpoint (oldV c β.x v) (new β.e n) = β.newSV v n := by
  apply Subtype.ext
  change (oldV c β.x v, (liftPart β.e (ψ.vertexPartition v)).repr (new β.e n)) = _
  rw [liftPart_repr_new]
  rfl

/-- **Every source vertex is old, new, or over a tail vertex.** -/
theorem sourceVertex_cases (X : β.regrowDatum.SourceVertex) :
    (∃ Y, X = β.psiSV Y) ∨ (∃ v n, X = β.newSV v n) ∨ ∃ w q, X = β.tailSV w q := by
  obtain ⟨⟨v, q⟩, hX⟩ := X
  rcases v with v | w
  · rcases sheet_cases (e := β.e) q with ⟨i, rfl⟩ | ⟨n, rfl⟩
    · have hi : (ψ.vertexPartition v).repr i = i := by
        have h : (liftPart β.e (ψ.vertexPartition v)).repr (old β.e i) = old β.e i := hX
        rw [liftPart_repr_old] at h
        exact old_injective h
      exact Or.inl ⟨⟨(v, i), hi⟩, rfl⟩
    · exact Or.inr (Or.inl ⟨v, n, rfl⟩)
  · refine Or.inr (Or.inr ⟨w, q, ?_⟩)
    exact (β.regrowDatum.sourceEndpoint_self ⟨(Sum.inr w, q), hX⟩).symm

theorem psiSE_injective : Function.Injective β.psiSE := by
  intro X Y h
  have h1 := congrArg (fun Z : β.regrowDatum.SourceEdge ↦ Z.1.1) h
  have h2 := congrArg (fun Z : β.regrowDatum.SourceEdge ↦ Z.1.2) h
  simp only [psiSE_target, oldE_inj] at h1
  exact Subtype.ext (Prod.ext h1 (old_injective h2))

@[simp] theorem psiSE_inj {X Y : ψ.SourceEdge} : β.psiSE X = β.psiSE Y ↔ X = Y :=
  β.psiSE_injective.eq_iff

@[simp] theorem newSE_inj {ε ε' : T.edges} {n n' : N} :
    β.newSE ε n = β.newSE ε' n' ↔ ε = ε' ∧ n = n' := by
  constructor
  · intro h
    have h1 := congrArg (fun Z : β.regrowDatum.SourceEdge ↦ Z.1.1) h
    have h2 := congrArg (fun Z : β.regrowDatum.SourceEdge ↦ Z.1.2) h
    simp only [newSE_target, oldE_inj] at h1
    exact ⟨h1, new_injective h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] theorem psiSE_ne_newSE (F : ψ.SourceEdge) (ε : T.edges) (n : N) :
    β.psiSE F ≠ β.newSE ε n := fun h ↦
  old_ne_new _ _ (congrArg (fun Z : β.regrowDatum.SourceEdge ↦ Z.1.2) h)
@[simp] theorem newSE_ne_psiSE (F : ψ.SourceEdge) (ε : T.edges) (n : N) :
    β.newSE ε n ≠ β.psiSE F := fun h ↦ β.psiSE_ne_newSE F ε n h.symm
@[simp] theorem psiSE_ne_tailSE (F : ψ.SourceEdge) (t : TE c) (q : Fin d) :
    β.psiSE F ≠ β.tailSE t q := fun h ↦
  oldE_ne_tailE c β.x _ _ (congrArg (fun Z : β.regrowDatum.SourceEdge ↦ Z.1.1) h)
@[simp] theorem tailSE_ne_psiSE (F : ψ.SourceEdge) (t : TE c) (q : Fin d) :
    β.tailSE t q ≠ β.psiSE F := fun h ↦ β.psiSE_ne_tailSE F t q h.symm
@[simp] theorem newSE_ne_tailSE (ε : T.edges) (n : N) (t : TE c) (q : Fin d) :
    β.newSE ε n ≠ β.tailSE t q := fun h ↦
  oldE_ne_tailE c β.x _ _ (congrArg (fun Z : β.regrowDatum.SourceEdge ↦ Z.1.1) h)
@[simp] theorem tailSE_ne_newSE (ε : T.edges) (n : N) (t : TE c) (q : Fin d) :
    β.tailSE t q ≠ β.newSE ε n := fun h ↦ β.newSE_ne_tailSE ε n t q h.symm

theorem tailSE_eq_iff (t t' : TE c) (q q' : Fin d) :
    β.tailSE t q = β.tailSE t' q' ↔ t = t' ∧ (q = q' ∨ (q ∈ β.eB t ∧ q' ∈ β.eB t)) := by
  constructor
  · intro h
    have ht : t = t' :=
      tailE_injective c β.x (congrArg (fun Z : β.regrowDatum.SourceEdge ↦ Z.1.1) h)
    subst ht
    refine ⟨rfl, ?_⟩
    have h2 := congrArg (fun Z : β.regrowDatum.SourceEdge ↦ Z.1.2) h
    simp only [tailSE, GluingDatum.sourceEdge_sheet, ep_tailE] at h2
    exact (blockPart_rel_iff (β.eA_anchored t) q q').mp h2
  · rintro ⟨rfl, h⟩
    apply Subtype.ext
    simp only [tailSE, GluingDatum.sourceEdge, ep_tailE]
    rw [show (blockPart (β.eB t) (β.eA t)).repr q = (blockPart (β.eB t) (β.eA t)).repr q' from
      (blockPart_rel_iff (β.eA_anchored t) q q').mpr h]

theorem tailSE_of_mem {t : TE c} {q : Fin d} (hq : q ∈ β.eB t) : β.tailSE t q = β.blockSE t := by
  unfold blockSE
  rw [tailSE_eq_iff]
  refine ⟨rfl, Or.inr ⟨hq, ?_⟩⟩
  exact (β.eA_anchored t).resolve_left (Finset.nonempty_of_ne_empty
    (Finset.ne_empty_of_mem hq)).ne_empty

/-- **Every source edge is old, new, or over a tail slot.** -/
theorem sourceEdge_cases (E : β.regrowDatum.SourceEdge) :
    (∃ F, E = β.psiSE F) ∨ (∃ ε n, E = β.newSE ε n) ∨ ∃ t q, E = β.tailSE t q := by
  rcases edge_cases c β.x E.1.1 with ⟨ε, hε⟩ | ⟨t, ht⟩
  · rcases sheet_cases (e := β.e) E.1.2 with ⟨i, hi⟩ | ⟨n, hn⟩
    · have hrepr : (ψ.edgePartition ε).repr i = i := by
        have h := E.2
        rw [hε, hi, ep_oldE, liftPart_repr_old] at h
        exact old_injective h
      refine Or.inl ⟨⟨(ε, i), hrepr⟩, Subtype.ext (Prod.ext hε hi)⟩
    · exact Or.inr (Or.inl ⟨ε, n, Subtype.ext (Prod.ext hε hn)⟩)
  · refine Or.inr (Or.inr ⟨t, E.1.2, ?_⟩)
    have h := GluingDatum.sourceEdge_self β.regrowDatum E
    rw [ht] at h
    exact h.symm

/-! ### Endpoints and incidence -/

theorem sourceEnds_psiSE (F : ψ.SourceEdge) :
    β.regrowDatum.sourceEnds (β.psiSE F) =
      (β.psiSV (ψ.sourceEnds F).1, β.psiSV (ψ.sourceEnds F).2) := by
  unfold GluingDatum.sourceEnds
  simp only [psiSE, oldE_ends]
  rw [sourceEndpoint_oldV_old, sourceEndpoint_oldV_old]

theorem sourceEnds_newSE (ε : T.edges) (n : N) :
    β.regrowDatum.sourceEnds (β.newSE ε n) =
      (β.newSV (ε : T.V × T.V).1 n, β.newSV (ε : T.V × T.V).2 n) := by
  unfold GluingDatum.sourceEnds
  simp only [newSE, oldE_ends]
  rw [sourceEndpoint_oldV_new, sourceEndpoint_oldV_new]

theorem sourceEnds_tailSE (t : TE c) (q : Fin d) :
    β.regrowDatum.sourceEnds (β.tailSE t q) =
      (β.regrowDatum.sourceEndpoint (tailEnd c β.x t) q, β.tailSV ⟨t.1, lHead t.2⟩ q) := by
  unfold tailSE
  refine Prod.ext ?_ ?_
  · rw [GenusSixExistence.Tripod.Gluing.sourceEnds_sourceEdge_fst, tailE_ends]
  · rw [GenusSixExistence.Tripod.Gluing.sourceEnds_sourceEdge_snd, tailE_ends]
    rfl

@[simp] theorem incident_psiSE_psiSV (F : ψ.SourceEdge) (Y : ψ.SourceVertex) :
    Incident β.regrowDatum (β.psiSE F) (β.psiSV Y) ↔ Incident ψ F Y := by
  unfold Incident
  rw [sourceEnds_psiSE]
  simp only [psiSV_inj]

@[simp] theorem incident_psiSE_newSV (F : ψ.SourceEdge) (v : T.V) (n : N) :
    ¬ Incident β.regrowDatum (β.psiSE F) (β.newSV v n) := by
  unfold Incident
  rw [sourceEnds_psiSE]
  simp

@[simp] theorem incident_psiSE_tailSV (F : ψ.SourceEdge) (w : TV c) (q : Fin d) :
    ¬ Incident β.regrowDatum (β.psiSE F) (β.tailSV w q) := by
  unfold Incident
  rw [sourceEnds_psiSE]
  simp

theorem incident_newSE_iff (ε : T.edges) (n : N) (X : β.regrowDatum.SourceVertex) :
    Incident β.regrowDatum (β.newSE ε n) X ↔
      X = β.newSV (ε : T.V × T.V).1 n ∨ X = β.newSV (ε : T.V × T.V).2 n := by
  unfold Incident
  rw [sourceEnds_newSE]
  simp only [eq_comm]

theorem incident_tailSE_iff (t : TE c) (q : Fin d) (X : β.regrowDatum.SourceVertex) :
    Incident β.regrowDatum (β.tailSE t q) X ↔
      X = β.regrowDatum.sourceEndpoint (tailEnd c β.x t) q ∨ X = β.tailSV ⟨t.1, lHead t.2⟩ q := by
  unfold Incident
  rw [sourceEnds_tailSE]
  simp only [eq_comm]

/-- The old end of the first path edge, in the block of the mark, is the mark. -/
theorem sourceEndpoint_x_of_mem {j : Fin k} {q : Fin d} (hq : q ∈ (β.chain j).P 0) :
    β.regrowDatum.sourceEndpoint (oldV c β.x (β.x j)) q = β.psiSV (β.mark j) := by
  obtain ⟨i, rfl, hi⟩ := β.P0_sub j q hq
  rw [sourceEndpoint_oldV_old, β.mark_eq j, psiSV_inj]
  apply (ψ.sourceEndpoint_eq_iff _ _ _).mpr
  refine ⟨rfl, ?_⟩
  exact hi.symm.trans ((ψ.vertexPartition (β.x j)).rel_repr_right (β.a j))

/-- The tail end of a tail slot, at a sheet of its block. -/
theorem sourceEndpoint_tailEnd_of_mem {t : TE c} {q : Fin d} (hq : q ∈ β.eB t) :
    β.regrowDatum.sourceEndpoint (tailEnd c β.x t) q =
      Option.elim (lTail t.2) (β.psiSV (β.mark t.1)) (fun w ↦ β.blockSV ⟨t.1, w⟩) := by
  obtain ⟨j, s⟩ := t
  rw [tailEnd_eq_attach]
  cases h : lTail s with
  | none =>
    rw [lTail_eq_none_iff] at h
    subst h
    exact β.sourceEndpoint_x_of_mem hq
  | some w =>
    exact β.tailSV_of_mem (β.eB_sub_vB_tail (t := ⟨j, s⟩) h hq)

/-- The head end of a tail slot, at a sheet of its block. -/
theorem tailSV_head_of_mem {t : TE c} {q : Fin d} (hq : q ∈ β.eB t) :
    β.tailSV ⟨t.1, lHead t.2⟩ q = β.blockSV ⟨t.1, lHead t.2⟩ :=
  β.tailSV_of_mem (β.eB_sub_vB_head t hq)

/-! ## 3.  Riemann--Hurwitz -/

section RH

variable (hInj : Function.Injective β.mark)
  (hRam : ∀ j, ((β.chain j).P 0).card - 1 ≤ MarkedCount.markRamification ψ (β.mark j))

include hInj in
/-- At most one mark lies in a given block over a given target vertex. -/
theorem mark_unique {v : T.V} {i : Fin d'} {j j' : Fin k} (hj : β.x j = v) (hj' : β.x j' = v)
    (hi : (ψ.vertexPartition v).Rel i (β.a j)) (hi' : (ψ.vertexPartition v).Rel i (β.a j')) :
    j = j' := by
  apply hInj
  rw [β.mark_eq j, β.mark_eq j']
  apply (ψ.sourceEndpoint_eq_iff _ _ _).mpr
  refine ⟨by rw [hj, hj']; rfl, ?_⟩
  show (ψ.vertexPartition (β.x j)).Rel (β.a j) ((ψ.vertexPartition (β.x j')).repr (β.a j'))
  rw [hj, hj']
  exact hi.symm.trans (hi'.trans ((ψ.vertexPartition v).rel_repr_right _))

include hInj hRam in
/-- Riemann--Hurwitz at an old vertex, at an old sheet. -/
theorem riemannHurwitz_old (hRH : ψ.RiemannHurwitz) (v : T.V) (i : Fin d') :
    (∑ e ∈ GluingDatum.incidentEdges (oldV c β.x v),
      ((β.regrowDatum.edgePartition e).blockCountWithin
        (β.regrowDatum.vertexPartition (oldV c β.x v)) (old β.e i) : ℤ)) - 2 ≥
    ((β.regrowDatum.vertexPartition (oldV c β.x v)).blockCard (old β.e i) : ℤ) *
      (((GluingDatum.incidentEdges (oldV c β.x v)).card : ℤ) - 2) := by
  classical
  rw [sum_incidentEdges_oldV, card_incidentEdges_oldV]
  simp only [ep_oldE, ep_tailE, vp_oldV, liftPart_blockCountWithin_old, liftPart_blockCard_old]
  set Q := ψ.vertexPartition v with hQ
  set J := Finset.univ.filter fun j ↦ β.x j = v
  have hTerm : ∀ j ∈ J,
      ((blockPart (β.eB ⟨j, path 0⟩) (β.eA ⟨j, path 0⟩)).blockCountWithin (liftPart β.e Q)
        (old β.e i) : ℤ) =
        (Q.blockCard i : ℤ) -
          (if Q.Rel i (β.a j) then (((β.chain j).P 0).card : ℤ) - 1 else 0) := by
    intro j hj
    have hx : β.x j = v := (Finset.mem_filter.mp hj).2
    have hA := β.eA_anchored ⟨j, path 0⟩
    have hne : (β.eB ⟨j, path 0⟩).Nonempty := (β.valid j).P_nonempty 0
    have hcard : (β.eB ⟨j, path 0⟩).card = ((β.chain j).P 0).card := rfl
    by_cases hi : Q.Rel i (β.a j)
    · rw [ite_eq_left hi]
      have hsub : β.eB ⟨j, path 0⟩ ⊆ (liftPart β.e Q).block (old β.e i) := by
        intro q hq
        obtain ⟨i', rfl, hi'⟩ := β.P0_sub j q hq
        change (ψ.vertexPartition (β.x j)).Rel (β.a j) i' at hi'
        rw [SheetPartition.mem_block_iff, liftPart_rel_old_old]
        rw [hx] at hi'
        exact hi.trans hi'
      have h := blockCountWithin_blockPart hA hsub
      rw [liftPart_blockCard_old, ite_eq_left hne, hcard] at h
      omega
    · rw [ite_eq_right hi, sub_zero]
      have hdisj : Disjoint (β.eB ⟨j, path 0⟩) ((liftPart β.e Q).block (old β.e i)) := by
        rw [Finset.disjoint_left]
        intro q hq hq'
        obtain ⟨i', rfl, hi'⟩ := β.P0_sub j q hq
        change (ψ.vertexPartition (β.x j)).Rel (β.a j) i' at hi'
        rw [SheetPartition.mem_block_iff, liftPart_rel_old_old] at hq'
        rw [hx] at hi'
        exact hi (hq'.trans hi'.symm)
      rw [blockCountWithin_blockPart_of_disjoint hdisj, liftPart_blockCard_old]
  rw [Finset.sum_congr rfl hTerm]
  have hOld := hRH v i
  have hAtMost : (∑ j ∈ J, (if Q.Rel i (β.a j) then (((β.chain j).P 0).card : ℤ) - 1 else 0)) ≤
      (∑ edge ∈ GluingDatum.incidentEdges v,
        ((ψ.edgePartition edge).blockCountWithin Q i : ℤ)) - 2 -
        (Q.blockCard i : ℤ) * (((GluingDatum.incidentEdges v).card : ℤ) - 2) := by
    by_cases hEx : ∃ j ∈ J, Q.Rel i (β.a j)
    · obtain ⟨j, hj, hi⟩ := hEx
      have hx : β.x j = v := (Finset.mem_filter.mp hj).2
      rw [Finset.sum_eq_single j]
      · rw [ite_eq_left hi]
        have h := hRam j
        unfold MarkedCount.markRamification GluingDatum.localRamification at h
        change ((β.chain j).P 0).card - 1 ≤
          (∑ edge ∈ GluingDatum.incidentEdges (β.x j),
            ((ψ.edgePartition edge).blockCountWithin (ψ.vertexPartition (β.x j)) (β.a j) : ℤ)) -
            2 - ((ψ.vertexPartition (β.x j)).blockCard (β.a j) : ℤ) *
              (((GluingDatum.incidentEdges (β.x j)).card : ℤ) - 2) at h
        rw [hx, ← hQ] at h
        have hBC : ∀ fine : SheetPartition d',
            fine.blockCountWithin Q (β.a j) = fine.blockCountWithin Q i := fun fine ↦
          ContractionRamification.blockCountWithin_congr fine Q hi.symm
        have hCard : Q.blockCard (β.a j) = Q.blockCard i :=
          ContractionRamification.blockCard_congr Q hi.symm
        simp only [hBC, hCard] at h
        exact h
      · intro j' hj' hne
        have hx' : β.x j' = v := (Finset.mem_filter.mp hj').2
        refine ite_eq_right fun hi' ↦ hne ?_
        exact β.mark_unique hInj hx' hx hi' hi
      · intro h; exact absurd hj h
    · push Not at hEx
      rw [Finset.sum_eq_zero fun j hj ↦ ite_eq_right (hEx j hj)]
      linarith
  have hJ : (∑ j ∈ J, ((Q.blockCard i : ℤ) -
      (if Q.Rel i (β.a j) then (((β.chain j).P 0).card : ℤ) - 1 else 0))) =
      (J.card : ℤ) * Q.blockCard i -
        ∑ j ∈ J, (if Q.Rel i (β.a j) then (((β.chain j).P 0).card : ℤ) - 1 else 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hJ]
  push_cast
  nlinarith

/-- Riemann--Hurwitz at an old vertex, at a new sheet: a singleton. -/
theorem riemannHurwitz_new (v : T.V) (n : N) :
    (∑ e ∈ GluingDatum.incidentEdges (oldV c β.x v),
      ((β.regrowDatum.edgePartition e).blockCountWithin
        (β.regrowDatum.vertexPartition (oldV c β.x v)) (new β.e n) : ℤ)) - 2 ≥
    ((β.regrowDatum.vertexPartition (oldV c β.x v)).blockCard (new β.e n) : ℤ) *
      (((GluingDatum.incidentEdges (oldV c β.x v)).card : ℤ) - 2) := by
  have h1 : ∀ e : (catTarget c T β.x).edges,
      (β.regrowDatum.edgePartition e).blockCountWithin
        (β.regrowDatum.vertexPartition (oldV c β.x v)) (new β.e n) = 1 := fun e ↦
    blockCountWithin_of_blockCard_eq_one _ (by rw [vp_oldV, liftPart_blockCard_new])
  have h2 : (∑ e ∈ GluingDatum.incidentEdges (oldV c β.x v),
      ((β.regrowDatum.edgePartition e).blockCountWithin
        (β.regrowDatum.vertexPartition (oldV c β.x v)) (new β.e n) : ℤ)) =
      (GluingDatum.incidentEdges (oldV c β.x v)).card := by
    rw [Finset.sum_congr rfl fun e _ ↦ by rw [h1 e]]
    simp
  rw [h2, vp_oldV, liftPart_blockCard_new]
  push_cast
  linarith

/-- The residual of Riemann--Hurwitz at a block vertex of a tail. -/
theorem blockCountWithin_tail (j : Fin k) (w : TailV (c j)) {s : CatSlot (c j)}
    (hs : s ∈ incSlots w) {q : Fin d} (hq : q ∈ β.vB ⟨j, w⟩) :
    ((blockPart (β.eB ⟨j, s⟩) (β.eA ⟨j, s⟩)).blockCountWithin
      (blockPart (β.vB ⟨j, w⟩) (β.vA ⟨j, w⟩)) q : ℤ) =
      (β.vB ⟨j, w⟩).card - (β.eB ⟨j, s⟩).card + (if (β.eB ⟨j, s⟩).Nonempty then 1 else 0) := by
  have hsub : β.eB ⟨j, s⟩ ⊆ β.vB ⟨j, w⟩ := by
    rcases (mem_incSlots w s).mp hs with h | h
    · exact β.eB_sub_vB_tail (t := ⟨j, s⟩) h
    · have := β.eB_sub_vB_head ⟨j, s⟩
      rw [h] at this
      exact this
  have h := blockCountWithin_blockPart_blockPart (β.eA_anchored ⟨j, s⟩) (β.vA_anchored ⟨j, w⟩)
    hsub hq
  have : ((if (β.eB ⟨j, s⟩).Nonempty then 1 else 0 : ℕ) : ℤ) =
      if (β.eB ⟨j, s⟩).Nonempty then 1 else 0 := by split_ifs <;> rfl
  rw [← this]
  omega

/-- Riemann--Hurwitz at a tail vertex. -/
theorem riemannHurwitz_tail (j : Fin k) (w : TailV (c j)) (q : Fin d) :
    (∑ e ∈ GluingDatum.incidentEdges (tailV c β.x ⟨j, w⟩),
      ((β.regrowDatum.edgePartition e).blockCountWithin
        (β.regrowDatum.vertexPartition (tailV c β.x ⟨j, w⟩)) q : ℤ)) - 2 ≥
    ((β.regrowDatum.vertexPartition (tailV c β.x ⟨j, w⟩)).blockCard q : ℤ) *
      (((GluingDatum.incidentEdges (tailV c β.x ⟨j, w⟩)).card : ℤ) - 2) := by
  classical
  rw [sum_incidentEdges_tailV, card_incidentEdges_tailV]
  simp only [ep_tailE, vp_tailV]
  by_cases hq : q ∈ β.vB ⟨j, w⟩
  · rw [blockPart_blockCard_of_mem (β.vA_anchored _) hq,
      Finset.sum_congr rfl fun s hs ↦ β.blockCountWithin_tail j w hs hq]
    have hv := β.valid j
    rcases TailV.cases w with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [incSlots_spine]
      have h1 : path i.castSucc ∉ ({path i.succ, bridge i} : Finset (CatSlot (c j))) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, path_inj, path_ne_bridge, or_false]
        intro h; have := congrArg Fin.val h; simp at this
      rw [Finset.sum_insert h1, Finset.sum_pair (path_ne_bridge _ _), Finset.card_insert_of_notMem h1,
        Finset.card_pair (path_ne_bridge _ _)]
      have hS := hv.card_S i
      have hne1 : (β.eB ⟨j, path i.castSucc⟩).Nonempty := hv.P_nonempty i.castSucc
      have hne2 : (β.eB ⟨j, path i.succ⟩).Nonempty := hv.P_nonempty i.succ
      have hneQ : (β.eB ⟨j, bridge i⟩).Nonempty := by
        change ((β.chain j).Q i).Nonempty
        rw [← Finset.card_pos, hv.card_Q]; omega
      rw [ite_eq_left hne1, ite_eq_left hne2, ite_eq_left hneQ]
      have e1 : (β.eB ⟨j, path i.castSucc⟩).card = ((β.chain j).P i.castSucc).card := rfl
      have e2 : (β.eB ⟨j, path i.succ⟩).card = ((β.chain j).P i.succ).card := rfl
      have e3 : (β.eB ⟨j, bridge i⟩).card = 2 := hv.card_Q i
      have e4 : (β.vB ⟨j, spine i⟩).card = ((β.chain j).S i).card := rfl
      rw [e1, e2, e3, e4]
      push_cast
      omega
    · rw [incSlots_bulb, Finset.sum_pair (inBridge_ne_loop _ _),
        Finset.card_pair (inBridge_ne_loop _ _)]
      have hne : (β.eB ⟨j, inBridge i⟩).Nonempty := hv.R_nonempty i
      have hnl : ¬ (β.eB ⟨j, loop i⟩).Nonempty := by
        change ¬ (∅ : Finset (Fin d)).Nonempty; simp
      rw [ite_eq_left hne, ite_eq_right hnl]
      have e1 : (β.eB ⟨j, inBridge i⟩).card = 2 := hv.card_R i
      have e2 : (β.eB ⟨j, loop i⟩).card = 0 := rfl
      have e3 : (β.vB ⟨j, bulb i⟩).card = 2 := hv.card_R i
      rw [e1, e2, e3]
      norm_num
    · rw [incSlots_tip, Finset.sum_singleton, Finset.card_singleton]
      have hnl : ¬ (β.eB ⟨j, loop i⟩).Nonempty := by
        change ¬ (∅ : Finset (Fin d)).Nonempty; simp
      rw [ite_eq_right hnl]
      have e2 : (β.eB ⟨j, loop i⟩).card = 0 := rfl
      have e3 : (β.vB ⟨j, tip i⟩).card = 2 := hv.card_R i
      rw [e2, e3]
      norm_num
  · rw [blockPart_blockCard_of_not_mem (β.vA_anchored _) hq]
    have h1 : ∀ s ∈ incSlots w, ((blockPart (β.eB ⟨j, s⟩) (β.eA ⟨j, s⟩)).blockCountWithin
        (blockPart (β.vB ⟨j, w⟩) (β.vA ⟨j, w⟩)) q : ℤ) = 1 := fun s _ ↦ by
      rw [blockCountWithin_of_blockCard_eq_one _
        (blockPart_blockCard_of_not_mem (β.vA_anchored _) hq)]
      rfl
    rw [Finset.sum_congr rfl h1]
    simp

include hInj hRam in
/-- **Riemann--Hurwitz for the regrowth**: unchanged over `T` away from the
marks, `r⁺ = r_ψ - (|P_1| - 1)` at a mark, `0` at a spine block, `1` at a bulb, `2` at a tip. -/
theorem riemannHurwitz_regrowDatum (hRH : ψ.RiemannHurwitz) : β.regrowDatum.RiemannHurwitz := by
  intro v q
  rcases vertex_cases c β.x v with ⟨w, rfl⟩ | ⟨⟨j, w⟩, rfl⟩
  · rcases sheet_cases (e := β.e) q with ⟨i, rfl⟩ | ⟨n, rfl⟩
    · exact β.riemannHurwitz_old hInj hRam hRH w i
    · exact β.riemannHurwitz_new w n
  · exact β.riemannHurwitz_tail j w q

end RH

/-! ## 4.  Connectedness -/

open GenusSixExistence.Tripod.Gluing in
/-- **The regrown source is connected**: the old sheets through `ψ`, every
sheet along the (connected) target, and every new sheet through the block of the spine vertex
where it enters its chain. -/
theorem connected_regrowDatum (hψ : ψ.Connected) (hT : graph_connected T) :
    β.regrowDatum.Connected := by
  set R := β.regrowDatum
  have hOld : ∀ X Y : ψ.SourceVertex, (srcGraph R).Reachable (β.psiSV X) (β.psiSV Y) := by
    refine reachable_of_sourceEdges ψ (srcGraph R) β.psiSV (fun e i ↦ ?_) hψ
    have h := adj_sourceEndpoint R (oldE c β.x e) (old β.e i)
    rw [oldE_ends] at h
    change (srcGraph R).Adj (R.sourceEndpoint (oldV c β.x (e : T.V × T.V).1) (old β.e i))
      (R.sourceEndpoint (oldV c β.x (e : T.V × T.V).2) (old β.e i)) at h
    rw [sourceEndpoint_oldV_old, sourceEndpoint_oldV_old] at h
    exact h.reachable
  have hSheet : ∀ (q : Fin d) (u v : (catTarget c T β.x).V),
      (srcGraph R).Reachable (R.sourceEndpoint u q) (R.sourceEndpoint v q) := fun q ↦
    reachable_of_targetEdges (srcGraph R) (fun v ↦ R.sourceEndpoint v q)
      (fun e ↦ (adj_sourceEndpoint R e q).reachable) (catTarget_connected c β.x hT)
  obtain ⟨v₀⟩ := T.instNonempty
  let X₀ : R.SourceVertex := β.psiSV (ψ.sourceEndpoint v₀ ⟨0, ψ.degree_pos⟩)
  have hChain : ∀ (j : Fin k) (m : ℕ) (i : Fin (c j + 1)), i.val = m → ∀ q ∈ (β.chain j).P i,
      (srcGraph R).Reachable X₀ (R.sourceEndpoint (oldV c β.x (β.x j)) q) := by
    intro j m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i hi q hq
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · obtain ⟨i'', rfl, -⟩ := β.P0_sub j q hq
        rw [sourceEndpoint_oldV_old]
        exact hOld _ _
      · obtain ⟨p, hp⟩ := (β.valid j).P_nonempty i'.castSucc
        have hp' := ih i'.castSucc.val (by simp at hi ⊢; omega) i'.castSucc rfl p hp
        have hqS : q ∈ β.vB ⟨j, spine i'⟩ := TailChain.P_succ_sub_S i' hq
        have hpS : p ∈ β.vB ⟨j, spine i'⟩ := TailChain.P_castSucc_sub_S i' hp
        have heq : R.sourceEndpoint (tailV c β.x ⟨j, spine i'⟩) p =
            R.sourceEndpoint (tailV c β.x ⟨j, spine i'⟩) q := by
          change β.tailSV _ p = β.tailSV _ q
          rw [β.tailSV_of_mem hqS, β.tailSV_of_mem hpS]
        refine hp'.trans ((hSheet p _ (tailV c β.x ⟨j, spine i'⟩)).trans ?_)
        rw [heq]
        exact hSheet q _ _
  have hAll : ∀ q : Fin d, ∃ u, (srcGraph R).Reachable X₀ (R.sourceEndpoint u q) := by
    intro q
    rcases sheet_cases (e := β.e) q with ⟨i, rfl⟩ | ⟨n, rfl⟩
    · refine ⟨oldV c β.x v₀, ?_⟩
      rw [sourceEndpoint_oldV_old]
      exact hOld _ _
    · obtain ⟨j, i, hi⟩ := β.new_used n
      exact ⟨_, hChain j _ i rfl _ hi⟩
  refine connected_of_reachable R X₀ fun X ↦ ?_
  obtain ⟨u, hu⟩ := hAll X.1.2
  rw [← R.sourceEndpoint_self X]
  exact hu.trans (hSheet _ _ _)

/-! ## 5.  The genus of the regrown source -/

variable [Fintype N]

theorem card_sourceVertex_regrowDatum :
    (Fintype.card β.regrowDatum.SourceVertex : ℤ) =
      Fintype.card ψ.SourceVertex + Fintype.card T.V * Fintype.card N +
        ∑ w : TV c, ((d : ℤ) + 1 - (β.vB w).card) := by
  rw [MarkedCount.Regrow.card_sourceVertex, MarkedCount.Regrow.card_sourceVertex]
  change ((∑ v : T.V ⊕ TV c, Fintype.card (β.regrowDatum.vertexPartition v).Blocks : ℕ) : ℤ) = _
  rw [Fintype.sum_sum_type]
  push_cast
  have h1 : ∀ v : T.V, (Fintype.card (β.regrowDatum.vertexPartition (Sum.inl v)).Blocks : ℤ) =
      Fintype.card (ψ.vertexPartition v).Blocks + Fintype.card N := fun v ↦ by
    have := card_blocks_liftPart (e := β.e) (ψ.vertexPartition v)
    exact_mod_cast this
  have h2 : ∀ w : TV c, (Fintype.card (β.regrowDatum.vertexPartition (Sum.inr w)).Blocks : ℤ) =
      (d : ℤ) + 1 - (β.vB w).card := fun w ↦ by
    have := card_blocks_blockPart (β.vA_anchored w)
    rw [ite_eq_left ⟨β.vA w, β.vA_mem w⟩] at this
    change (Fintype.card (blockPart (β.vB w) (β.vA w)).Blocks : ℤ) = _
    omega
  rw [Finset.sum_congr rfl fun v _ ↦ h1 v, Finset.sum_congr rfl fun w _ ↦ h2 w,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem card_sourceEdge_regrowDatum :
    (Fintype.card β.regrowDatum.SourceEdge : ℤ) =
      Fintype.card ψ.SourceEdge + Multiset.card T.edges * Fintype.card N +
        ∑ t : TE c, ((d : ℤ) + (if (β.eB t).Nonempty then 1 else 0) - (β.eB t).card) := by
  classical
  rw [MarkedCount.Regrow.card_sourceEdge, MarkedCount.Regrow.card_sourceEdge, sum_edges]
  push_cast
  have h1 : ∀ ε : T.edges, (Fintype.card (β.regrowDatum.edgePartition (oldE c β.x ε)).Blocks : ℤ) =
      Fintype.card (ψ.edgePartition ε).Blocks + Fintype.card N := fun ε ↦ by
    rw [ep_oldE]
    have := card_blocks_liftPart (e := β.e) (ψ.edgePartition ε)
    exact_mod_cast this
  have h2 : ∀ t : TE c, (Fintype.card (β.regrowDatum.edgePartition (tailE c β.x t)).Blocks : ℤ) =
      (d : ℤ) + (if (β.eB t).Nonempty then 1 else 0) - (β.eB t).card := fun t ↦ by
    rw [ep_tailE]
    have := card_blocks_blockPart (β.eA_anchored t)
    have hc : ((if (β.eB t).Nonempty then 1 else 0 : ℕ) : ℤ) =
        if (β.eB t).Nonempty then 1 else 0 := by split_ifs <;> rfl
    rw [← hc]
    omega
  rw [Finset.sum_congr rfl fun ε _ ↦ h1 ε, Finset.sum_congr rfl fun t _ ↦ h2 t,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Multiset.card_coe]

/-- **The genus of the regrown source**: that of `ψ`, plus the tails' contributions, minus one per
new sheet (each is a copy of the tree `T` attached once). -/
theorem genus_regrowDatum (hT : genus T = 0) :
    genus β.regrowDatum.sourceGraph =
      genus ψ.sourceGraph - Fintype.card N + ∑ j, (β.chain j).genusContribution := by
  classical
  rw [MarkedCount.Regrow.genus_sourceGraph, MarkedCount.Regrow.genus_sourceGraph,
    card_sourceEdge_regrowDatum, card_sourceVertex_regrowDatum]
  have hT' : (Multiset.card T.edges : ℤ) = Fintype.card T.V - 1 := by
    unfold genus at hT; omega
  have hsum : ∑ t : TE c, ((d : ℤ) + (if (β.eB t).Nonempty then 1 else 0) - (β.eB t).card) -
      ∑ w : TV c, ((d : ℤ) + 1 - (β.vB w).card) = ∑ j, (β.chain j).genusContribution := by
    rw [Fintype.sum_sigma, Fintype.sum_sigma, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    unfold TailChain.genusContribution
    have hcard : (Fintype.card (CatSlot (c j)) : ℤ) = Fintype.card (TailV (c j)) := by
      rw [card_catSlot, TailV.card]
    have e1 : ∑ s : CatSlot (c j), ((d : ℤ) + (if (β.eB ⟨j, s⟩).Nonempty then 1 else 0) -
        (β.eB ⟨j, s⟩).card) = Fintype.card (CatSlot (c j)) * d +
        ∑ s : CatSlot (c j), ((if ((β.chain j).eB s).Nonempty then 1 else 0 : ℤ) -
          ((β.chain j).eB s).card) := by
      have h : ∀ s : CatSlot (c j), ((d : ℤ) + (if (β.eB ⟨j, s⟩).Nonempty then 1 else 0) -
          (β.eB ⟨j, s⟩).card) = (d : ℤ) + ((if ((β.chain j).eB s).Nonempty then 1 else 0 : ℤ) -
            ((β.chain j).eB s).card) := fun s ↦ by
        rw [show β.eB ⟨j, s⟩ = (β.chain j).eB s from rfl]; ring
      rw [Finset.sum_congr rfl fun s _ ↦ h s, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    have e2 : ∑ w : TailV (c j), ((d : ℤ) + 1 - (β.vB ⟨j, w⟩).card) =
        Fintype.card (TailV (c j)) * d -
        ∑ w : TailV (c j), (((β.chain j).vB w).card - 1 : ℤ) := by
      have h : ∀ w : TailV (c j), ((d : ℤ) + 1 - (β.vB ⟨j, w⟩).card) =
          (d : ℤ) - (((β.chain j).vB w).card - 1 : ℤ) := fun w ↦ by
        rw [show β.vB ⟨j, w⟩ = (β.chain j).vB w from rfl]; ring
      rw [Finset.sum_congr rfl fun w _ ↦ h w, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    rw [e1, e2, hcard]
    ring
  linear_combination hsum + (Fintype.card N : ℤ) * hT'

end CatBranching

end

end DraismaVargas.Count.MarkedCountGeneral.CatRegrow
