module

public import DraismaVargasMarkedCount.MarkedCountGeneral.DropExtend
public import DraismaVargasCount.W4LimitContraction

@[expose] public section

/-!
# The drop lemma: subdividing a target edge (the datum of the lift, I5)

The inverse of module `DropContract`, on data: a target edge `t` of a gluing datum `data` on a tree,
with an end `w`, is **subdivided** by the public resolution expansion
(`GlobalResolution.datum`) at `w`, moving `t` to the fresh vertex `x'` (`place t`) and giving
`x'` and the new edge `c' = (w, x')` the partition of `t` (`res`):

* the expanded target `T'` is a tree (`TargetExpansion.graph_connected`, `graph_genus`);
* `x'` is divalent of change zero, with incident edges `c'` and the moved `t`
  (`divalentZero`), so `site` is a contraction site in the sense of `DropContract`;
* contracting `c'` gives back `data` (`contractIso`): the public `W4LimitContraction.limitIso`
  onto `data` with the partition at `w` replaced by its join with that of `t` (`base'`), followed
  by the block normalization of that partition (`normIso`); its source dictionaries undo the lifts
  of source vertices and edges (`contractIso_vmap`, `contractIso_emap`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCountGeneral.DivalentContraction

namespace DivalentExpansion

variable {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)

/-- The placement moving `t` (and only `t`) to the fresh vertex. -/
def place (t : target.edges) : target.edges → Bool := fun e ↦ decide (e = t)

variable {w : target.V} {t : target.edges} (hw : t ∈ incidentEdges w)

/-- **The local resolution of the subdivision**: `P_w` at the retained wall, `P_t` at the fresh
vertex and on the new edge. -/
def res : ResolutionM11.LocalResolution degree where
  left := data.vertexPartition w
  right := data.edgePartition t
  newEdge := data.edgePartition t
  edge_refines_left := edgePartition_refines_of_mem_incidentEdges data w t hw
  edge_refines_right := SheetPartition.Refines.refl _

/-- The exterior compatibility of the subdivision. -/
theorem compat : GlobalResolution.OldCompatible data w (place t) (res data hw) := by
  refine GlobalResolution.oldCompatible_of_wall _ _ _ _ fun e he ↦ ?_
  by_cases h : e = t
  · subst h
    have : place e e = true := decide_eq_true rfl
    rw [this, ite_eq_left rfl]
    exact SheetPartition.Refines.refl _
  · have : place t e = false := decide_eq_false h
    rw [this]
    exact edgePartition_refines_of_mem_incidentEdges data w e ((mem_incidentEdges_iff _ _).mpr he)

/-- The subdivided target. -/
abbrev T' : CFGraph := TargetExpansion.graph target w (place t)

/-- **The subdivided datum.** -/
noncomputable abbrev D' : GluingDatum (T' (w := w) (t := t)) degree :=
  GlobalResolution.datum data w (place t) (res data hw) (compat data hw)

/-- The new edge `c' = (w, x')`. -/
noncomputable abbrev c' : (T' (w := w) (t := t)).edges := occurrenceEquiv target w (place t) none

/-- The moved copy of `t`. -/
noncomputable abbrev tM : (T' (w := w) (t := t)).edges :=
  occurrenceEquiv target w (place t) (some t)

/-- The fresh vertex `x'`. -/
abbrev x' : (T' (w := w) (t := t)).V := freshVertex target

/-- The new edge joins the retained copy of `w` to `x'`. -/
theorem c'_ends : ((c' (w := w) (t := t) : (T' (w := w) (t := t)).edges) :
    (T' (w := w) (t := t)).V × (T' (w := w) (t := t)).V) = (oldVertex target w, freshVertex target) :=
  occurrenceEquiv_none target w (place t)

/-- The new edge is not the moved `t`. -/
theorem c'_ne_tM : (c' (w := w) (t := t)) ≠ tM := fun h ↦
  Option.some_ne_none t ((occurrenceEquiv target w (place t)).injective h).symm

include hw in
/-- **The edges at `x'`**: `c'` and the moved `t`. -/
theorem mem_incident_x'_iff (e : (T' (w := w) (t := t)).edges) :
    e ∈ incidentEdges (x' (w := w) (t := t)) ↔ e = c' ∨ e = tM := by
  obtain ⟨label, rfl⟩ := (occurrenceEquiv target w (place t)).surjective e
  rw [mem_incidentEdges_iff]
  cases label with
  | none =>
    simp only [occurrenceEquiv_none, newEnds, true_or, iff_true]
    exact Or.inr rfl
  | some e₀ =>
    rw [occurrenceEquiv_some]
    change (oldEnds target w (place t) e₀).1 = freshVertex target ∨
      (oldEnds target w (place t) e₀).2 = freshVertex target ↔ _
    rw [oldEnds_incident_freshVertex_iff]
    constructor
    · rintro ⟨-, h⟩
      right
      have : e₀ = t := of_decide_eq_true h
      rw [this]
    · rintro (h | h)
      · exact absurd ((occurrenceEquiv target w (place t)).injective h) (Option.some_ne_none _)
      · have h' : e₀ = t := Option.some_injective _ ((occurrenceEquiv target w (place t)).injective h)
        subst h'
        exact ⟨(mem_incidentEdges_iff _ _).mp hw, decide_eq_true rfl⟩

include hw in
/-- The edges at `x'`, as a set. -/
theorem incident_x'_eq : incidentEdges (x' (w := w) (t := t)) = {c', tM} := by
  ext e
  rw [mem_incident_x'_iff hw, Finset.mem_insert, Finset.mem_singleton]

include hw in
/-- `x'` is divalent. -/
theorem card_incident_x' : (incidentEdges (x' (w := w) (t := t))).card = 2 := by
  rw [incident_x'_eq hw, Finset.card_pair c'_ne_tM]

/-! ### The partitions -/

/-- The partition at `x'` is that of `t`. -/
theorem vp_x' : (D' data hw).vertexPartition x' = data.edgePartition t := rfl

/-- The partition at the retained copy of `w` is that of `w`. -/
theorem vp_old_w : (D' data hw).vertexPartition (oldVertex target w) = data.vertexPartition w :=
  GlobalResolution.expandedVertexPartition_old_wall _ _ _

/-- The partitions away from `w` are unchanged. -/
theorem vp_old_of_ne {v : target.V} (hv : v ≠ w) :
    (D' data hw).vertexPartition (oldVertex target v) = data.vertexPartition v :=
  GlobalResolution.expandedVertexPartition_old_of_ne _ _ _ _ hv

/-- The partition of the new edge is that of `t`. -/
theorem ep_c' : (D' data hw).edgePartition c' = data.edgePartition t :=
  GlobalResolution.expandedEdgePartition_new _ _ _ _

/-- The partitions of the old occurrences are unchanged. -/
theorem ep_old (e : target.edges) :
    (D' data hw).edgePartition (occurrenceEquiv target w (place t) (some e)) = data.edgePartition e :=
  GlobalResolution.expandedEdgePartition_old _ _ _ _ _

/-- **`x'` is divalent of change zero.** -/
theorem divalentZero : DivalentZero (D' data hw) x' := by
  refine ⟨card_incident_x' hw, fun sheet ↦ ?_⟩
  unfold GluingDatum.localRamification
  rw [card_incident_x' hw, incident_x'_eq hw, Finset.sum_pair c'_ne_tM, ep_c', ep_old, vp_x',
    SheetPartition.blockCountWithin_self]
  norm_num

/-! ### The target -/

variable (hConn : graph_connected target) (hGenus : genus target = 0)

include hConn in
/-- The subdivided target is connected. -/
theorem T'_connected : graph_connected (T' (w := w) (t := t)) :=
  TargetExpansion.graph_connected target w (place t) hConn

include hGenus in
/-- The subdivided target is a tree. -/
theorem T'_genus : genus (T' (w := w) (t := t)) = 0 := by
  rw [TargetExpansion.graph_genus]; exact hGenus

include hConn hGenus in
/-- The new edge is the only edge between its ends. -/
theorem hOne' : num_edges (T' (w := w) (t := t))
    ((c' (w := w) (t := t) : (T' (w := w) (t := t)).edges) :
      (T' (w := w) (t := t)).V × (T' (w := w) (t := t)).V).1
    ((c' (w := w) (t := t) : (T' (w := w) (t := t)).edges) :
      (T' (w := w) (t := t)).V × (T' (w := w) (t := t)).V).2 = 1 :=
  IteratedContraction.num_edges_eq_one_of_genus_zero_of_connected _ (T'_connected hConn)
    (T'_genus hGenus) _

/-- **The contraction site of the subdivision.** -/
noncomputable def site : Site (D' data hw) where
  x := x'
  c := c'
  hOne := hOne' hConn hGenus
  mem := (mem_incident_x'_iff hw _).mpr (Or.inl rfl)
  div := divalentZero data hw

/-- The partition at every retained copy is the old one. -/
theorem vp_old (v : target.V) :
    (D' data hw).vertexPartition (oldVertex target v) = data.vertexPartition v := by
  by_cases h : v = w
  · subst h; exact vp_old_w data hw
  · exact vp_old_of_ne data hw h

/-- The site's far end of `c'` is the retained copy of `w`. -/
theorem site_w : (site data hw hConn hGenus).w = oldVertex target w := by
  unfold Site.w
  have h : (site data hw hConn hGenus).x ≠
      ((site data hw hConn hGenus).c : (T' (w := w) (t := t)).V × (T' (w := w) (t := t)).V).1 := by
    change freshVertex target ≠ ((c' (w := w) (t := t) : (T' (w := w) (t := t)).edges) :
      (T' (w := w) (t := t)).V × (T' (w := w) (t := t)).V).1
    rw [c'_ends]
    exact Sum.inr_ne_inl
  rw [ite_eq_right h]
  exact congrArg Prod.fst c'_ends

/-- The other edge at `x'` is the moved `t`. -/
theorem site_other : (site data hw hConn hGenus).other = tM := by
  rcases (mem_incident_x'_iff hw _).mp (site data hw hConn hGenus).other_mem with h | h
  · exact absurd h (site data hw hConn hGenus).other_ne
  · exact h

/-! ### Validity -/

/-- The resolution contracts to the partition of `w`. -/
theorem contractsTo : (res data hw).ContractsTo (data.vertexPartition w) := by
  intro i j
  constructor
  · exact fun h ↦ Relation.EqvGen.rel _ _ (Or.inl h)
  · intro h
    induction h with
    | rel a b h =>
      rcases h with h | h
      · exact h
      · exact edgePartition_refines_of_mem_incidentEdges data w t hw a b h
    | refl a => exact rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

include hw in
/-- Only `t` moves to `x'`. -/
theorem wallAssigned_true :
    wallEdgesAssigned target w (place t) true = {t} := by
  ext e
  rw [mem_wallEdgesAssigned, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩; exact of_decide_eq_true h
  · rintro rfl; exact ⟨(mem_incidentEdges_iff _ _).mp hw, decide_eq_true rfl⟩

include hw in
/-- The edges at `w`: `t`, then the ones that stay. -/
theorem incident_w_val : ((t :: (wallEdgesAssigned target w (place t) false).toList :
    List target.edges) : Multiset target.edges) = (incidentEdges w).val := by
  have hEq : incidentEdges w = insert t (wallEdgesAssigned target w (place t) false) := by
    ext e
    rw [Finset.mem_insert, mem_wallEdgesAssigned, mem_incidentEdges_iff]
    constructor
    · intro h
      by_cases het : e = t
      · exact Or.inl het
      · exact Or.inr ⟨h, decide_eq_false het⟩
    · rintro (rfl | ⟨h, -⟩)
      · exact (mem_incidentEdges_iff _ _).mp hw
      · exact h
  have hNot : t ∉ wallEdgesAssigned target w (place t) false := by
    rw [mem_wallEdgesAssigned]
    rintro ⟨-, h⟩
    exact absurd h (by simp [place])
  rw [hEq, Finset.insert_val_of_notMem hNot, ← Multiset.cons_coe, Finset.coe_toList]

omit hConn hGenus in
/-- **The subdivided datum is valid.** -/
theorem valid (hValid : data.Valid) : (D' data hw).Valid := by
  refine GlobalResolution.datum_valid_of_assignedOccurrences data w (place t) (res data hw)
    (compat data hw) (contractsTo data hw) hValid
    (wallEdgesAssigned target w (place t) false).toList [t] (by simp)
    (by rw [wallAssigned_true hw]; rfl) ?_ ?_
  · have h := (data.riemannHurwitzAtTargetVertex_iff_incidentList w _ (incident_w_val hw)).mp
      (hValid.2 w)
    simpa [res] using h
  · intro i
    simp [res, SheetPartition.blockCountWithin_self]

/-! ### Contracting `c'` gives back `data` -/

/-- The join at `w`. -/
noncomputable abbrev J : SheetPartition degree :=
  SheetPartition.join (data.vertexPartition w) (data.edgePartition t)

include hw in
/-- The join at `w` has the blocks of `w`. -/
theorem J_sameBlocks : (J data (w := w) (t := t)).SameBlocks (data.vertexPartition w) := by
  intro i j
  constructor
  · exact (SheetPartition.join_refines_iff _ _ _).mpr ⟨SheetPartition.Refines.refl _,
      edgePartition_refines_of_mem_incidentEdges data w t hw⟩ i j
  · exact SheetPartition.left_refines_join _ _ i j

/-- `data` with the partition at `w` replaced by its join with that of `t`. -/
noncomputable def base' : GluingDatum target degree where
  degree_pos := data.degree_pos
  vertexPartition := Function.update data.vertexPartition w (J data (w := w) (t := t))
  edgePartition := data.edgePartition
  refines_left e := by
    intro i j hij
    rw [Function.update_apply]
    split_ifs with h
    · exact SheetPartition.left_refines_join _ _ i j (h ▸ data.refines_left e i j hij)
    · exact data.refines_left e i j hij
  refines_right e := by
    intro i j hij
    rw [Function.update_apply]
    split_ifs with h
    · exact SheetPartition.left_refines_join _ _ i j (h ▸ data.refines_right e i j hij)
    · exact data.refines_right e i j hij

/-- The merge hypothesis of `W4LimitContraction.limitIso`. -/
theorem limMerge : SheetPartition.join ((D' data hw).vertexPartition (oldVertex target w))
    ((D' data hw).vertexPartition (freshVertex target)) =
      (base' data (w := w) (t := t)).vertexPartition w := by
  rw [vp_old_w]
  show _ = Function.update data.vertexPartition w (J data (w := w) (t := t)) w
  rw [Function.update_self]
  rfl

/-- The old-vertex hypothesis of `W4LimitContraction.limitIso`. -/
theorem limOld : ∀ v : target.V, v ≠ w →
    (D' data hw).vertexPartition (oldVertex target v) = (base' data (w := w) (t := t)).vertexPartition v :=
  fun v hv ↦ by rw [vp_old_of_ne data hw hv]; exact (Function.update_of_ne hv _ _).symm

/-- The old-edge hypothesis of `W4LimitContraction.limitIso`. -/
theorem limEdge : ∀ e : target.edges,
    (D' data hw).edgePartition (occurrenceEquiv target w (place t) (some e)) =
      (base' data (w := w) (t := t)).edgePartition e :=
  fun e ↦ ep_old data hw e

/-- The literal limit of the subdivision. -/
noncomputable def limIso : GeometricDatumIso (site data hw hConn hGenus).D (base' data (w := w) (t := t)) :=
  W4LimitContraction.limitIso (hc := rfl) (fst_ne_snd (c' (w := w) (t := t))) (hOne' hConn hGenus)
    (hcontract := rfl) (base' data (w := w) (t := t)) (D' data hw) (limMerge data hw) (limOld data hw)
    (limEdge data hw)

include hw in
/-- The block normalization at `w`. -/
noncomputable def β : Equiv.Perm (Fin degree) :=
  PartitionNormalization.permutation (J data (w := w) (t := t)) (data.vertexPartition w)
    (J_sameBlocks data hw)

include hw in
/-- **The normalization of `base'` back to `data`.** -/
noncomputable def normIso : GeometricDatumIso (base' data (w := w) (t := t)) data where
  targetVertex := Equiv.refl _
  targetEdge := Equiv.refl _
  ends _ := Or.inl rfl
  vertexPerm v := if v = w then β data hw else Equiv.refl _
  edgePerm _ := Equiv.refl _
  vertexPartition v := by
    by_cases h : v = w
    · subst h
      rw [ite_eq_left rfl]
      change data.vertexPartition v =
        ((Function.update data.vertexPartition v (J data (w := v) (t := t))) v).relabel _
      rw [Function.update_self]
      exact (PartitionNormalization.relabel_eq _ _ _).symm
    · rw [ite_eq_right h, Transport.DatumIso.relabel_refl]
      exact (Function.update_of_ne h _ _).symm
  edgePartition e := (Transport.DatumIso.relabel_refl _).symm
  compatible e v _ sheet := by
    by_cases h : v = w
    · subst h
      rw [ite_eq_left rfl]
      change (Function.update data.vertexPartition v (J data (w := v) (t := t)) v).Rel _ sheet
      rw [Function.update_self]
      exact PartitionNormalization.permutation_symm_rel _ _ _ sheet
    · rw [ite_eq_right h]
      exact rfl

/-- **Contracting `c'` gives back `data`.** -/
noncomputable def contractIso : GeometricDatumIso (site data hw hConn hGenus).D data :=
  (limIso data hw hConn hGenus).trans (normIso data hw)

/-- The normalization on canonical source vertices. -/
theorem normIso_sourceEndpoint (v : target.V) (i : Fin degree) :
    (normIso data hw).sourceVertexEquiv ((base' data (w := w) (t := t)).sourceEndpoint v i) =
      data.sourceEndpoint v i := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (if v = w then β data hw else Equiv.refl _)
      (((Function.update data.vertexPartition w (J data)) v).repr i) =
        (data.vertexPartition v).repr i
    by_cases h : v = w
    · subst h
      rw [ite_eq_left rfl, Function.update_self]
      exact PartitionNormalization.permutation_repr _ _ _ i
    · rw [ite_eq_right h, Function.update_of_ne h]
      rfl

/-- **The vertex dictionary of the contraction.** -/
theorem contractIso_vmap (X : (D' data hw).SourceVertex) :
    (contractIso data hw hConn hGenus).sourceVertexEquiv ((site data hw hConn hGenus).vmap X) =
      data.sourceEndpoint (contractVertex target w X.1.1) X.1.2 := by
  have h := W4LimitContraction.sourceVertexEquiv_sourceVertexMap (hc := rfl)
    (fst_ne_snd (c' (w := w) (t := t))) (hOne' hConn hGenus) (hcontract := rfl)
    (base' data (w := w) (t := t)) (D' data hw) (limMerge data hw) (limOld data hw)
    (limEdge data hw) X
  exact (congrArg (normIso data hw).sourceVertexEquiv h).trans (normIso_sourceEndpoint data hw _ _)

/-- The lift of a source vertex to the retained copies. -/
noncomputable def liftV (Y : data.SourceVertex) : (D' data hw).SourceVertex :=
  (D' data hw).sourceEndpoint (oldVertex target Y.1.1) Y.1.2

/-- A lifted vertex lies over the retained copy of its target vertex. -/
theorem liftV_target (Y : data.SourceVertex) : (liftV data hw Y).1.1 = oldVertex target Y.1.1 := rfl

/-- **Contracting undoes the lift of a source vertex.** -/
theorem contractIso_vmap_liftV (Y : data.SourceVertex) :
    (contractIso data hw hConn hGenus).sourceVertexEquiv
        ((site data hw hConn hGenus).vmap (liftV data hw Y)) = Y := by
  rw [contractIso_vmap]
  change data.sourceEndpoint Y.1.1 (((D' data hw).vertexPartition (oldVertex target Y.1.1)).repr Y.1.2) = Y
  rw [vp_old, Y.2]
  exact data.sourceEndpoint_self Y

/-- The lift of a source edge to the retained occurrences. -/
noncomputable abbrev liftE (e : data.SourceEdge) : (D' data hw).SourceEdge :=
  GlobalResolution.oldSourceEdge data w (place t) (res data hw) (compat data hw) e

/-- A lifted occurrence is not over the new edge. -/
theorem liftE_ne (e : data.SourceEdge) :
    (liftE data hw e).1.1 ≠ (site data hw hConn hGenus).c := fun h ↦
  Option.some_ne_none e.1.1 ((occurrenceEquiv target w (place t)).injective h)

/-- **The edge dictionary of the contraction.** -/
theorem contractIso_emap (e : data.SourceEdge) :
    (contractIso data hw hConn hGenus).sourceEdgeEquiv
        ((site data hw hConn hGenus).emap ⟨liftE data hw e, liftE_ne data hw hConn hGenus e⟩) = e := by
  apply Subtype.ext
  change (W4LimitContraction.edgeEquiv rfl (fst_ne_snd (c' (w := w) (t := t))) (hOne' hConn hGenus)
    rfl (foldEdge rfl (fst_ne_snd (c' (w := w) (t := t))) (hOne' hConn hGenus)
      ⟨occurrenceEquiv target w (place t) (some e.1.1), _⟩), e.1.2) = e.1
  unfold W4LimitContraction.edgeEquiv
  rw [Equiv.trans_apply]
  unfold foldEdgeEquiv
  rw [Equiv.ofBijective_symm_apply_apply]
  have hS : (⟨occurrenceEquiv target w (place t) (some e.1.1), liftE_ne data hw hConn hGenus e⟩ :
      {f : (T' (w := w) (t := t)).edges // f ≠ c'}) = W4LimitContraction.survivingEquiv rfl e.1.1 :=
    Subtype.ext rfl
  rw [hS, Equiv.symm_apply_apply]

end DivalentExpansion

end DraismaVargas.Count.MarkedCountGeneral
