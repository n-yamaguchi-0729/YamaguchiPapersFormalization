/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import EtaleFundamentalGroups.GaloisCategories.ContinuousHomComparison
public import EtaleFundamentalGroups.GaloisCategories.ConnectedActions
public import EtaleFundamentalGroups.ContinuousActions.RestrictionFullyFaithful
public import Mathlib.Data.List.TFAE
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.Transitive
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Surjectivity criteria for functors of Galois categories

The continuous homomorphism on automorphism groups induced by a functor of
Galois categories is surjective exactly when the functor is fully faithful.
Equivalently, it preserves connected objects, lifts points of connected
objects, or induces bijections on points.
-/

@[expose] public section

universe g g' u₁ u₂ v₁ v₂ w

noncomputable section

open CategoryTheory Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

private theorem exists_open_supergroup
    {G' : Type g'} {G : Type g}
    [Group G'] [TopologicalSpace G'] [CompactSpace G']
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] [T2Space G]
    (h : G' →ₜ* G) (nh : ¬ Function.Surjective h) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧
      h.toMonoidHom.range ≤ U ∧ U ≠ ⊤ := by
  let K : ClosedSubgroup G :=
    { toSubgroup := h.toMonoidHom.range
      isClosed' := by
        change IsClosed (Set.range h)
        exact (isCompact_range h.continuous_toFun).isClosed }
  have hK : K.toSubgroup ≠ ⊤ := by
    intro heq
    apply nh
    exact MonoidHom.range_eq_top.mp heq
  have hnall : ¬ ∀ g : G, g ∈ K := by
    intro hall
    apply hK
    exact eq_top_iff.mpr fun g _ ↦ hall g
  obtain ⟨g, hg⟩ := not_forall.mp hnall
  have hg' :
      g ∉ sInf {N : Subgroup G |
        IsOpen (N : Set G) ∧ K.toSubgroup ≤ N} := by
    rwa [← ProfiniteGrp.closedSubgroup_eq_sInf_open K]
  rw [Subgroup.mem_sInf] at hg'
  push Not at hg'
  obtain ⟨U, ⟨hUopen, hKU⟩, hgU⟩ := hg'
  exact ⟨U, hUopen, hKU,
    fun htop ↦ hgU (htop ▸ Subgroup.mem_top g)⟩

private theorem exists_small_action
    {G' : Type g'} {G : Type g}
    [Group G'] [TopologicalSpace G']
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (h : G' →ₜ* G) (U : Subgroup G)
    (hUopen : IsOpen (U : Set G))
    (hKU : h.toMonoidHom.range ≤ U) (hUne : U ≠ ⊤) :
    ∃ (Y : ContAction FintypeCat.{w} G) (y : Y.obj.V),
      MulAction.IsPretransitive G Y.obj.V ∧
      (∀ a : G', h a • y = y) ∧ ¬ Subsingleton Y.obj.V := by
  let : Finite (G ⧸ U) :=
    Subgroup.quotient_finite_of_isOpen U hUopen
  let hex := Finite.exists_equiv_fin (G ⧸ U)
  let n : ℕ := hex.choose
  let qEquiv : (G ⧸ U) ≃ Fin n :=
    Classical.choice hex.choose_spec
  let A := ULift.{w} (Fin n)
  let e : A ≃ (G ⧸ U) := Equiv.ulift.trans qEquiv.symm
  let : MulAction G A := e.mulAction G
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have stabilizer_eq (i : A) :
      MulAction.stabilizer G i =
        MulAction.stabilizer G (e i) := by
    ext g
    simp only [MulAction.mem_stabilizer_iff, Equiv.smul_def,
      Equiv.symm_apply_eq]
  let : MulAction.IsPretransitive G A := by
    rw [MulAction.isPretransitive_iff]
    intro i j
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (e i) (e j)
    refine ⟨g, ?_⟩
    rw [Equiv.smul_def, hg, Equiv.symm_apply_apply]
  let Y : ContAction FintypeCat.{w} G := by
    refine ⟨Action.FintypeCat.ofMulAction G (FintypeCat.of A), ?_⟩
    exact (by
      rw [continuousSMul_iff_stabilizer_isOpen]
      intro i
      rw [stabilizer_eq i]
      obtain ⟨a, ha⟩ :=
        MulAction.exists_smul_eq G
          (((1 : G) : G ⧸ U)) (e i)
      rw [← ha, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
        MulAction.stabilizer_quotient, Subgroup.coe_map]
      change IsOpen ((fun x : G ↦ a * x * a⁻¹) '' (U : Set G))
      simpa only [Set.image_image] using
        isOpenMap_mul_right a⁻¹ _
          (isOpenMap_mul_left a _ hUopen)
      : ContinuousSMul G A)
  let y : A := e.symm (((1 : G) : G ⧸ U))
  have hy (a : G') : h a • y = y := by
    apply e.injective
    rw [Equiv.smul_def, e.apply_symm_apply, e.apply_symm_apply]
    change QuotientGroup.mk (h a * 1) = QuotientGroup.mk 1
    rw [mul_one, QuotientGroup.eq]
    have haU : h a ∈ U := by
      apply hKU
      exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
    simpa only [mul_one] using U.inv_mem haU
  have hnsub : ¬ Subsingleton A := by
    intro hsub
    have hnall : ¬ ∀ g : G, g ∈ U := by
      intro hall
      apply hUne
      exact eq_top_iff.mpr fun g _ ↦ hall g
    obtain ⟨a, ha⟩ := not_forall.mp hnall
    have heq :=
      congrArg e (hsub.elim (e.symm (QuotientGroup.mk a)) y)
    have hq :
        (QuotientGroup.mk a : G ⧸ U) = QuotientGroup.mk 1 := by
      simpa only [y, e.apply_symm_apply] using heq
    have hainv : a⁻¹ ∈ U := by
      rw [QuotientGroup.eq] at hq
      simpa only [mul_one] using hq
    exact ha (U.inv_mem_iff.mp hainv)
  refine ⟨Y, y, ?_, hy, ?_⟩
  · change MulAction.IsPretransitive G A
    infer_instance
  · change ¬ Subsingleton A
    exact hnsub

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
variable {C' : Type v₁} [Category.{v₂} C'] [GaloisCategory C']
variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
variable (F' : C' ⥤ FintypeCat.{w}) [FiberFunctor F']
variable (H : C ⥤ C')

private theorem point_lifting_implies_surjective
    (t : H ⋙ F' ≅ F)
    (h4 : ∀ X : C, IsConnected X →
      Nonempty (⊤_ C' ⟶ H.obj X) → Nonempty (⊤_ C ⟶ X)) :
    Function.Surjective (autHomOfCompIso H t) := by
  let h := autHomOfCompIso H t
  by_contra nh
  obtain ⟨U, hUopen, hKU, hUne⟩ :=
    exists_open_supergroup h nh
  have hsmall :
      ∃ (Y : ContAction FintypeCat.{w} (Aut F)) (y : Y.obj.V),
        MulAction.IsPretransitive (Aut F) Y.obj.V ∧
        (∀ a : Aut F', h a • y = y) ∧ ¬ Subsingleton Y.obj.V :=
    exists_small_action h U hUopen hKU hUne
  obtain ⟨Y, y, hYtrans, hy, hYnsub⟩ := hsmall
  let E := functorToContAction F
  let E' := functorToContAction F'
  let X : C := E.objPreimage Y
  let eX := E.objObjPreimageIso Y
  let ef :=
    (forget₂ (ContAction FintypeCat (Aut F)) FintypeCat).mapIso eX
  let : Nonempty (F.obj X) := ⟨ef.inv y⟩
  let : MulAction.IsPretransitive (Aut F) (F.obj X) := by
    constructor
    intro x z
    let ex : Y.obj.V := ef.hom x
    let ez : Y.obj.V := ef.hom z
    obtain ⟨a, ha⟩ := hYtrans.exists_smul_eq ex ez
    refine ⟨a, ?_⟩
    have heq := ConcreteCategory.congr_hom (eX.hom.hom.comm a) x
    change ef.hom (a • x) = a • ex at heq
    have hmap : ef.hom (a • x) = ef.hom z := heq.trans ha
    have hi := congrArg ef.inv hmap
    exact (FintypeCat.hom_inv_id_apply ef (a • x)).symm.trans
      (hi.trans (FintypeCat.hom_inv_id_apply ef z))
  let : IsConnected X :=
    FiberFunctor.isConnected_of_isPretransitive F X
  let R := ContAction.res FintypeCat h
  let fixedMor : ⊤_ (ContAction FintypeCat.{w} (Aut F')) ⟶
      R.obj Y :=
    ObjectProperty.homMk
      (Action.Hom.mk (FintypeCat.homMk (fun _ ↦ y)) (by
        intro a
        ext z
        change y = h a • y
        exact (hy a).symm))
  let s := (functorToContActionCompIso H t).app X
  let m : E'.obj (⊤_ C') ⟶ E'.obj (H.obj X) :=
    (PreservesTerminal.iso E').hom ≫ fixedMor ≫
      (R.mapIso eX).inv ≫ s.inv
  obtain ⟨q⟩ := h4 X inferInstance ⟨E'.preimage m⟩
  let : Mono q := terminalIsTerminal.mono_from q
  let z : (⊤_ FintypeCat.{w}).obj :=
    (terminalIsTerminal.from (FintypeCat.of PUnit.{w + 1}))
      PUnit.unit
  have hterm_noninitial : IsInitial (⊤_ C) → False :=
    (not_initial_iff_fiber_nonempty F (⊤_ C)).mpr
      ⟨(PreservesTerminal.iso F).inv z⟩
  let : IsIso q :=
    IsConnected.noTrivialComponent (⊤_ C) q hterm_noninitial
  have hXterm : IsTerminal X :=
    terminalIsTerminal.ofIso (asIso q)
  have hFXterm : IsTerminal (F.obj X) :=
    hXterm.isTerminalObj F _
  have hFXsub : Subsingleton (F.obj X) := ⟨fun a b ↦ by
    let S := FintypeCat.of PUnit.{w + 1}
    let fa : S ⟶ F.obj X := FintypeCat.homMk (fun _ ↦ a)
    let fb : S ⟶ F.obj X := FintypeCat.homMk (fun _ ↦ b)
    have hab : fa = fb := hFXterm.hom_ext fa fb
    exact ConcreteCategory.congr_hom hab PUnit.unit⟩
  apply hYnsub
  constructor
  intro a b
  have hi : ef.inv a = ef.inv b := hFXsub.elim _ _
  have hh := congrArg ef.hom hi
  change @Eq
    ((forget₂ (ContAction FintypeCat (Aut F)) FintypeCat).obj Y).obj
      a b
  simpa only [FintypeCat.inv_hom_id_apply] using hh

private theorem surjective_implies_fullyFaithful
    (t : H ⋙ F' ≅ F)
    (hs : Function.Surjective (autHomOfCompIso H t)) :
    Nonempty H.FullyFaithful := by
  let h := autHomOfCompIso H t
  let E := functorToContAction F
  let E' := functorToContAction F'
  let R := ContAction.res FintypeCat h
  let : R.Full := ContAction.full_res FintypeCat h hs
  let : (E ⋙ R).Full := Functor.Full.comp E R
  let : (H ⋙ E').Full :=
    Functor.Full.of_iso (functorToContActionCompIso H t).symm
  let : H.Full := Functor.Full.of_comp_faithful H E'
  let : H.Faithful := t.faithful_of_comp
  exact ⟨Functor.FullyFaithful.ofFullyFaithful H⟩

private theorem surjective_implies_connected
    (t : H ⋙ F' ≅ F)
    (hs : Function.Surjective (autHomOfCompIso H t)) :
    ∀ X : C, IsConnected X → IsConnected (H.obj X) := by
  intro X hX
  let : IsConnected X := hX
  have hFX : Nonempty (F.obj X) :=
    (not_initial_iff_fiber_nonempty F X).mp IsConnected.notInitial
  let e := (functorToContActionCompIso H t).app X
  let ef :=
    (forget₂ (ContAction FintypeCat (Aut F')) FintypeCat).mapIso e
  let : Nonempty (F'.obj (H.obj X)) := ⟨ef.inv hFX.some⟩
  have htransF :
      MulAction.IsPretransitive (Aut F) (F.obj X) :=
    inferInstance
  let :
      MulAction.IsPretransitive (Aut F') (F'.obj (H.obj X)) := by
    constructor
    intro x y
    let ex : F.obj X := ef.hom x
    let ey : F.obj X := ef.hom y
    obtain ⟨a, ha⟩ := htransF.exists_smul_eq ex ey
    obtain ⟨a', rfl⟩ := hs a
    refine ⟨a', ?_⟩
    have heq := ConcreteCategory.congr_hom (e.hom.hom.comm a') x
    change ef.hom (a' • x) =
      ((autHomOfCompIso H t a') • ex : F.obj X) at heq
    have hmap : ef.hom (a' • x) = ef.hom y :=
      heq.trans ha
    have hi := congrArg ef.inv hmap
    exact (FintypeCat.hom_inv_id_apply ef (a' • x)).symm.trans
      (hi.trans (FintypeCat.hom_inv_id_apply ef y))
  exact FiberFunctor.isConnected_of_isPretransitive F' (H.obj X)

private theorem fullyFaithful_implies_points
    [PreservesLimitsOfShape (Discrete PEmpty.{1}) H]
    (hff : Nonempty H.FullyFaithful) :
    ∀ X : C, Function.Bijective
      (fun f : (⊤_ C ⟶ X) ↦
        (PreservesTerminal.iso H).inv ≫ H.map f) := by
  intro X
  let ff := hff.some
  constructor
  · intro f g hfg
    apply ff.map_injective
    simpa using
      (cancel_epi (PreservesTerminal.iso H).inv).mp hfg
  · intro q
    let f := ff.preimage ((PreservesTerminal.iso H).hom ≫ q)
    refine ⟨f, ?_⟩
    dsimp [f]
    rw [ff.map_preimage]
    rw [← PreservesTerminal.iso_hom]
    exact (PreservesTerminal.iso H).inv_hom_id_assoc q

private theorem points_imply_point_lifting
    [PreservesLimitsOfShape (Discrete PEmpty.{1}) H]
    (h5 : ∀ X : C, Function.Bijective
      (fun f : (⊤_ C ⟶ X) ↦
        (PreservesTerminal.iso H).inv ≫ H.map f)) :
    ∀ X : C, IsConnected X →
      Nonempty (⊤_ C' ⟶ H.obj X) → Nonempty (⊤_ C ⟶ X) := by
  intro X _ hq
  obtain ⟨f, _⟩ := (h5 X).surjective hq.some
  exact ⟨f⟩

private theorem connected_implies_point_lifting
    (t : H ⋙ F' ≅ F)
    (h3 : ∀ X : C, IsConnected X → IsConnected (H.obj X)) :
    ∀ X : C, IsConnected X →
      Nonempty (⊤_ C' ⟶ H.obj X) → Nonempty (⊤_ C ⟶ X) := by
  intro X hconn hq
  let : IsConnected (H.obj X) := h3 X hconn
  obtain ⟨q⟩ := hq
  let : Mono q := terminalIsTerminal.mono_from q
  let z : (⊤_ FintypeCat.{w}).obj :=
    (terminalIsTerminal.from (FintypeCat.of PUnit.{w + 1}))
      PUnit.unit
  have hterm_noninitial : IsInitial (⊤_ C') → False :=
    (not_initial_iff_fiber_nonempty F' (⊤_ C')).mpr
      ⟨(PreservesTerminal.iso F').inv z⟩
  let : IsIso q :=
    IsConnected.noTrivialComponent (⊤_ C') q hterm_noninitial
  have hHX : IsTerminal (H.obj X) :=
    terminalIsTerminal.ofIso (asIso q)
  have hFHX : IsTerminal (F'.obj (H.obj X)) :=
    hHX.isTerminalObj F' _
  have hFX : IsTerminal (F.obj X) :=
    hFHX.ofIso (t.app X)
  have hX : IsTerminal X :=
    hFX.isTerminalOfObj F X
  exact ⟨hX.from (⊤_ C)⟩

/--
The five equivalent surjectivity criteria for the homomorphism on fundamental
groups induced by a functor of Galois categories.
-/
@[stacks 0BN6]
theorem autHomOfCompIso_surjective_tfae
    [PreservesLimitsOfShape (Discrete PEmpty.{1}) H]
    (t : H ⋙ F' ≅ F) :
    List.TFAE [
      Function.Surjective (autHomOfCompIso H t),
      Nonempty H.FullyFaithful,
      ∀ X : C, IsConnected X → IsConnected (H.obj X),
      ∀ X : C, IsConnected X →
        Nonempty (⊤_ C' ⟶ H.obj X) → Nonempty (⊤_ C ⟶ X),
      ∀ X : C, Function.Bijective
        (fun f : (⊤_ C ⟶ X) ↦
          (PreservesTerminal.iso H).inv ≫ H.map f)] := by
  tfae_have 1 → 2 :=
    surjective_implies_fullyFaithful F F' H t
  tfae_have 1 → 3 :=
    surjective_implies_connected F F' H t
  tfae_have 2 → 5 :=
    fullyFaithful_implies_points H
  tfae_have 5 → 4 :=
    points_imply_point_lifting H
  tfae_have 3 → 4 :=
    connected_implies_point_lifting F F' H t
  tfae_have 4 → 1 :=
    point_lifting_implies_surjective F F' H t
  tfae_finish

end CategoryTheory.PreGaloisCategory
