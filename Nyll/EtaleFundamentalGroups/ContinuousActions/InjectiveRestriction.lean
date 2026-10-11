/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ProCGroups.ProC.Quotients.ClosedSubgroupNeighborhoods
import Nyll.ProCGroups.ProC.Quotients.LeftQuotientProjectionSections
import Nyll.EtaleFundamentalGroups.ContinuousActions.FiniteLimitsAndColimits
import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# Injectivity detected by finite continuous actions

A continuous homomorphism of profinite groups is injective exactly when every
nonempty transitive finite continuous action of the source has the
epi--mono span of [Stacks Project, Tag 0BN7](https://stacks.math.columbia.edu/tag/0BN7).
-/

noncomputable section

universe g' g w

open CategoryTheory
open scoped FintypeCatDiscrete

namespace CategoryTheory.ContAction

private theorem exists_openNormalSubgroup_comap_le
    {G' : Type g'} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
      [CompactSpace G']
    {G : Type g} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (h : G' →ₜ* G) (hinj : Function.Injective h)
    (U : OpenSubgroup G') :
    ∃ V : OpenNormalSubgroup G,
      (V : Subgroup G).comap h.toMonoidHom ≤ (U : Subgroup G') := by
  let H : ClosedSubgroup G :=
    { toSubgroup := h.toMonoidHom.range
      isClosed' := by
        change IsClosed (Set.range h)
        exact (isCompact_range h.continuous_toFun).isClosed }
  have hrangeInj : Function.Injective h.toMonoidHom.rangeRestrict := by
    intro a b hab
    apply hinj
    exact congrArg Subtype.val hab
  let emul : G' ≃* H :=
    MulEquiv.ofBijective h.toMonoidHom.rangeRestrict
      ⟨hrangeInj, h.toMonoidHom.rangeRestrict_surjective⟩
  have hemul_cont : Continuous emul :=
    Continuous.subtype_mk h.continuous_toFun _
  let ehomeo : G' ≃ₜ H :=
    Continuous.homeoOfEquivCompactToT2 (f := emul.toEquiv) hemul_cont
  let e : G' ≃ₜ* H :=
    ContinuousMulEquiv.mk' ehomeo (fun a b => emul.map_mul a b)
  let UH : OpenSubgroup H :=
    { toSubgroup := (U : Subgroup G').map e.toMulEquiv.toMonoidHom
      isOpen' := by
        change IsOpen (e '' ((U : Subgroup G') : Set G'))
        exact e.toHomeomorph.isOpenMap _ U.isOpen' }
  obtain ⟨V, hVU⟩ :=
    ProCGroups.ProC.exists_openNormalSubgroup_inter_closedSubgroup_le H UH
  refine ⟨V, ?_⟩
  intro a ha
  have heaComap : e a ∈
      (ProCGroups.OpenNormalSubgroup.comap
        ((H : Subgroup G).subtype) continuous_subtype_val V :
          OpenNormalSubgroup H) := by
    change h a ∈ V
    exact ha
  have heaUH : e a ∈ UH := hVU heaComap
  have heaU : e.symm (e a) ∈ U := Subgroup.mem_map_equiv.mp heaUH
  simpa using heaU

variable {G' : Type g'} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  [CompactSpace G'] [TotallyDisconnectedSpace G']
variable {G : Type g} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [TotallyDisconnectedSpace G'] in
private theorem exists_epi_mono_span_of_injective
    (h : G' →ₜ* G) (hinj : Function.Injective h)
    (X' : ContAction FintypeCat.{w} G')
    (hnon : Nonempty X'.obj.V)
    (htrans : MulAction.IsPretransitive G' X'.obj.V) :
    ∃ (X : ContAction FintypeCat.{w} G)
      (Y : ContAction FintypeCat.{w} G')
      (q : Y ⟶ X')
      (i : Y ⟶ (ContAction.res FintypeCat h).obj X),
      Epi q ∧ Mono i := by
  let : ContinuousSMul G' X'.obj.V := X'.2
  let : MulAction.IsPretransitive G' X'.obj.V := htrans
  let x₀ : X'.obj.V := hnon.some
  let U : OpenSubgroup G' :=
    { toSubgroup := MulAction.stabilizer G' x₀
      isOpen' := stabilizer_isOpen G' x₀ }
  obtain ⟨V, hcomap_le⟩ :=
    exists_openNormalSubgroup_comap_le h hinj U
  let : Finite (G ⧸ (V : Subgroup G)) :=
    ProCGroups.openNormalSubgroup_finiteQuotient V
  let hex := Finite.exists_equiv_fin (G ⧸ (V : Subgroup G))
  let n : ℕ := hex.choose
  let qEquiv : (G ⧸ (V : Subgroup G)) ≃ Fin n :=
    Classical.choice hex.choose_spec
  let A := ULift.{w} (Fin n)
  let eA : A ≃ (G ⧸ (V : Subgroup G)) := Equiv.ulift.trans qEquiv.symm
  let : MulAction G A := eA.mulAction G
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have stabilizer_A_eq (a : A) :
      MulAction.stabilizer G a = MulAction.stabilizer G (eA a) := by
    ext s
    simp only [MulAction.mem_stabilizer_iff, Equiv.smul_def, Equiv.symm_apply_eq]
  have hAcont : ContinuousSMul G A := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro a
    rw [stabilizer_A_eq a]
    obtain ⟨s, hs⟩ := MulAction.exists_smul_eq G
      (((1 : G) : G ⧸ (V : Subgroup G))) (eA a)
    rw [← hs, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      MulAction.stabilizer_quotient, Subgroup.coe_map]
    change IsOpen ((fun x : G => s * x * s⁻¹) '' ((V : Subgroup G) : Set G))
    simpa only [Set.image_image] using
      isOpenMap_mul_right s⁻¹ _
        (isOpenMap_mul_left s _ (ProCGroups.openNormalSubgroup_isOpen V))
  let : ContinuousSMul G A := hAcont
  let X : ContAction FintypeCat.{w} G :=
    ⟨Action.FintypeCat.ofMulAction G (FintypeCat.of A), hAcont⟩
  let : MulAction G' A := MulAction.compHom A h.toMonoidHom
  let : ContinuousSMul G' A :=
    MulAction.continuousSMul_compHom h.continuous_toFun
  let a₀ : A := eA.symm (((1 : G) : G ⧸ (V : Subgroup G)))
  let p₀ : A × X'.obj.V := (a₀, x₀)
  let B := MulAction.orbit G' p₀
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  have stabilizer_B_eq (b : B) :
      MulAction.stabilizer G' b = MulAction.stabilizer G' b.1 := by
    ext s
    simp only [MulAction.mem_stabilizer_iff]
    constructor
    · exact fun hs => congrArg Subtype.val hs
    · exact fun hs => Subtype.ext hs
  have hBcont : ContinuousSMul G' B := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro b
    rw [stabilizer_B_eq b]
    exact stabilizer_isOpen G' b.1
  let Y : ContAction FintypeCat.{w} G' :=
    ⟨Action.FintypeCat.ofMulAction G' (FintypeCat.of B), hBcont⟩
  let q : Y ⟶ X' := ObjectProperty.homMk (Action.Hom.mk
    (FintypeCat.homMk (fun b : B => b.1.2)) (by intro s; ext b; rfl))
  let i : Y ⟶ (ContAction.res FintypeCat h).obj X :=
    ObjectProperty.homMk (Action.Hom.mk
      (FintypeCat.homMk (fun b : B => b.1.1)) (by intro s; ext b; rfl))
  have hqsurj : Function.Surjective (ConcreteCategory.hom q) := by
    intro z
    obtain ⟨s, hs⟩ := MulAction.exists_smul_eq G' x₀ z
    let b : B := ⟨s • p₀, MulAction.mem_orbit_iff.mpr ⟨s, rfl⟩⟩
    exact ⟨b, hs⟩
  have hiinj : Function.Injective (ConcreteCategory.hom i) := by
    change Function.Injective (fun b : B => b.1.1)
    intro b c hbc
    apply Subtype.ext
    apply Prod.ext hbc
    obtain ⟨s, hs⟩ := MulAction.mem_orbit_iff.mp b.2
    obtain ⟨t, ht⟩ := MulAction.mem_orbit_iff.mp c.2
    have hfirst : s • a₀ = t • a₀ := by
      calc
        s • a₀ = (s • p₀).1 := rfl
        _ = b.1.1 := congrArg (fun z : A × X'.obj.V => z.1) hs
        _ = c.1.1 := hbc
        _ = (t • p₀).1 :=
          (congrArg (fun z : A × X'.obj.V => z.1) ht).symm
        _ = t • a₀ := rfl
    have hd_first : (t⁻¹ * s) • a₀ = a₀ := by
      have heq := congrArg (t⁻¹ • ·) hfirst
      simpa only [← mul_smul, inv_mul_cancel, one_smul] using heq
    have hdV : h.toMonoidHom (t⁻¹ * s) ∈ (V : Subgroup G) := by
      rw [← MulAction.stabilizer_quotient (V : Subgroup G),
        MulAction.mem_stabilizer_iff]
      have heq := congrArg eA hd_first
      simpa only [MulAction.compHom_smul_def, Equiv.smul_def,
        eA.apply_symm_apply, a₀] using heq
    have hdU : t⁻¹ * s ∈ U := hcomap_le hdV
    have hd_second : (t⁻¹ * s) • x₀ = x₀ := hdU
    have hsecond : s • x₀ = t • x₀ := by
      have heq := congrArg (t • ·) hd_second
      simpa only [← mul_smul, mul_inv_cancel_left] using heq
    calc
      b.1.2 = (s • p₀).2 :=
        (congrArg (fun z : A × X'.obj.V => z.2) hs).symm
      _ = s • x₀ := rfl
      _ = t • x₀ := hsecond
      _ = (t • p₀).2 := rfl
      _ = c.1.2 := congrArg (fun z : A × X'.obj.V => z.2) ht
  let : Epi q := ConcreteCategory.epi_of_surjective q hqsurj
  let : Mono i := ConcreteCategory.mono_of_injective i hiinj
  exact ⟨X, Y, q, i, inferInstance, inferInstance⟩

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G] in
private theorem injective_of_exists_epi_mono_span
    (h : G' →ₜ* G)
    (hspan :
      ∀ X' : ContAction FintypeCat.{w} G',
        Nonempty X'.obj.V →
        MulAction.IsPretransitive G' X'.obj.V →
        ∃ (X : ContAction FintypeCat.{w} G)
          (Y : ContAction FintypeCat.{w} G')
          (q : Y ⟶ X')
          (i : Y ⟶ (ContAction.res FintypeCat h).obj X),
          Epi q ∧ Mono i) :
    Function.Injective h := by
  intro a b hab
  let k : G' := a⁻¹ * b
  have hab' : h.toMonoidHom a = h.toMonoidHom b := hab
  have hkmap : h.toMonoidHom k = 1 := by
    simp only [k, map_mul, map_inv, hab', inv_mul_cancel]
  by_contra hkne
  have hkne' : k ≠ 1 := by
    intro hk
    exact hkne (inv_mul_eq_one.mp (by simpa [k] using hk))
  obtain ⟨U, hkU⟩ :=
    ProCGroups.ProC.exists_openNormalSubgroup_not_mem
      (G := G') (x := k) hkne'
  let : Finite (G' ⧸ (U : Subgroup G')) :=
    ProCGroups.openNormalSubgroup_finiteQuotient U
  let hex := Finite.exists_equiv_fin (G' ⧸ (U : Subgroup G'))
  let n : ℕ := hex.choose
  let qEquiv : (G' ⧸ (U : Subgroup G')) ≃ Fin n :=
    Classical.choice hex.choose_spec
  let A := ULift.{w} (Fin n)
  let eU : A ≃ (G' ⧸ (U : Subgroup G')) :=
    Equiv.ulift.trans qEquiv.symm
  let : MulAction G' A := eU.mulAction G'
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have stabilizer_A_eq (x : A) :
      MulAction.stabilizer G' x = MulAction.stabilizer G' (eU x) := by
    ext s
    simp only [MulAction.mem_stabilizer_iff, Equiv.smul_def, Equiv.symm_apply_eq]
  have hAcont : ContinuousSMul G' A := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    rw [stabilizer_A_eq x]
    obtain ⟨s, hs⟩ := MulAction.exists_smul_eq G'
      (((1 : G') : G' ⧸ (U : Subgroup G'))) (eU x)
    rw [← hs, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      MulAction.stabilizer_quotient, Subgroup.coe_map]
    change IsOpen
      ((fun z : G' => s * z * s⁻¹) '' ((U : Subgroup G') : Set G'))
    simpa only [Set.image_image] using
      isOpenMap_mul_right s⁻¹ _
        (isOpenMap_mul_left s _
          (ProCGroups.openNormalSubgroup_isOpen U))
  let X' : ContAction FintypeCat.{w} G' :=
    ⟨Action.FintypeCat.ofMulAction G' (FintypeCat.of A), hAcont⟩
  let x₀ : A :=
    eU.symm (((1 : G') : G' ⧸ (U : Subgroup G')))
  have htrans : MulAction.IsPretransitive G' A := by
    constructor
    intro x y
    obtain ⟨s, hs⟩ := MulAction.exists_smul_eq G' (eU x) (eU y)
    refine ⟨s, eU.injective ?_⟩
    simpa only [Equiv.smul_def, eU.apply_symm_apply] using hs
  obtain ⟨X, Y, q, i, hq, hi⟩ :=
    hspan X' ⟨x₀⟩ htrans
  let : Epi q := hq
  let : Mono i := hi
  let : Limits.PreservesColimitsOfShape Limits.WalkingSpan
      (forget (ContAction FintypeCat.{w} G')) := by
    change Limits.PreservesColimitsOfShape _
      (forget₂ (ContAction FintypeCat.{w} G') FintypeCat ⋙
        forget FintypeCat)
    infer_instance
  let : Limits.PreservesLimitsOfShape Limits.WalkingCospan
      (forget (ContAction FintypeCat.{w} G')) := by
    change Limits.PreservesLimitsOfShape _
      (forget₂ (ContAction FintypeCat.{w} G') FintypeCat ⋙
        forget FintypeCat)
    infer_instance
  have hqsurj : Function.Surjective (ConcreteCategory.hom q) :=
    ConcreteCategory.surjective_of_epi_of_preservesPushout q
  have hiinj : Function.Injective (ConcreteCategory.hom i) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback i
  obtain ⟨y, hy⟩ := hqsurj x₀
  have hki :
      ConcreteCategory.hom i ((Y.obj.ρ k).hom y) =
        ConcreteCategory.hom i y := by
    have hcomm := ConcreteCategory.congr_hom (i.hom.comm k) y
    change ConcreteCategory.hom i ((Y.obj.ρ k).hom y) =
      (X.obj.ρ (h.toMonoidHom k)).hom
        (ConcreteCategory.hom i y) at hcomm
    rw [hkmap, Action.ρ_one] at hcomm
    exact hcomm.trans (ConcreteCategory.id_apply _)
  have hky : (Y.obj.ρ k).hom y = y := hiinj hki
  have hkxρ : (X'.obj.ρ k).hom x₀ = x₀ := by
    rw [← hy]
    have hcomm := ConcreteCategory.congr_hom (q.hom.comm k) y
    change ConcreteCategory.hom q ((Y.obj.ρ k).hom y) =
      (X'.obj.ρ k).hom (ConcreteCategory.hom q y) at hcomm
    rw [← hcomm, hky]
  have hkx : k • x₀ = x₀ := by
    change (X'.obj.ρ k).hom x₀ = x₀
    exact hkxρ
  have hkstab :
      k ∈ MulAction.stabilizer G'
        (((1 : G') : G' ⧸ (U : Subgroup G'))) := by
    rw [MulAction.mem_stabilizer_iff]
    have heq := congrArg eU hkx
    simpa only [Equiv.smul_def, eU.apply_symm_apply, x₀] using heq
  apply hkU
  rwa [MulAction.stabilizer_quotient] at hkstab

/--
A continuous homomorphism of profinite groups is injective exactly when every
nonempty transitive finite continuous source action has an epimorphism from
a finite continuous source action that embeds in a restricted target action.
-/
@[stacks 0BN7]
theorem injective_iff_exists_epi_mono_span
    (h : G' →ₜ* G) :
    Function.Injective h ↔
      ∀ X' : ContAction FintypeCat.{w} G',
        Nonempty X'.obj.V →
        MulAction.IsPretransitive G' X'.obj.V →
        ∃ (X : ContAction FintypeCat.{w} G)
          (Y : ContAction FintypeCat.{w} G')
          (q : Y ⟶ X')
          (i : Y ⟶ (ContAction.res FintypeCat h).obj X),
          Epi q ∧ Mono i := by
  constructor
  · exact exists_epi_mono_span_of_injective h
  · exact injective_of_exists_epi_mono_span h

end CategoryTheory.ContAction
