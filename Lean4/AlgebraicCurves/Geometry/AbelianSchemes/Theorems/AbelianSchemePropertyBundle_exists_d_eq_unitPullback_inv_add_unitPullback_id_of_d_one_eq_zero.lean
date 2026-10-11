/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_inv_add_unitPullback_id_of_d_one_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Abel
import AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import AlgebraicCurves.Cohomology.Sheaves.OrderedAffineCoverCochainPullback
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero
import AlgebraicCurves.Geometry.Schemes.Scheme_OrderedAffineCover_exists_refinement_pullback_fst_snd_of_isSeparated
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_exists_linearMap_apply_eq_unitPullback
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_d_unitPullback
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_unitPullback_unitPullback_sub_mem_of_d_eq_zero
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_exists_HSucc_equiv_unitPullback_id_of_isSeparated

/-!
# Coboundaries from inversion and identity pullbacks of first cocycles
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs.AbelianInverseUnitPullback
attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChange_inv
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.baseChange_mul
  GoodReductionJacobian.RelativeGroupLaw.baseChange_one
  GoodReductionJacobian.RelativeGroupLaw.nsmul_zero
  GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset
  GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.schemeHomOverComp_id_left
  NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe
  NeronModelInfra.schemeHomOverComp_coe
attribute [-simp] NeronModelInfra.fibreRestrictAlong_coe_comp_snd
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst GoodReductionJacobian.RelativeGroupLaw.fibre_inv
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_mul
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_one
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra hiding schemeHomOverComp
open _root_.GoodReductionJacobian


universe u

namespace AntiInv

theorem le_preimage_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (g' : Y ⟶ Z) {U : X.Opens} {V : Y.Opens}
  {W : Z.Opens}
    (hU : U ≤ g ⁻¹ᵁ V) (hV : V ≤ g' ⁻¹ᵁ W) : U ≤ (g ≫ g') ⁻¹ᵁ W := fun _ hx => hV (hU hx)

theorem unitPullback_eq_zero_of_subsingleton {R R' : Type u} [CommRing R] [CommRing R'] {X Y :
  Scheme.{u}}
    {πX : X ⟶ Spec (.of R')} {πY : Y ⟶ Spec (.of R)} (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover)
    (𝒦 : Y.OrderedAffineCover) [Subsingleton 𝒦.ι] (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U
      (lam w))
    (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 (n + 1)) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam (n + 1) z = 0 := by
  funext s
  rw [OModulePresheaf.unitPullback_apply_of_not_injective]
  · rfl
  · intro hinj
    have h01 : (0 : Fin (n + 2)) = 1 := hinj (Subsingleton.elim _ _)
    exact absurd h01 (by simp)

end AntiInv

end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs.AbelianInverseUnitPullback

namespace GoodReductionJacobian.AbelianSchemePropertyBundle

universe u

open _root_.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs.AbelianInverseUnitPullback in
open _root_.CategoryTheory in
open _root_.CategoryTheory.Limits in
open _root_.AlgebraicGeometry in
open _root_.NeronModelInfra hiding schemeHomOverComp in
open _root_.GoodReductionJacobian in
open AntiInv _root_.AlgebraicGeometry.OModulePresheaf in
theorem exists_d_eq_unitPullback_inv_add_unitPullback_id_of_d_one_eq_zero
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (𝒦 𝒲 : A.OrderedAffineCover) (lam₁ lam₂ : 𝒲.ι → 𝒦.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1 ⁻¹ᵁ 𝒦.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam₂ w))
    (z : (OModulePresheaf.unit f).cochain 𝒦 1) (hz : (OModulePresheaf.unit f).d 𝒦 1 z = 0) :
    ∃ b : (OModulePresheaf.unit f).cochain 𝒲 0,
      (OModulePresheaf.unit f).d 𝒲 0 b =
        OModulePresheaf.unitPullback (πX := f) (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1 𝒲 𝒦 lam₁ h₁ 1
          z +
          OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦 lam₂ h₂ 1 z := by
  classical
  have : IsProper f := hA.proper
  have : IsSeparated f := inferInstance
  let ι : A ⟶ A := (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1
  have hι : ι ≫ f = f := (L.inv f ⟨𝟙 A, Category.id_comp f⟩).2
  let e : Spec (CommRingCat.of k) ⟶ A := (L.one (𝟙 (Spec (CommRingCat.of k)))).1
  have he : e ≫ f = 𝟙 _ := (L.one (𝟙 (Spec (CommRingCat.of k)))).2
  let μ : pullback f f ⟶ A :=
    (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f,
      pullback.condition.symm⟩).1
  have hμ : μ ≫ f = pullback.fst f f ≫ f :=
    (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f,
      pullback.condition.symm⟩).2
  have w : 𝟙 A ≫ f = ι ≫ f := by rw [Category.id_comp, hι]
  let δ : A ⟶ pullback f f := pullback.lift (𝟙 A) ι w
  have hδ1 : δ ≫ pullback.fst f f = 𝟙 A := pullback.lift_fst _ _ _
  have hδ2 : δ ≫ pullback.snd f f = ι := pullback.lift_snd _ _ _
  have hδμ : δ ≫ μ = f ≫ e := by
    have hψ : δ ≫ (pullback.fst f f ≫ f) = f := by rw [← Category.assoc, hδ1, Category.id_comp]
    have h := congrArg Subtype.val
      (L.mul_natural (pullback.fst f f ≫ f) f δ hψ ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f,
        pullback.condition.symm⟩)
    have hx : schemeHomOverComp δ hψ ⟨pullback.fst f f, rfl⟩ = ⟨𝟙 A, Category.id_comp f⟩ :=
      Subtype.ext hδ1
    have hy : schemeHomOverComp δ hψ ⟨pullback.snd f f, pullback.condition.symm⟩ =
        L.inv f ⟨𝟙 A, Category.id_comp f⟩ := Subtype.ext hδ2
    rw [hx, hy, L.mul_inv_cancel, ← L.one_natural (𝟙 _) f f (Category.comp_id f)] at h
    exact h
  have hδf : δ ≫ (pullback.fst f f ≫ f) = f := by rw [← Category.assoc, hδ1, Category.id_comp]
  have : IsAffineHom δ := by
    have : IsAffineHom (δ ≫ pullback.fst f f) := by rw [hδ1]; infer_instance
    exact IsAffineHom.of_comp δ (pullback.fst f f)
  let zt : (OModulePresheaf.unit f).cochain 𝒲 1 := OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦
    lam₂ h₂ 1 z
  have hzt : (OModulePresheaf.unit f).d 𝒲 1 zt = 0 := by
    obtain ⟨L2, hL2⟩ := AlgebraicGeometry.OModulePresheaf.exists_linearMap_apply_eq_unitPullback f
      f (𝟙 A)
      (Category.id_comp f) 𝒲 𝒦 lam₂ h₂ 2
    change (OModulePresheaf.unit f).d 𝒲 1 (OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦 lam₂ h₂
      1 z) = 0
    rw [AlgebraicGeometry.OModulePresheaf.d_unitPullback, hz, ← hL2, map_zero]
  obtain ⟨𝒲', l₁, l₂, l₃, hl₁, hl₂, hl₃⟩ :=
    AlgebraicGeometry.Scheme.OrderedAffineCover.exists_refinement_pullback_fst_snd_of_isSeparated f
      𝒲 μ hμ
  obtain ⟨b', hb'⟩ :=
    exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero
      k f L hA 𝒲 𝒲' l₁ l₂ l₃ hl₁ hl₂ hl₃ zt hzt
  let 𝒱 : A.OrderedAffineCover := 𝒲'.comap δ
  have hv : ∀ v, 𝒱.U v ≤ δ ⁻¹ᵁ 𝒲'.U (id v) := fun v => le_rfl
  have hv1 : ∀ v, 𝒱.U v ≤ (𝟙 A) ⁻¹ᵁ 𝒲.U (l₁ v) := fun v => hδ1 ▸ le_preimage_comp δ (pullback.fst f
    f) (hv v) (hl₁ v)
  have hv2 : ∀ v, 𝒱.U v ≤ ι ⁻¹ᵁ 𝒲.U (l₂ v) := fun v => hδ2 ▸ le_preimage_comp δ (pullback.snd f f)
    (hv v) (hl₂ v)
  have hv3 : ∀ v, 𝒱.U v ≤ (δ ≫ μ) ⁻¹ᵁ 𝒲.U (l₃ v) := fun v => le_preimage_comp δ μ (hv v) (hl₃ v)
  let S : Submodule k ((OModulePresheaf.unit f).cochain 𝒱 1) := LinearMap.range
    ((OModulePresheaf.unit f).d 𝒱 0)
  have ha : OModulePresheaf.unitPullback (πX := f) δ 𝒱 𝒲' id hv 1
        (OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) μ 𝒲' 𝒲 l₃ hl₃ 1 zt) -
      OModulePresheaf.unitPullback (πX := f) (δ ≫ μ) 𝒱 𝒲 l₃ hv3 1 zt ∈ S :=
    AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f
      (pullback.fst f f ≫ f) f
      δ μ (δ ≫ μ) rfl 𝒱 𝒲' 𝒲 id l₃ l₃ rfl hv hl₃ hv3 1 zt hzt
  have hb : OModulePresheaf.unitPullback (πX := f) δ 𝒱 𝒲' id hv 1
        (OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲' 𝒲 l₁ hl₁ 1
          zt) -
      OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱 𝒲 l₁ hv1 1 zt ∈ S :=
    AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f
      (pullback.fst f f ≫ f) f
      δ (pullback.fst f f) (𝟙 A) hδ1.symm 𝒱 𝒲' 𝒲 id l₁ l₁ rfl hv hl₁ hv1 1 zt hzt
  have hc : OModulePresheaf.unitPullback (πX := f) δ 𝒱 𝒲' id hv 1
        (OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲' 𝒲 l₂ hl₂ 1
          zt) -
      OModulePresheaf.unitPullback (πX := f) ι 𝒱 𝒲 l₂ hv2 1 zt ∈ S :=
    AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f
      (pullback.fst f f ≫ f) f
      δ (pullback.snd f f) ι hδ2.symm 𝒱 𝒲' 𝒲 id l₂ l₂ rfl hv hl₂ hv2 1 zt hzt
  have hd : OModulePresheaf.unitPullback (πX := f) δ 𝒱 𝒲' id hv 1
        (OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) μ 𝒲' 𝒲 l₃ hl₃ 1 zt) -
      OModulePresheaf.unitPullback (πX := f) δ 𝒱 𝒲' id hv 1
        (OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲' 𝒲 l₁ hl₁ 1
          zt) -
      OModulePresheaf.unitPullback (πX := f) δ 𝒱 𝒲' id hv 1
        (OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲' 𝒲 l₂ hl₂ 1
          zt) ∈ S := by
    obtain ⟨Lδ, hLδ⟩ := AlgebraicGeometry.OModulePresheaf.exists_linearMap_apply_eq_unitPullback f
      (pullback.fst f f ≫ f)
      δ hδf 𝒱 𝒲' id hv 1
    rw [← hLδ, ← hLδ, ← hLδ, ← map_sub, ← map_sub, ← hb', hLδ]
    erw [← AlgebraicGeometry.OModulePresheaf.d_unitPullback f (pullback.fst f f ≫ f) δ 𝒱 𝒲' id hv 0
      b']
    exact LinearMap.mem_range_self _ _
  have he' : OModulePresheaf.unitPullback (πX := f) (δ ≫ μ) 𝒱 𝒲 l₃ hv3 1 zt ∈ S := by
    have hpt : (e.base (IsLocalRing.closedPoint k) : A) ∈ (⊤ : A.Opens) := trivial
    rw [← 𝒲.iSup_eq_top, TopologicalSpace.Opens.mem_iSup] at hpt
    obtain ⟨i₀, hi₀⟩ := hpt
    let 𝒮 := Scheme.OrderedAffineCover.ofAffine (Spec (CommRingCat.of k))
    have : Subsingleton 𝒮.ι := (inferInstance : Subsingleton PUnit)
    have hlamf : ∀ v, 𝒱.U v ≤ f ⁻¹ᵁ 𝒮.U ((fun _ => PUnit.unit) v) := fun v => le_top
    have hlame : ∀ s, 𝒮.U s ≤ e ⁻¹ᵁ 𝒲.U ((fun _ => i₀) s) := by
      intro s x _
      have hx : x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      rw [hx]; exact hi₀
    have hlam3 : ∀ v, 𝒱.U v ≤ (δ ≫ μ) ⁻¹ᵁ 𝒲.U ((fun _ => i₀) v) := fun v =>
      hδμ ▸ le_preimage_comp f e (hlamf v) (hlame PUnit.unit)
    have h1 := AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f
      (𝟙 _) f
      f e (δ ≫ μ) hδμ 𝒱 𝒮 𝒲 (fun _ => PUnit.unit) (fun _ => i₀) (fun _ => i₀) rfl hlamf hlame hlam3
        1 zt hzt
    rw [AntiInv.unitPullback_eq_zero_of_subsingleton (πX := f)
      (πY := 𝟙 (Spec (CommRingCat.of k))) f 𝒱 𝒮 (fun _ => PUnit.unit) hlamf 0, zero_sub] at h1
    obtain ⟨b3, hb3⟩ :=
      exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero
      f f (δ ≫ μ) 𝒱 𝒲 l₃ (fun _ => i₀) hv3 hlam3 zt hzt
    have h2 : OModulePresheaf.unitPullback (πX := f) (δ ≫ μ) 𝒱 𝒲 l₃ hv3 1 zt -
        OModulePresheaf.unitPullback (πX := f) (δ ≫ μ) 𝒱 𝒲 (fun _ => i₀) hlam3 1 zt ∈ S := ⟨b3, hb3⟩
    have hB := (S.neg_mem_iff).mp h1
    have h3 := S.add_mem h2 hB
    simpa only [sub_add_cancel] using h3
  have key : OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱 𝒲 l₁ hv1 1 zt +
      OModulePresheaf.unitPullback (πX := f) ι 𝒱 𝒲 l₂ hv2 1 zt ∈ S := by
    have hμS := S.add_mem ha he'
    simp only [sub_add_cancel] at hμS
    have hsum := S.sub_mem hμS hd
    have := S.sub_mem (S.sub_mem hsum hb) hc
    convert this using 1
    abel
  let uu : (OModulePresheaf.unit f).cochain 𝒲 1 :=
    OModulePresheaf.unitPullback (πX := f) (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1 𝒲 𝒦 lam₁ h₁ 1 z +
      OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦 lam₂ h₂ 1 z
  have hu0 : (OModulePresheaf.unit f).d 𝒲 1 uu = 0 := by
    obtain ⟨L1, hL1⟩ := AlgebraicGeometry.OModulePresheaf.exists_linearMap_apply_eq_unitPullback f
      f ι hι 𝒲 𝒦 lam₁ h₁ 2
    obtain ⟨L2, hL2⟩ := AlgebraicGeometry.OModulePresheaf.exists_linearMap_apply_eq_unitPullback f
      f (𝟙 A)
      (Category.id_comp f) 𝒲 𝒦 lam₂ h₂ 2
    change (OModulePresheaf.unit f).d 𝒲 1 (OModulePresheaf.unitPullback (πX := f) ι 𝒲 𝒦 lam₁ h₁ 1 z
      +
      OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦 lam₂ h₂ 1 z) = 0
    rw [map_add, AlgebraicGeometry.OModulePresheaf.d_unitPullback,
      AlgebraicGeometry.OModulePresheaf.d_unitPullback, hz,
      ← hL1, ← hL2, map_zero, map_zero, add_zero]
  have hkey2 : OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱 𝒲 l₁ hv1 1 uu ∈ S := by
    obtain ⟨L1, hL1⟩ := AlgebraicGeometry.OModulePresheaf.exists_linearMap_apply_eq_unitPullback f
      f (𝟙 A)
      (Category.id_comp f) 𝒱 𝒲 l₁ hv1 1
    have hsplit : OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱 𝒲 l₁ hv1 1 uu =
        OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱 𝒲 l₁ hv1 1
            (OModulePresheaf.unitPullback (πX := f) ι 𝒲 𝒦 lam₁ h₁ 1 z) +
          OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱 𝒲 l₁ hv1 1 zt := by
      rw [← hL1, ← hL1, ← hL1, ← map_add]
    rw [hsplit]
    have hg1 : ∀ v, 𝒱.U v ≤ ι ⁻¹ᵁ 𝒦.U ((lam₁ ∘ l₁) v) := fun v =>
      (Category.id_comp ι) ▸ le_preimage_comp (𝟙 A) ι (hv1 v) (h₁ (l₁ v))
    have hg := AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f f
      f
      (𝟙 A) ι ι (Category.id_comp ι).symm 𝒱 𝒲 𝒦 l₁ lam₁ (lam₁ ∘ l₁) rfl hv1 h₁ hg1 1 z hz
    have hh1 : ∀ v, 𝒱.U v ≤ ι ⁻¹ᵁ 𝒦.U ((lam₂ ∘ l₂) v) := fun v =>
      (Category.comp_id ι) ▸ le_preimage_comp ι (𝟙 A) (hv2 v) (h₂ (l₂ v))
    have hh := AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero f f
      f
      ι (𝟙 A) ι (Category.comp_id ι).symm 𝒱 𝒲 𝒦 l₂ lam₂ (lam₂ ∘ l₂) rfl hv2 h₂ hh1 1 z hz
    obtain ⟨bi, hbi⟩ :=
      exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero
      f f ι 𝒱 𝒦 (lam₁ ∘ l₁) (lam₂ ∘ l₂) hg1 hh1 z hz
    have hi : OModulePresheaf.unitPullback (πX := f) ι 𝒱 𝒦 (lam₁ ∘ l₁) hg1 1 z -
        OModulePresheaf.unitPullback (πX := f) ι 𝒱 𝒦 (lam₂ ∘ l₂) hh1 1 z ∈ S := ⟨bi, hbi⟩
    have := S.add_mem (S.sub_mem (S.add_mem hg hi) hh) key
    convert this using 1
    change _ = _ - (OModulePresheaf.unitPullback (πX := f) ι 𝒱 𝒲 l₂ hv2 1 zt - _) + _
    abel
  obtain ⟨e₀, eH, -, heH⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated f 𝒲 𝒱 l₁ hv1
  obtain ⟨huv, heq⟩ := heH 0 ⟨uu, hu0⟩
  have hzero : eH 0 (Submodule.Quotient.mk ⟨uu, hu0⟩) = 0 := by
    rw [heq, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact hkey2
  rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hzero
  obtain ⟨b, hb⟩ := hzero
  exact ⟨b, hb⟩
end GoodReductionJacobian.AbelianSchemePropertyBundle
end ProofImplementation

attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype
  AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp
  CochainCx.Bounded.modR
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChange_inv
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.baseChange_mul
  GoodReductionJacobian.RelativeGroupLaw.baseChange_one
  GoodReductionJacobian.RelativeGroupLaw.nsmul_zero
  GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset
  GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.schemeHomOverComp_id_left
attribute [-simp] NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe
  NeronModelInfra.schemeHomOverComp_coe NeronModelInfra.fibreRestrictAlong_coe_comp_snd
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst GoodReductionJacobian.RelativeGroupLaw.fibre_inv
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_mul
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_one
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq
  AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec CochainCx.Bounded.mk.sizeOf_spec
  CochainCx.Bounded.mk.injEq
