/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import AlgebraicCurves.Cohomology.Cech.OrderedAffineCoverCechCup
import AlgebraicCurves.Cohomology.Sheaves.OrderedAffineCoverCochainPullback
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_map_app_unitPullback_eq_unitPullback_comp
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_d_unitPullback
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_bijective_appTop_fibre_of_isPullback

/-!
# Abelian Scheme Property Bundle exists d eq unit Pullback mul sub fst sub snd of d one eq
zero
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero
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
  AlgebraicGeometry.schemeFibreEndo_fst


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra hiding schemeHomOverComp
open _root_.GoodReductionJacobian

open scoped TensorProduct DirectSum

universe u

namespace GoodReductionJacobian

export _root_.GoodReductionJacobian (AbelianSchemePropertyBundle schemeHomOverComp RelativeGroupLaw
  AbelianSchemePropertyBundle.bijective_appTop_fibre_of_isPullback)

namespace P2mPrimDeg1

open _root_.GoodReductionJacobian


theorem unitPullback_congr {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h h' : X ⟶ Y) (e : h = h') (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι →
      𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ w, 𝒲.U w ≤ h' ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ)
    (z : (OModulePresheaf.unit πY).cochain 𝒦 n) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z = OModulePresheaf.unitPullback (πX
      := πX) h' 𝒲 𝒦 lam hlam' n z := by
  subst e; rfl

theorem unitPullback_const_one {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (j₀ : 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U ((fun _ => j₀) w))
    (z : (OModulePresheaf.unit πY).cochain 𝒦 1) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 (fun _ => j₀) hlam 1 z = 0 := by
  funext s
  rw [Pi.zero_apply]
  apply OModulePresheaf.unitPullback_apply_of_not_injective
  intro hinj
  have := @hinj 0 1 rfl
  exact absurd this (by decide)

theorem unitPullback_zero {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n (0 : (OModulePresheaf.unit πY).cochain
      𝒦 n) = 0 := by
  classical
  funext s
  rw [Pi.zero_apply]
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam n 0 s hinj]
    change _ • (X.presheaf.map _).hom ((h.app _).hom (0 : Γ(Y, _))) = (0 : Γ(X, _))
    rw [map_zero, map_zero, smul_zero]
  · exact OModulePresheaf.unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam n 0 s hinj

end GoodReductionJacobian.P2mPrimDeg1

open GoodReductionJacobian.P2mPrimDeg1

end AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs

namespace GoodReductionJacobian.AbelianSchemePropertyBundle

universe u

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.NeronModelInfra hiding schemeHomOverComp
open _root_.GoodReductionJacobian
open scoped TensorProduct DirectSum

open _root_.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs in
open AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero in
open GoodReductionJacobian.P2mPrimDeg1 in
theorem exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (𝒦 : A.OrderedAffineCover)
    (𝒲 : (pullback f f).OrderedAffineCover) (lam₁ lam₂ lam₃ : 𝒲.ι → 𝒦.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst f f ⁻¹ᵁ 𝒦.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd f f ⁻¹ᵁ 𝒦.U (lam₂ w))
    (h₃ : ∀ w, 𝒲.U w ≤ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f,
      pullback.condition.symm⟩).1 ⁻¹ᵁ 𝒦.U (lam₃ w))
    (z : (OModulePresheaf.unit f).cochain 𝒦 1) (hz : (OModulePresheaf.unit f).d 𝒦 1 z = 0) :
    ∃ b : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cochain 𝒲 0,
      (OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 0 b =
        OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (L.mul (pullback.fst f f ≫ f)
          ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 𝒲 𝒦 lam₃ h₃ 1 z -
          OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲 𝒦 lam₁ h₁
            1 z -
          OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲 𝒦 lam₂ h₂
            1 z := by
  classical
  have : IsProper f := hA.proper
  let e : Spec (CommRingCat.of k) ⟶ A := (L.one (𝟙 _)).1
  have he : e ≫ f = 𝟙 _ := (L.one (𝟙 _)).2
  let p₁ := pullback.fst f f
  let p₂ := pullback.snd f f
  let μ : pullback f f ⟶ A := (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f
    f, pullback.condition.symm⟩).1
  have hμ : μ ≫ f = pullback.fst f f ≫ f :=
    (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f,
      pullback.condition.symm⟩).2
  have hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom := by
    refine GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_appTop_fibre_of_isPullback
      hA (RingHom.id k) f (𝟙 A) ?_
    have hid : Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _ :=
      by rw [CommRingCat.ofHom_id]; exact Spec.map_id _
    rw [hid]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  let iX : A ⟶ pullback f f := pullback.lift (𝟙 A) (f ≫ e)
    (by rw [Category.id_comp, Category.assoc, he, Category.comp_id])
  let iY : A ⟶ pullback f f := pullback.lift (f ≫ e) (𝟙 A)
    (by rw [Category.id_comp, Category.assoc, he, Category.comp_id])
  have hiX₁ : iX ≫ pullback.fst f f = 𝟙 A := pullback.lift_fst _ _ _
  have hiX₂ : iX ≫ pullback.snd f f = f ≫ e := pullback.lift_snd _ _ _
  have hiY₁ : iY ≫ pullback.fst f f = f ≫ e := pullback.lift_fst _ _ _
  have hiY₂ : iY ≫ pullback.snd f f = 𝟙 A := pullback.lift_snd _ _ _
  have : IsClosedImmersion iX := by
    have : IsClosedImmersion (iX ≫ pullback.fst f f) := by rw [hiX₁]; infer_instance
    exact IsClosedImmersion.of_comp iX (pullback.fst f f)
  have : IsClosedImmersion iY := by
    have : IsClosedImmersion (iY ≫ pullback.snd f f) := by rw [hiY₂]; infer_instance
    exact IsClosedImmersion.of_comp iY (pullback.snd f f)
  have hone : ∀ (g : A ⟶ Spec (CommRingCat.of k)) (hg : g = f), (⟨f ≫ e,
    by rw [Category.assoc, he, Category.comp_id]⟩ : SchemeHomOver f f) = L.one f := by
    intro g hg
    have := L.one_natural (𝟙 _) f f (Category.comp_id f)
    rw [← this]
    rfl
  have hμX : iX ≫ μ = 𝟙 A := by
    have hψ : iX ≫ (pullback.fst f f ≫ f) = f := by rw [← Category.assoc, hiX₁, Category.id_comp]
    have key := L.mul_natural (pullback.fst f f ≫ f) f iX hψ ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd
      f f, pullback.condition.symm⟩
    have e1 : schemeHomOverComp iX hψ ⟨pullback.fst f f, rfl⟩ = (⟨𝟙 A, Category.id_comp f⟩ :
      SchemeHomOver f f) := Subtype.ext hiX₁
    have e2 : schemeHomOverComp iX hψ ⟨pullback.snd f f, pullback.condition.symm⟩ = L.one f := by
      rw [← hone f rfl]; exact Subtype.ext hiX₂
    rw [e1, e2, L.mul_one] at key
    exact congrArg Subtype.val key
  have hμY : iY ≫ μ = 𝟙 A := by
    have hψ : iY ≫ (pullback.fst f f ≫ f) = f :=
      by rw [← Category.assoc, hiY₁, Category.assoc, he, Category.comp_id]
    have key := L.mul_natural (pullback.fst f f ≫ f) f iY hψ ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd
      f f, pullback.condition.symm⟩
    have e1 : schemeHomOverComp iY hψ ⟨pullback.fst f f, rfl⟩ = L.one f := by
      rw [← hone f rfl]; exact Subtype.ext hiY₁
    have e2 : schemeHomOverComp iY hψ ⟨pullback.snd f f, pullback.condition.symm⟩ = (⟨𝟙 A,
      Category.id_comp f⟩ : SchemeHomOver f f) :=
      Subtype.ext hiY₂
    rw [e1, e2, L.one_mul] at key
    exact congrArg Subtype.val key
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : 𝒦.ι, e ⁻¹ᵁ 𝒦.U j₀ = ⊤ := by
    have hpt : (e.base (IsLocalRing.closedPoint k) : A) ∈ (⊤ : A.Opens) := trivial
    rw [← 𝒦.iSup_eq_top, TopologicalSpace.Opens.mem_iSup] at hpt
    obtain ⟨j₀, hj⟩ := hpt
    refine ⟨j₀, eq_top_iff.mpr fun x _ => ?_⟩
    have hx : x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    change e.base x ∈ 𝒦.U j₀
    rw [hx]; exact hj
  set c : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cochain 𝒲 1 :=
    OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) μ 𝒲 𝒦 lam₃ h₃ 1 z -
      OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲 𝒦 lam₁ h₁ 1 z -
      OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲 𝒦 lam₂ h₂ 1 z
        with hcdef
  have hc : (OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 1 c = 0 := by
    rw [hcdef, map_sub, map_sub, OModulePresheaf.d_unitPullback, OModulePresheaf.d_unitPullback,
      OModulePresheaf.d_unitPullback, hz,
      unitPullback_zero, unitPullback_zero, unitPullback_zero, sub_zero, sub_zero]
  have hrestr : ∀ (i : A ⟶ pullback f f) [IsAffineHom i] (s : (𝒲.comap i).Idx 1)
      (g₃ : ∀ w : (𝒲.comap i).ι, (𝒲.comap i).U w ≤ (i ≫ μ) ⁻¹ᵁ 𝒦.U (lam₃ w))
      (g₁ : ∀ w : (𝒲.comap i).ι, (𝒲.comap i).U w ≤ (i ≫ pullback.fst f f) ⁻¹ᵁ 𝒦.U (lam₁ w))
      (g₂ : ∀ w : (𝒲.comap i).ι, (𝒲.comap i).U w ≤ (i ≫ pullback.snd f f) ⁻¹ᵁ 𝒦.U (lam₂ w)),
      (A.presheaf.map (homOfLE (𝒲.comap_inter_le i s)).op).hom ((i.app (𝒲.inter s)).hom (c s)) =
        (OModulePresheaf.unitPullback (πX := f) (i ≫ μ) (𝒲.comap i) 𝒦 lam₃ g₃ 1 z -
          OModulePresheaf.unitPullback (πX := f) (i ≫ pullback.fst f f) (𝒲.comap i) 𝒦 lam₁ g₁ 1 z -
          OModulePresheaf.unitPullback (πX := f) (i ≫ pullback.snd f f) (𝒲.comap i) 𝒦 lam₂ g₂ 1 z)
            s := by
    intro i _ s g₃ g₁ g₂
    have hμ' := OModulePresheaf.map_app_unitPullback_eq_unitPullback_comp
      (pullback.fst f f ≫ f) f f μ i 𝒲 𝒦 lam₃ h₃ g₃ 1 z s
    have h₁' := OModulePresheaf.map_app_unitPullback_eq_unitPullback_comp
      (pullback.fst f f ≫ f) f f (pullback.fst f f) i 𝒲 𝒦 lam₁ h₁ g₁ 1 z s
    have h₂' := OModulePresheaf.map_app_unitPullback_eq_unitPullback_comp
      (pullback.fst f f ≫ f) f f (pullback.snd f f) i 𝒲 𝒦 lam₂ h₂ g₂ 1 z s
    have hcval : c s =
        OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) μ 𝒲 𝒦 lam₃ h₃ 1 z s -
          OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲 𝒦 lam₁ h₁
            1 z s -
          OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲 𝒦 lam₂ h₂
            1 z s := rfl
    let F : Γ(pullback f f, 𝒲.inter s) →+* Γ(A, (𝒲.comap i).inter s) :=
      (A.presheaf.map (homOfLE (𝒲.comap_inter_le i s)).op).hom.comp (i.app (𝒲.inter s)).hom
    let x₃ : Γ(pullback f f, 𝒲.inter s) :=
      OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) μ 𝒲 𝒦 lam₃ h₃ 1 z s
    let x₁ : Γ(pullback f f, 𝒲.inter s) :=
      OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲 𝒦 lam₁ h₁ 1 z s
    let x₂ : Γ(pullback f f, 𝒲.inter s) :=
      OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲 𝒦 lam₂ h₂ 1 z s
    have hmap : F (c s) = F x₃ - F x₁ - F x₂ :=
      (congrArg F hcval).trans ((map_sub F (x₃ - x₁) x₂).trans
        (congrArg (fun a : Γ(A, (𝒲.comap i).inter s) => a - F x₂) (map_sub F x₃ x₁)))
    exact hmap.trans (congrArg₂ (fun (a b : Γ(A, (𝒲.comap i).inter s)) => a - b)
      (congrArg₂ (fun (a b : Γ(A, (𝒲.comap i).inter s)) => a - b) hμ' h₁') h₂')
  have hle_comp : ∀ (i : A ⟶ pullback f f) [IsAffineHom i] (g : pullback f f ⟶ A) (lam : 𝒲.ι → 𝒦.ι)
      (hl : ∀ w, 𝒲.U w ≤ g ⁻¹ᵁ 𝒦.U (lam w)) (w : (𝒲.comap i).ι), (𝒲.comap i).U w ≤ (i ≫ g) ⁻¹ᵁ 𝒦.U
        (lam w) := by
    intro i _ g lam hl w
    change i ⁻¹ᵁ 𝒲.U w ≤ (i ≫ g) ⁻¹ᵁ 𝒦.U (lam w)
    rw [Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono i (hl w)
  have hslice : ∀ (i : A ⟶ pullback f f) [IsAffineHom i] (hiμ : i ≫ μ = 𝟙 A)
      (q q' : pullback f f ⟶ A) (lamq lamq' : 𝒲.ι → 𝒦.ι) (hq : ∀ w, 𝒲.U w ≤ q ⁻¹ᵁ 𝒦.U (lamq w))
      (hq' : ∀ w, 𝒲.U w ≤ q' ⁻¹ᵁ 𝒦.U (lamq' w)),
      i ≫ q = 𝟙 A → i ≫ q' = f ≫ e →
      ∃ b : (OModulePresheaf.unit f).cochain (𝒲.comap i) 0, (OModulePresheaf.unit f).d (𝒲.comap i)
        0 b =
        OModulePresheaf.unitPullback (πX := f) (i ≫ μ) (𝒲.comap i) 𝒦 lam₃ (hle_comp i μ lam₃ h₃) 1
          z -
          OModulePresheaf.unitPullback (πX := f) (i ≫ q) (𝒲.comap i) 𝒦 lamq (hle_comp i q lamq hq)
            1 z -
          OModulePresheaf.unitPullback (πX := f) (i ≫ q') (𝒲.comap i) 𝒦 lamq' (hle_comp i q' lamq'
            hq') 1 z := by
    intro i _ hiμ q q' lamq lamq' hq hq' hiq hiq'
    have g₃ : ∀ w : (𝒲.comap i).ι, (𝒲.comap i).U w ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam₃ w) := fun w => by
      rw [← hiμ]; exact hle_comp i μ lam₃ h₃ w
    have g₁ : ∀ w : (𝒲.comap i).ι, (𝒲.comap i).U w ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lamq w) := fun w => by
      rw [← hiq]; exact hle_comp i q lamq hq w
    have g₂ : ∀ w : (𝒲.comap i).ι, (𝒲.comap i).U w ≤ (f ≫ e) ⁻¹ᵁ 𝒦.U (lamq' w) := fun w => by
      rw [← hiq']; exact hle_comp i q' lamq' hq' w
    have g₀ : ∀ w : (𝒲.comap i).ι, (𝒲.comap i).U w ≤ (f ≫ e) ⁻¹ᵁ 𝒦.U ((fun _ => j₀) w) := fun w =>
      by
      rw [Scheme.Hom.comp_preimage, hj₀, Scheme.Hom.preimage_top]; exact le_top
    rw [unitPullback_congr f f (i ≫ μ) (𝟙 A) hiμ _ _ _ _ g₃, unitPullback_congr f f (i ≫ q) (𝟙 A)
      hiq _ _ _ _ g₁,
      unitPullback_congr f f (i ≫ q') (f ≫ e) hiq' _ _ _ _ g₂]
    obtain ⟨b₁, hb₁⟩ :=
      OModulePresheaf.exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero f f (𝟙 A)
      (𝒲.comap i) 𝒦
      lam₃ lamq g₃ g₁ z hz
    obtain ⟨b₂, hb₂⟩ :=
      OModulePresheaf.exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero f f (f ≫ e)
      (𝒲.comap i) 𝒦
      lamq' (fun _ => j₀) g₂ g₀ z hz
    rw [unitPullback_const_one, sub_zero] at hb₂
    exact ⟨b₁ - b₂, by rw [map_sub, hb₁, hb₂]⟩
  have : IsAffineHom iX := inferInstance
  have : IsAffineHom iY := inferInstance
  obtain ⟨b, hb⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap f f
    hX hX e he e he
    (pullback.fst f f) (pullback.snd f f) (IsPullback.of_hasPullback f f) iX hiX₁ hiX₂ iY hiY₁ hiY₂
      𝒲 c hc
    (by
      obtain ⟨b, hb⟩ := hslice iX hμX (pullback.fst f f) (pullback.snd f f) lam₁ lam₂ h₁ h₂ hiX₁
        hiX₂
      refine ⟨b, ?_⟩
      rw [hb]; funext s
      exact (hrestr iX s _ _ _).symm)
    (by
      obtain ⟨b, hb⟩ := hslice iY hμY (pullback.snd f f) (pullback.fst f f) lam₂ lam₁ h₂ h₁ hiY₂
        hiY₁
      refine ⟨b, ?_⟩
      rw [hb]; funext s
      rw [hrestr iY s (hle_comp iY μ lam₃ h₃) (hle_comp iY _ lam₁ h₁) (hle_comp iY _ lam₂ h₂)]
      simp only [Pi.sub_apply]
      exact sub_right_comm _ _ _)
  exact ⟨b, by rw [hb]⟩
end GoodReductionJacobian.AbelianSchemePropertyBundle
end ProofImplementation
