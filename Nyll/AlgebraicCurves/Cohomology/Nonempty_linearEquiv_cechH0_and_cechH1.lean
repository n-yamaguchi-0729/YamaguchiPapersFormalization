/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.AlgebraicCurves.Models.Places
import Nyll.AlgebraicCurves.Models.Eq_of_range_stalk_eq
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Models.Range_algebraMap_functionField_eq_iInf_of_isAffineOpen

/-!
Equivalences between geometric structure-sheaf cohomology and the two-chart function-field Cech
model.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Proofs.Nonempty_linearEquiv_cechH0_and_cechH1
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open CategoryTheory AlgebraicGeometry

universe u

namespace TwoChartCech
open _root_.TwoChartCech
open _root_.TwoChartCech

universe uR uK uC

variable {R : Type uR} [CommRing R]
variable {K0 K1 : Type uK} [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
variable {C0 C1 : Type uK} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

theorem kerMap_bijective_of_bijective (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0)
    (ι1 : K1 →ₗ[R] C1) (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (h0 : Function.Bijective ι0)
    (h1 : Function.Injective ι1) : Function.Bijective (kerMap dK d ι0 ι1 comm) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply h0.1
    exact congrArg Subtype.val hxy
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := h0.2 y
    have hx : x ∈ LinearMap.ker dK := by
      rw [LinearMap.mem_ker] at hy ⊢
      apply h1
      rw [map_zero, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply, hy]
    exact ⟨⟨x, hx⟩, rfl⟩

theorem cokerMap_bijective_of_bijective (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0)
    (ι1 : K1 →ₗ[R] C1) (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (h0 : Function.Surjective ι0)
    (h1 : Function.Bijective ι1) : Function.Bijective (cokerMap dK d ι0 ι1 comm) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_ker] at hq
    change Submodule.Quotient.mk (ι1 y) = 0 at hq
    rw [Submodule.Quotient.mk_eq_zero] at hq ⊢
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hq
    obtain ⟨x, rfl⟩ := h0 c
    refine ⟨x, h1.1 ?_⟩
    rw [← hc, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply]
  · intro q
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨y, rfl⟩ := h1.2 c
    exact ⟨Submodule.Quotient.mk y, rfl⟩

end TwoChartCech

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

variable {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsIntegral C]

theorem placesOf_inf [IsSeparated c] [SmoothOfRelativeDimension 1 c] (U V : C.Opens) :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c (U ⊓ V) = placesOf c U ∩ placesOf c V := by
  let := (baseToFunctionField c).toAlgebra
  apply Set.Subset.antisymm
  · exact fun v hv => ⟨placesOf_mono c inf_le_left hv, placesOf_mono c inf_le_right hv⟩
  · rintro v ⟨⟨x, hxU, hx, hvx⟩, ⟨y, hyV, -, hvy⟩⟩
    have hxy : x = y := eq_of_range_stalk_eq c x y (hvx.trans hvy.symm)
    subst hxy
    exact ⟨x, ⟨hxU, hyV⟩, hx, hvx⟩

theorem germToFunctionField_algebraMap (U : C.Opens) [Nonempty U] (r : K) :
    (C.germToFunctionField U).hom ((Scheme.TwoAffineOpenCover.algebraOfHom c U).algebraMap r)
      = baseToFunctionField c r := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  change (c.appLE ⊤ U le_top ≫ C.germToFunctionField U).hom _
    = (c.appTop ≫ C.presheaf.germ ⊤ (genericPoint C) trivial).hom _
  congr 2
  dsimp only [Scheme.Hom.appLE]
  rw [Category.assoc]
  erw [TopCat.Presheaf.germ_res]
  try rfl

omit [IsIntegral C] in
theorem germToFunctionField_map [IrreducibleSpace C] {U V : C.Opens} [Nonempty U] [Nonempty V]
    (h : V ≤ U) (s : Γ(C, U)) :
    (C.germToFunctionField V).hom ((C.presheaf.map (homOfLE h).op).hom s)
      = (C.germToFunctionField U).hom s := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply]
  erw [TopCat.Presheaf.germ_res]
  try rfl

/-- The linear germ map from sections on an open set to the function field. -/
noncomputable def germLinear (U : C.Opens) [Nonempty U] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := (baseToFunctionField c).toAlgebra
    Γ(C, U) →ₗ[K] C.functionField :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI := (baseToFunctionField c).toAlgebra
  { toFun := (C.germToFunctionField U).hom
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r s => by
      rw [Algebra.smul_def, map_mul, germToFunctionField_algebraMap, RingHom.id_apply,
        Algebra.smul_def]
      rfl }

theorem germLinear_apply (U : C.Opens) [Nonempty U] (s : Γ(C, U)) :
    germLinear c U s = (C.germToFunctionField U).hom s := rfl

theorem range_germ_eq_lSpaceOn (U : C.Opens) [Nonempty U]
    (hsec : letI := (baseToFunctionField c).toAlgebra
      (C.germToFunctionField U).hom.range = ⨅ v ∈ placesOf c U, v.toValuationSubring.toSubring) :
    letI := (baseToFunctionField c).toAlgebra
    Set.range (germLinear c U) = (lSpaceOn (placesOf c U) (0 : Divisor K C.functionField) : Set
      C.functionField) := by
  let := (baseToFunctionField c).toAlgebra
  ext f
  have h1 : f ∈ Set.range (germLinear c U) ↔ f ∈ (C.germToFunctionField U).hom.range := by
    simp only [Set.mem_range, RingHom.mem_range, germLinear_apply]
  rw [h1, hsec, SetLike.mem_coe, mem_lSpaceOn_iff]
  simp only [Subring.mem_iInf, Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
  refine forall₂_congr fun v _ => ?_
  exact (Place.mem_iff_adicValuation_le_one v)

/-- Identify affine sections with rational functions regular at the places of the open set. -/
noncomputable def germEquiv (U : C.Opens) [Nonempty U]
    (hsec : letI := (baseToFunctionField c).toAlgebra
      (C.germToFunctionField U).hom.range = ⨅ v ∈ placesOf c U, v.toValuationSubring.toSubring) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := (baseToFunctionField c).toAlgebra
    Γ(C, U) ≃ₗ[K] ↥(lSpaceOn (placesOf c U) (0 : Divisor K C.functionField)) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI := (baseToFunctionField c).toAlgebra
  LinearEquiv.ofBijective
    (LinearMap.codRestrict _ (germLinear c U) (fun s => by
      have : germLinear c U s ∈ Set.range (germLinear c U) := ⟨s, rfl⟩
      rw [range_germ_eq_lSpaceOn c U hsec] at this
      exact this))
    ⟨fun x y hxy => Scheme.germToFunctionField_injective C U (congrArg Subtype.val hxy),
     fun ⟨f, hf⟩ => by
      have : f ∈ Set.range (germLinear c U) := by rw [range_germ_eq_lSpaceOn c U hsec]; exact hf
      obtain ⟨s, rfl⟩ := this
      exact ⟨s, rfl⟩⟩

theorem coe_germEquiv_apply (U : C.Opens) [Nonempty U]
    (hsec : letI := (baseToFunctionField c).toAlgebra
      (C.germToFunctionField U).hom.range = ⨅ v ∈ placesOf c U, v.toValuationSubring.toSubring)
    (s : Γ(C, U)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := (baseToFunctionField c).toAlgebra
    ((germEquiv c U hsec s : ↥(lSpaceOn (placesOf c U) (0 : Divisor K C.functionField))) :
      C.functionField)
      = (C.germToFunctionField U).hom s := rfl

theorem nonempty_linearEquiv_cechH0_and_cechH1' [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (𝒱 : C.TwoAffineOpenCover) (h0 : Nonempty 𝒱.U0) (h1 : Nonempty 𝒱.U1) :
    letI := (baseToFunctionField c).toAlgebra
    Nonempty ((𝒱.structureSheafSections c).H0
        ≃ₗ[K] ↥(cechH0 (placesOf c 𝒱.U0) (placesOf c 𝒱.U1) (0 : Divisor K C.functionField))) ∧
      Nonempty ((𝒱.structureSheafSections c).H1
        ≃ₗ[K] cechH1 (placesOf c 𝒱.U0) (placesOf c 𝒱.U1) (0 : Divisor K C.functionField)) := by
  let := (baseToFunctionField c).toAlgebra
  have := h0
  have := h1
  have h01' : ((𝒱.U0 ⊓ 𝒱.U1 : C.Opens) : Set C).Nonempty :=
    nonempty_preirreducible_inter 𝒱.U0.isOpen 𝒱.U1.isOpen
      (Set.nonempty_coe_sort.mp h0) (Set.nonempty_coe_sort.mp h1)
  have h01 : Nonempty (𝒱.U0 ⊓ 𝒱.U1 : C.Opens) := h01'.to_subtype
  have hS01 : placesOf c (𝒱.U0 ⊓ 𝒱.U1) = placesOf c 𝒱.U0 ∩ placesOf c 𝒱.U1 :=
    placesOf_inf c 𝒱.U0 𝒱.U1
  have hsec' : ∀ (U : C.Opens), IsAffineOpen U → ∀ [Nonempty U],
      (C.germToFunctionField U).hom.range = ⨅ v ∈ placesOf c U, v.toValuationSubring.toSubring :=
    fun U hU _ => range_algebraMap_functionField_eq_iInf_of_isAffineOpen c U hU
  let S := 𝒱.structureSheafSections c
  let e0 : S.M0 ≃ₗ[K] ↥(lSpaceOn (placesOf c 𝒱.U0) (0 : Divisor K C.functionField)) :=
    germEquiv c 𝒱.U0 (hsec' _ 𝒱.isAffineOpen_U0)
  let e1 : S.M1 ≃ₗ[K] ↥(lSpaceOn (placesOf c 𝒱.U1) (0 : Divisor K C.functionField)) :=
    germEquiv c 𝒱.U1 (hsec' _ 𝒱.isAffineOpen_U1)
  let e01' := germEquiv c (𝒱.U0 ⊓ 𝒱.U1) (hsec' _ 𝒱.isAffineOpen_inf)
  have hL01 : lSpaceOn (placesOf c (𝒱.U0 ⊓ 𝒱.U1)) (0 : Divisor K C.functionField)
      = lSpaceOn (placesOf c 𝒱.U0 ∩ placesOf c 𝒱.U1) 0 := by rw [hS01]
  let e01 : S.M01 ≃ₗ[K] ↥(lSpaceOn (placesOf c 𝒱.U0 ∩ placesOf c 𝒱.U1)
      (0 : Divisor K C.functionField)) := e01'.trans (LinearEquiv.ofEq _ _ hL01)
  let := Scheme.TwoAffineOpenCover.algebraOfHom c 𝒱.U0
  let := Scheme.TwoAffineOpenCover.algebraOfHom c 𝒱.U1
  let := Scheme.TwoAffineOpenCover.algebraOfHom c (𝒱.U0 ⊓ 𝒱.U1)
  let ι0 : S.M0 × S.M1
      →ₗ[K] ↥(lSpaceOn (placesOf c 𝒱.U0) (0 : Divisor K C.functionField))
        × ↥(lSpaceOn (placesOf c 𝒱.U1) (0 : Divisor K C.functionField)) :=
    LinearMap.prodMap e0.toLinearMap e1.toLinearMap
  let ι1 : S.M01
      →ₗ[K] ↥(lSpaceOn (placesOf c 𝒱.U0 ∩ placesOf c 𝒱.U1) (0 : Divisor K C.functionField)) :=
    e01.toLinearMap
  have comm : cechDiff (placesOf c 𝒱.U0) (placesOf c 𝒱.U1) 0 ∘ₗ ι0
      = ι1 ∘ₗ (𝒱.structureSheafSections c).cechDiff := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    have lhs : ((cechDiff (placesOf c 𝒱.U0) (placesOf c 𝒱.U1) 0 ∘ₗ ι0) p : C.functionField)
        = (C.germToFunctionField 𝒱.U1).hom p.2 - (C.germToFunctionField 𝒱.U0).hom p.1 := by
      rw [LinearMap.comp_apply, coe_cechDiff_apply]
      rfl
    have rhs : ((ι1 ∘ₗ (𝒱.structureSheafSections c).cechDiff) p : C.functionField)
        = (C.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom ((𝒱.structureSheafSections c).cechDiff p) := rfl
    rw [lhs]
    refine Eq.trans ?_ rhs.symm
    rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Cover.lineBundle_r1_apply,
      TwoChartCech.Cover.lineBundle_r0_apply, Units.val_one, one_mul]
    change _ = (C.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom
        (((C.presheaf.map (homOfLE inf_le_right).op).hom p.2 : Γ(C, 𝒱.U0 ⊓ 𝒱.U1))
          - (C.presheaf.map (homOfLE inf_le_left).op).hom p.1)
    rw [← germToFunctionField_map (C := C) (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1) p.2,
      ← germToFunctionField_map (C := C) (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0) p.1]
    exact (map_sub _ _ _).symm
  have hι0 : Function.Bijective ι0 :=
    ⟨fun x y hxy => Prod.ext (e0.injective (congrArg Prod.fst hxy)) (e1.injective (congrArg
      Prod.snd hxy)),
     fun q => ⟨(e0.symm q.1, e1.symm q.2), Prod.ext (e0.apply_symm_apply q.1) (e1.apply_symm_apply
       q.2)⟩⟩
  have hι1 : Function.Bijective ι1 := e01.bijective
  exact ⟨⟨LinearEquiv.ofBijective _
      (TwoChartCech.kerMap_bijective_of_bijective ((𝒱.structureSheafSections c).cechDiff)
        (cechDiff (placesOf c 𝒱.U0) (placesOf c 𝒱.U1) 0) ι0 ι1 comm hι0 hι1.1)⟩,
    ⟨LinearEquiv.ofBijective _
      (TwoChartCech.cokerMap_bijective_of_bijective ((𝒱.structureSheafSections c).cechDiff)
        (cechDiff (placesOf c 𝒱.U0) (placesOf c 𝒱.U1) 0) ι0 ι1 comm hι0.2 hι1)⟩⟩

end AlgebraicCurve

open _root_.AlgebraicCurves.Cohomology.Proofs in
open _root_.AlgebraicCurve Nonempty_linearEquiv_cechH0_and_cechH1.AlgebraicCurve in
theorem _root_.AlgebraicCurve.nonempty_linearEquiv_cechH0_and_cechH1 {K : Type u} [Field K] {C :
    Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (h0 : Nonempty 𝒱.U0) (h1 : Nonempty 𝒱.U1) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Nonempty ((𝒱.structureSheafSections c).H0 ≃ₗ[K]
        ↥(AlgebraicCurve.cechH0 (AlgebraicCurve.placesOf c 𝒱.U0) (AlgebraicCurve.placesOf c 𝒱.U1)
            (0 : AlgebraicCurve.Divisor K C.functionField))) ∧
      Nonempty ((𝒱.structureSheafSections c).H1 ≃ₗ[K]
        AlgebraicCurve.cechH1 (AlgebraicCurve.placesOf c 𝒱.U0) (AlgebraicCurve.placesOf c 𝒱.U1)
            (0 : AlgebraicCurve.Divisor K C.functionField)) :=
  nonempty_linearEquiv_cechH0_and_cechH1' c 𝒱 h0 h1
end AlgebraicCurves.Cohomology.Proofs.Nonempty_linearEquiv_cechH0_and_cechH1
end ProofImplementation
