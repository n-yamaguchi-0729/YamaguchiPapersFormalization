/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_flat_aeval_of_twoChartPoleDatum.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Foundations.Algebra.Module_Flat_of_finitePresentation_of_forall_flat_residueField_tensorProduct
import Nyll.AlgebraicCurves.Geometry.Curves.isDomain_tensorProduct_sections_of_geometricallyIntegral
import Nyll.AlgebraicCurves.Models.Gluing.SmoothProperCurve_injective_aeval_tensor_of_twoChartPoleDatum

/-!
# Smooth Proper Curve flat aeval of two Chart Pole Datum
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Gluing.Proofs.SmoothProperCurve_flat_aeval_of_twoChartPoleDatum

universe u

open scoped TensorProduct
open Polynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace U3bFLAT

theorem flat_aeval_of_injective {κ D : Type u} [Field κ] [CommRing D] [IsDomain D] [Algebra κ D] (y
  : D)
    (hinj : Function.Injective (Polynomial.aeval y : κ[X] →ₐ[κ] D)) :
    (Polynomial.aeval y : κ[X] →ₐ[κ] D).toRingHom.Flat := by
  let : Algebra κ[X] D := (Polynomial.aeval y : κ[X] →ₐ[κ] D).toRingHom.toAlgebra
  have : Module.IsTorsionFree κ[X] D := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  change Module.Flat κ[X] D
  infer_instance

theorem flat_of_subsingleton {A D : Type u} [CommRing A] [CommRing D] [Subsingleton D] (φ : A →+*
  D) :
    φ.Flat := by
  let : Algebra A D := φ.toAlgebra
  change Module.Flat A D
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f _
  have : Subsingleton (N ⊗[A] D) := inferInstance
  exact Function.injective_of_subsingleton _

section Sections

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))

theorem flat_sections [Flat c] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.Flat R Γ(X, U) := by
  have h : RingHom.Flat (c.appLE ⊤ U le_top).hom :=
    HasRingHomProperty.appLE (P := @Flat) (f := c) inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩
      le_top
  have h2 : RingHom.Flat ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp
      (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (.of
        R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact h2

theorem finitePresentation_sections [LocallyOfFinitePresentation c] {U : X.Opens} (hU :
  IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Algebra.FinitePresentation R Γ(X, U) := by
  have h : RingHom.FinitePresentation (c.appLE ⊤ U le_top).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) (f := c) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h2 : RingHom.FinitePresentation ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom :=
    by
    rw [CommRingCat.hom_comp]
    exact RingHom.finitePresentation_respectsIso.2 _
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv h
  exact h2

end Sections

section FibreMap

variable {R : Type u} [CommRing R] {B : Type u} [CommRing B] [Algebra R B] (f : B)
  (κ : Type u) [Field κ] [Algebra R κ]

theorem fibreMap_comp_polyEquivTensor
    [Algebra R[X] B] [IsScalarTower R R[X] B] (hX : algebraMap R[X] B Polynomial.X = f) :
    (Algebra.TensorProduct.map (AlgHom.id κ κ) (IsScalarTower.toAlgHom R R[X] B)).toRingHom.comp
        (polyEquivTensor R κ).toRingHom =
      (Polynomial.aeval ((1 : κ) ⊗ₜ[R] f) : κ[X] →ₐ[κ] κ ⊗[R] B).toRingHom := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp only [AlgHom.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      polyEquivTensor_apply, eval₂_C, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_one,
      aeval_C, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  · change (Algebra.TensorProduct.map (AlgHom.id κ κ) (IsScalarTower.toAlgHom R R[X] B))
      ((polyEquivTensor R κ) Polynomial.X) =
      (Polynomial.aeval ((1 : κ) ⊗ₜ[R] f) : κ[X] →ₐ[κ] κ ⊗[R] B) Polynomial.X
    simp only [polyEquivTensor_apply, eval₂_X, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, IsScalarTower.coe_toAlgHom', hX, aeval_X]

theorem flat_fibreMap_of_flat_aeval
    [Algebra R[X] B] [IsScalarTower R R[X] B] (hX : algebraMap R[X] B Polynomial.X = f)
    (h : (Polynomial.aeval ((1 : κ) ⊗ₜ[R] f) : κ[X] →ₐ[κ] κ ⊗[R] B).toRingHom.Flat) :
    (Algebra.TensorProduct.map (AlgHom.id κ κ) (IsScalarTower.toAlgHom R R[X] B)).toRingHom.Flat :=
      by
  have key := fibreMap_comp_polyEquivTensor f κ hX
  have h1 : ((Algebra.TensorProduct.map (AlgHom.id κ κ) (IsScalarTower.toAlgHom R R[X]
    B)).toRingHom.comp
        (polyEquivTensor R κ).toRingHom).Flat := by
    rw [key]; exact h
  have h2 := RingHom.Flat.respectsIso.2 _ (polyEquivTensor R κ).symm.toRingEquiv h1
  have h3 : ((Algebra.TensorProduct.map (AlgHom.id κ κ) (IsScalarTower.toAlgHom R R[X]
    B)).toRingHom.comp
        (polyEquivTensor R κ).toRingHom).comp (polyEquivTensor R κ).symm.toRingEquiv.toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id κ κ) (IsScalarTower.toAlgHom R R[X] B)).toRingHom := by
    refine RingHom.ext fun y => ?_
    change (Algebra.TensorProduct.map (AlgHom.id κ κ) (IsScalarTower.toAlgHom R R[X] B))
        ((polyEquivTensor R κ) ((polyEquivTensor R κ).symm y)) = _
    rw [AlgEquiv.apply_symm_apply]
    rfl
  rw [h3] at h2
  exact h2

end FibreMap

theorem main
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Flat := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom c U
  have : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have : Module.Flat R Γ(C, U) := flat_sections c hU
  have : Algebra.FinitePresentation R Γ(C, U) := finitePresentation_sections c hU
  let algXB : Algebra R[X] Γ(C, U) := (Polynomial.aeval f : R[X] →ₐ[R] Γ(C, U)).toRingHom.toAlgebra
  have : IsScalarTower R R[X] Γ(C, U) := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R Γ(C, U) r = (Polynomial.aeval f : R[X] →ₐ[R] Γ(C, U)) (algebraMap R R[X] r)
    rw [AlgHom.commutes]
  have hX : algebraMap R[X] Γ(C, U) Polynomial.X = f := Polynomial.aeval_X f
  change Module.Flat R[X] Γ(C, U)
  refine Module.Flat.of_finitePresentation_of_forall_flat_residueField_tensorProduct
    (R := R) (A := R[X]) (B := Γ(C, U)) fun p _ => ?_
  refine flat_fibreMap_of_flat_aeval f p.ResidueField hX ?_
  by_cases hne : Nontrivial (p.ResidueField ⊗[R] Γ(C, U))
  · have := AlgebraicGeometry.isDomain_tensorProduct_sections_of_geometricallyIntegral c U hU
      p.ResidueField hne
    exact flat_aeval_of_injective _
      (AlgebraicGeometry.SmoothProperCurve.injective_aeval_tensor_of_twoChartPoleDatum
        R c ε U V hU hV hUV hUε f g hf hg hfg p.ResidueField hne)
  · have : Subsingleton (p.ResidueField ⊗[R] Γ(C, U)) := not_nontrivial_iff_subsingleton.mp hne
    exact flat_of_subsingleton _

end U3bFLAT

open scoped TensorProduct in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra in
theorem _root_.AlgebraicGeometry.SmoothProperCurve.flat_aeval_of_twoChartPoleDatum
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Flat :=
  U3bFLAT.main R c ε U V hU hV hUV hUε f g hf hg hfg
end AlgebraicCurves.Models.Gluing.Proofs.SmoothProperCurve_flat_aeval_of_twoChartPoleDatum
end ProofImplementation
