/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_isDomain_tensorProduct_sections_of_geometricallyIntegral.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.RingTheory.TensorProduct.Maps
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover

/-!
# Tensor products of affine sections of a geometrically integral scheme

A nontrivial scalar extension of the section ring of an affine open in a geometrically
integral scheme to a field is a domain.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace isDomain_tensorProduct_sections_of_geometricallyIntegral

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace NoncritGeom

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (U : C.Opens) (hU : IsAffineOpen U) (K : Type u) [Field K] [Algebra R K]

theorem ι_comp_eq :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    U.ι ≫ c = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(C, U))) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom c U
  have h1 : hU.fromSpec ≫ c = Spec.map (c.appLE ⊤ U le_top) ≫ (isAffineOpen_top (Spec (.of
      R))).fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec c (isAffineOpen_top _) hU le_top).symm
  have h2 : (isAffineOpen_top (Spec (CommRingCat.of R))).fromSpec = Spec.map (Scheme.ΓSpecIso
      (.of R)).inv := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have h3 : (CommRingCat.ofHom (algebraMap R Γ(C, U))) = (Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE
      ⊤ U le_top := rfl
  rw [h3, Spec.map_comp, ← h2, ← h1, ← Category.assoc, IsAffineOpen.isoSpec_hom hU,
    ← IsAffineOpen.isoSpec_inv_ι hU, ← Category.assoc, ← IsAffineOpen.isoSpec_hom hU,
        Iso.hom_inv_id,
    Category.id_comp]

/-- The inverse image of the affine open in the field base change identifies with the spectrum
    of the tensor-product ring. -/
noncomputable def preimageIso :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    (↑((pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ U) : Scheme.{u}) ≅
      Spec (.of (Γ(C, U) ⊗[R] K)) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  (pullbackRestrictIsoRestrict (pullback.fst c g) U).symm
    ≪≫ pullbackSymmetry _ _
    ≪≫ pullbackRightPullbackFstIso c g U.ι
    ≪≫ asIso (pullback.map (U.ι ≫ c) g (Spec.map (CommRingCat.ofHom (algebraMap R Γ(C, U)))) g
          hU.isoSpec.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ι_comp_eq c U hU]) (by simp))
    ≪≫ pullbackSpecIso R Γ(C, U) K
include hU in
private theorem isDomain (hne : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U; Nontrivial
    (K ⊗[R] Γ(C, U)))
    [GeometricallyIntegral c] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    IsDomain (K ⊗[R] Γ(C, U)) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom c U
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : IsIntegral (pullback c g) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback c g)
  let U' : (pullback c g).Opens := (pullback.fst c g) ⁻¹ᵁ U
  let e : (↑U' : Scheme.{u}) ≅ Spec (.of (Γ(C, U) ⊗[R] K)) := preimageIso c U hU K
  have := hne
  have : Nontrivial (Γ(C, U) ⊗[R] K) := (Algebra.TensorProduct.comm R Γ(C, U) K).toEquiv.nontrivial
  have : Nonempty (Spec (CommRingCat.of (Γ(C, U) ⊗[R] K))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (Γ(C, U) ⊗[R] K)))
  have : Nonempty U' := ⟨e.inv.base (Classical.arbitrary _)⟩
  have : IsIntegral (↑U' : Scheme.{u}) := inferInstance
  have : IsIntegral (Spec (CommRingCat.of (Γ(C, U) ⊗[R] K))) := IsIntegral.of_isIso e.hom
  have : IsDomain Γ(Spec (CommRingCat.of (Γ(C, U) ⊗[R] K)), ⊤) := inferInstance
  have : IsDomain (Γ(C, U) ⊗[R] K) :=
    MulEquiv.isDomain Γ(Spec (CommRingCat.of (Γ(C, U) ⊗[R] K)), ⊤)
      (Scheme.ΓSpecIso (.of (Γ(C, U) ⊗[R] K))).commRingCatIsoToRingEquiv.symm.toMulEquiv
  exact MulEquiv.isDomain (Γ(C, U) ⊗[R] K) (Algebra.TensorProduct.comm R K Γ(C, U)).toMulEquiv

end NoncritGeom

theorem _root_.AlgebraicGeometry.isDomain_tensorProduct_sections_of_geometricallyIntegral
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [GeometricallyIntegral c] (U : C.Opens) (hU : IsAffineOpen U)
    (K : Type u) [Field K] [Algebra R K]
    (hne : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U; Nontrivial (K ⊗[R] Γ(C, U))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    IsDomain (K ⊗[R] Γ(C, U)) :=
  NoncritGeom.isDomain c U hU K hne
end isDomain_tensorProduct_sections_of_geometricallyIntegral
end AlgebraicCurves.Geometry.Curves.Proofs
end ProofImplementation
