/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_bijective_app_of_isPullback_of_bijective_of_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap

/-!
# Scheme Hom bijective app of is Pullback of bijective of is Affine Open
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_Hom_bijective_app_of_isPullback_of_bijective_of_isAffineOpen

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace C2KunnethH0Aux

theorem flat_of_field {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    Flat f := by
  have : Subsingleton ↥(Spec (CommRingCat.of k)) := (inferInstance : Subsingleton (PrimeSpectrum k))
  have : IsIntegral (Spec (CommRingCat.of k)) := inferInstance
  infer_instance

theorem bijective_appLE_top_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    Function.Bijective (f.appLE ⊤ ⊤ e).hom ↔ Function.Bijective f.appTop.hom := by
  rw [Scheme.Hom.appLE_congr f e rfl (show (⊤ : X.Opens) = f ⁻¹ᵁ ⊤ by simp)
    (fun φ => Function.Bijective φ.hom), Scheme.Hom.appLE_eq_app]
  exact Iff.rfl

end C2KunnethH0Aux

open C2KunnethH0Aux in
theorem _root_.AlgebraicGeometry.Scheme.Hom.bijective_app_of_isPullback_of_bijective_of_isAffineOpen
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fY] [IsSeparated fY]
    (hY : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fY.appTop).hom)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective (p₁.app U).hom := by
  have : Flat fX := flat_of_field fX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace fY
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated fY
  have : IsIso ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fY.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hY
  have hfY : IsIso fY.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of k)).inv _
  have hUSX : U ≤ fX ⁻¹ᵁ ⊤ := le_top
  have hUST : (⊤ : Y.Opens) ≤ fY ⁻¹ᵁ ⊤ := by simp
  have hUY : p₁ ⁻¹ᵁ U = p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ ⊤ := by simp
  have : IsIso (fY.appLE ⊤ ⊤ hUST) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ((bijective_appLE_top_iff fY hUST).mpr (ConcreteCategory.bijective_of_isIso fY.appTop))
  have hps := isIso_pushoutSection_of_isQuasiSeparated_of_flat_left hP hUST hUSX hUY
    (isAffineOpen_top _) hU
    (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
    (by rw [TopologicalSpace.Opens.coe_top]; exact isQuasiSeparated_univ)
  have hcomp : pushout.inl (fX.appLE ⊤ U hUSX) (fY.appLE ⊤ ⊤ hUST) ≫
      pushoutSection hP hUST hUSX hUY = p₁.appLE U (p₁ ⁻¹ᵁ U) (by simp) :=
    pushout.inl_desc _ _ _
  have hiso : IsIso (p₁.appLE U (p₁ ⁻¹ᵁ U) (by simp)) := by
    rw [← hcomp]
    infer_instance
  have := ConcreteCategory.bijective_of_isIso (p₁.appLE U (p₁ ⁻¹ᵁ U) le_rfl)
  rwa [Scheme.Hom.appLE_eq_app] at this
end Scheme_Hom_bijective_app_of_isPullback_of_bijective_of_isAffineOpen
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
