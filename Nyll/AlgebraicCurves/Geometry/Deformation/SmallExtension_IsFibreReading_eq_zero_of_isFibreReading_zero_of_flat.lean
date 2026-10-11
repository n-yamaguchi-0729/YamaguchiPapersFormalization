/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmallExtension_IsFibreReading_eq_zero_of_isFibreReading_zero_of_flat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic.Choose
import Mathlib.LinearAlgebra.BilinearMap
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OrderedAffineCoverCochainPullback
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.CechObstruction
import Nyll.AlgebraicCurves.Geometry.Sheaves.KaehlerModule
import Nyll.SchemeTheory.Affine.PullbackSectionsPushout

/-!
# Small Extension Is Fibre Reading eq zero of is Fibre Reading zero of flat
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Deformation.Proofs
namespace SmallExtension_IsFibreReading_eq_zero_of_isFibreReading_zero_of_flat


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.IsLocalRing
open _root_.AlgebraicGeometry.SmallExtension
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover


open scoped TensorProduct

universe u

theorem
  _root_.AlgebraicGeometry.SmallExtension.IsFibreReading.eq_zero_of_isFibreReading_zero_of_flat
    {B₁ : Type u} [CommRing B₁] [IsLocalRing B₁]
    (V : Type u) [AddCommGroup V] [Module (ResidueField B₁) V] [Module.Finite (ResidueField B₁) V]
    [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V] (ι : V →ₗ[B₁] B₁)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) [Flat f]
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of (ResidueField B₁))) (i : Xk ⟶ X)
    (hi : IsPullback i fk f (Spec.map (CommRingCat.ofHom (residue B₁))))
    (U : X.Opens) (hU : IsAffineOpen U) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) (hW' : i ⁻¹ᵁ U ≤ W)
    (δ : Γ(X, U)) (hδ : IsFibreReading V ι f fk i U W hW δ 0) :
    δ = 0 := by
  classical
  obtain rfl : W = i ⁻¹ᵁ U := le_antisymm hW hW'
  obtain ⟨n, v, s, hsum, hread⟩ := hδ
  let iA : Algebra B₁ Γ(X, U) := f.sectionsAlgebra U
  let iAk : Algebra (ResidueField B₁) Γ(Xk, i ⁻¹ᵁ U) := fk.sectionsAlgebra (i ⁻¹ᵁ U)
  let iT : Algebra Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) := (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  let iB : Algebra B₁ Γ(Xk, i ⁻¹ᵁ U) :=
    ((algebraMap (ResidueField B₁) Γ(Xk, i ⁻¹ᵁ U)).comp (algebraMap B₁ (ResidueField B₁))).toAlgebra
  have : IsScalarTower B₁ (ResidueField B₁) Γ(Xk, i ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _
    => rfl)
  have htop : (Spec.map (CommRingCat.ofHom (residue B₁))).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom (residue B₁))).appTop := Scheme.Hom.appLE_eq_app _
  have hsq : ∀ b : B₁, algebraMap Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) (algebraMap B₁ Γ(X, U) b) =
      algebraMap B₁ Γ(Xk, i ⁻¹ᵁ U) b := by
    intro b
    change (((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appLE ⊤ U le_top) ≫ i.appLE U (i ⁻¹ᵁ U)
      le_rfl).hom b =
      ((CommRingCat.ofHom (residue B₁) ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B₁))).inv) ≫
        fk.appLE ⊤ (i ⁻¹ᵁ U) le_top).hom b
    congr 2
    erw [Category.assoc,
      Scheme.Hom.appLE_comp_appLE i f ⊤ U (i ⁻¹ᵁ U) le_top le_rfl,
      Scheme.ΓSpecIso_inv_naturality, Category.assoc, ← htop,
      Scheme.Hom.appLE_comp_appLE fk (Spec.map (CommRingCat.ofHom (residue B₁)))
        ⊤ ⊤ (i ⁻¹ᵁ U) le_top le_top]
    congr 1
    have key : ∀ {g₁ g₂ : Xk ⟶ Spec (CommRingCat.of B₁)} (h : g₁ = g₂)
        (p₁ : i ⁻¹ᵁ U ≤ g₁ ⁻¹ᵁ ⊤) (p₂ : i ⁻¹ᵁ U ≤ g₂ ⁻¹ᵁ ⊤), g₁.appLE ⊤ (i ⁻¹ᵁ U) p₁ = g₂.appLE ⊤
          (i ⁻¹ᵁ U) p₂ := by
      rintro g₁ _ rfl p₁ p₂; rfl
    exact key hi.w _ _
  have : IsScalarTower B₁ Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun b => (hsq
    b).symm)
  have hi' : IsPullback i fk f (Spec.map (CommRingCat.ofHom (algebraMap B₁ (ResidueField B₁)))) :=
    by
    rw [ResidueField.algebraMap_eq]; exact hi
  have hP : Algebra.IsPushout B₁ (ResidueField B₁) Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) :=
    (Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback f fk i hi' U hU).2
  have hsum' : (∑ j, algebraMap B₁ (X.presheaf.obj (Opposite.op U)) (ι (v j)) * s j) = δ := hsum
  have hread' : ∀ ξ : Module.Dual (ResidueField B₁) V,
      (∑ j, algebraMap (ResidueField B₁) (Xk.presheaf.obj (Opposite.op (i ⁻¹ᵁ U))) (ξ (v j)) *
        (i.app U).hom (s j)) = 0 := by
    intro ξ
    have h := hread ξ
    rw [LinearMap.zero_apply] at h
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h.symm
    rw [OModulePresheaf.res_refl_apply]
    rfl
  have h1 : ∀ ξ : Module.Dual (ResidueField B₁) V,
      (∑ j, ξ (v j) ⊗ₜ[B₁] s j : ResidueField B₁ ⊗[B₁] (X.presheaf.obj (Opposite.op U))) = 0 := by
    intro ξ
    apply (Algebra.IsPushout.equiv B₁ (ResidueField B₁) (X.presheaf.obj (Opposite.op U))
      (Xk.presheaf.obj (Opposite.op (i ⁻¹ᵁ U)))).injective
    rw [map_zero, map_sum, ← hread' ξ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.IsPushout.equiv_tmul, Scheme.Hom.app_eq_appLE]
    rfl
  have h2 : ∀ (e : V) (ξ : Module.Dual (ResidueField B₁) V),
      (∑ j, algebraMap B₁ (X.presheaf.obj (Opposite.op U)) (ι (ξ (v j) • e)) * s j) = 0 := by
    intro e ξ
    let Λ : ResidueField B₁ ⊗[B₁] (X.presheaf.obj (Opposite.op U)) →ₗ[B₁] (X.presheaf.obj
      (Opposite.op U)) :=
      TensorProduct.lift (LinearMap.mk₂ B₁ (fun (c : ResidueField B₁) (a : (X.presheaf.obj
        (Opposite.op U))) => algebraMap B₁ (X.presheaf.obj (Opposite.op U)) (ι (c • e)) * a)
        (fun c c' a => by simp only [add_smul, map_add, add_mul])
        (fun b c a => by
          rw [smul_assoc, map_smul, smul_eq_mul, map_mul, Algebra.smul_def, mul_assoc])
        (fun c a a' => by simp only [mul_add])
        (fun b c a => by rw [Algebra.smul_def, Algebra.smul_def, mul_left_comm]))
    have hΛ : ∀ c a, Λ (c ⊗ₜ a) = algebraMap B₁ (X.presheaf.obj (Opposite.op U)) (ι (c • e)) * a :=
      fun c a => TensorProduct.lift.tmul _ _
    have h := congrArg Λ (h1 ξ)
    rw [map_sum, map_zero] at h
    simpa only [hΛ] using h
  let bV := Module.finBasis (ResidueField B₁) V
  have h3 : ∀ j, ι (v j) = ∑ l, ι (bV.dualBasis l (v j) • bV l) := fun j => by
    rw [← map_sum]
    congr 1
    simp only [bV.dualBasis_apply]
    exact (bV.sum_repr (v j)).symm
  calc δ = ∑ j, algebraMap B₁ (X.presheaf.obj (Opposite.op U)) (ι (v j)) * s j := hsum'.symm
    _ = ∑ j, ∑ l, algebraMap B₁ (X.presheaf.obj (Opposite.op U)) (ι (bV.dualBasis l (v j) • bV l))
      * s j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [h3, map_sum, Finset.sum_mul]
    _ = ∑ l, ∑ j, algebraMap B₁ (X.presheaf.obj (Opposite.op U)) (ι (bV.dualBasis l (v j) • bV l))
      * s j := Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun l _ => h2 (bV l) (bV.dualBasis l)

end SmallExtension_IsFibreReading_eq_zero_of_isFibreReading_zero_of_flat
end AlgebraicCurves.Geometry.Deformation.Proofs
end ProofImplementation

attribute [-instance] PresheafOfModules.ExteriorPower.instModulePresheafAb
attribute [-simp] AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj
  PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply
  AlgebraicGeometry.Scheme.Modules.exteriorPower_obj
