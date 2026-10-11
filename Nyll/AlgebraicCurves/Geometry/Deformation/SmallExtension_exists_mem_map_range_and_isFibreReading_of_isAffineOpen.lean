/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmallExtension_exists_mem_map_range_and_isFibreReading_of_isAffineOpen.lean
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
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic.Choose
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OrderedAffineCoverCochainPullback
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.CechObstruction
import Nyll.AlgebraicCurves.Geometry.Sheaves.KaehlerModule
import Nyll.SchemeTheory.Affine.PullbackSectionsPushout

/-!
# Small Extension exists mem map range and is Fibre Reading of is Affine Open
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Deformation.Proofs
namespace SmallExtension_exists_mem_map_range_and_isFibreReading_of_isAffineOpen


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.IsLocalRing
open _root_.AlgebraicGeometry.SmallExtension
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover


universe u
open TensorProduct

theorem
  _root_.AlgebraicGeometry.SmallExtension.exists_mem_map_range_and_isFibreReading_of_isAffineOpen
    {B₁ : Type u} [CommRing B₁] [IsLocalRing B₁]
    (V : Type u) [AddCommGroup V] [Module (ResidueField B₁) V] [Module.Finite (ResidueField B₁) V]
    [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V] (ι : V →ₗ[B₁] B₁)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of (ResidueField B₁))) (i : Xk ⟶ X)
    (hi : IsPullback i fk f (Spec.map (CommRingCat.ofHom (residue B₁))))
    (U : X.Opens) (hU : IsAffineOpen U) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) (hW' : i ⁻¹ᵁ U ≤ W)
    (w : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).obj W) :
    ∃ δ : Γ(X, U), (letI := algebraOfHom f U
      δ ∈ Ideal.map (algebraMap B₁ Γ(X, U)) (LinearMap.range ι)) ∧ IsFibreReading V ι f fk i U W hW
        δ w := by
  classical
  obtain rfl : W = i ⁻¹ᵁ U := le_antisymm hW hW'
  have hsurj : Function.Surjective (i.app U).hom := by
    have hi' : IsPullback i fk f (Spec.map (CommRingCat.ofHom (algebraMap B₁ (ResidueField B₁))))
      := by
      rw [ResidueField.algebraMap_eq]; exact hi
    obtain ⟨-, hpo⟩ := Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback f fk i hi' U hU
    let iA := f.sectionsAlgebra U
    let iAk := fk.sectionsAlgebra (i ⁻¹ᵁ U)
    let iT : Algebra Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) := (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    let iB : Algebra B₁ Γ(Xk, i ⁻¹ᵁ U) :=
      ((algebraMap (ResidueField B₁) Γ(Xk, i ⁻¹ᵁ U)).comp (algebraMap B₁ (ResidueField
        B₁))).toAlgebra
    have : IsScalarTower B₁ (ResidueField B₁) Γ(Xk, i ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun
      _ => rfl)
    have htop : (Spec.map (CommRingCat.ofHom (residue B₁))).appLE ⊤ ⊤ le_top =
        (Spec.map (CommRingCat.ofHom (residue B₁))).appTop := Scheme.Hom.appLE_eq_app _
    have hsq : ∀ b : B₁, algebraMap Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) (algebraMap B₁ Γ(X, U) b) = algebraMap
      B₁ Γ(Xk, i ⁻¹ᵁ U) b := by
      intro b
      change (((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appLE ⊤ U le_top) ≫ i.appLE U (i ⁻¹ᵁ
        U) le_rfl).hom b =
        ((CommRingCat.ofHom (residue B₁) ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField
          B₁))).inv) ≫
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
    have hP : Algebra.IsPushout B₁ (ResidueField B₁) Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) := hpo
    have key : ∀ z : ResidueField B₁ ⊗[B₁] Γ(X, U), ∃ s : Γ(X, U),
        algebraMap Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) s = Algebra.IsPushout.equiv B₁ (ResidueField B₁) Γ(X, U)
          Γ(Xk, i ⁻¹ᵁ U) z := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a s =>
        obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
        refine ⟨algebraMap B₁ Γ(X, U) b * s, ?_⟩
        rw [Algebra.IsPushout.equiv_tmul, map_mul, hsq]
        rfl
      | add x y hx hy =>
        obtain ⟨s, hs⟩ := hx; obtain ⟨s', hs'⟩ := hy
        exact ⟨s + s', by rw [map_add, hs, hs', map_add]⟩
    intro y
    obtain ⟨s, hs⟩ := key ((Algebra.IsPushout.equiv B₁ (ResidueField B₁) Γ(X, U) Γ(Xk, i ⁻¹ᵁ
      U)).symm y)
    rw [AlgEquiv.apply_symm_apply] at hs
    refine ⟨s, ?_⟩
    rw [Scheme.Hom.app_eq_appLE]
    exact hs
  let := algebraOfHom f U
  let bV := Module.finBasis (ResidueField B₁) V
  choose s hs using fun l : Fin (Module.finrank (ResidueField B₁) V) => hsurj (w (bV.dualBasis l))
  refine ⟨∑ l, algebraMap B₁ (X.presheaf.obj (Opposite.op U)) (ι (bV l)) * s l, ?_, ?_⟩
  · exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _
      (LinearMap.mem_range.mpr ⟨bV l, rfl⟩))
  · refine ⟨_, bV, s, rfl, fun ξ => ?_⟩
    conv_lhs => rw [← bV.dualBasis.sum_repr ξ]
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, bV.dualBasis_repr ξ l, hs l, OModulePresheaf.res_refl_apply]
end SmallExtension_exists_mem_map_range_and_isFibreReading_of_isAffineOpen
end AlgebraicCurves.Geometry.Deformation.Proofs
end ProofImplementation

attribute [-instance] PresheafOfModules.ExteriorPower.instModulePresheafAb
attribute [-simp] AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj
  PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply
  AlgebraicGeometry.Scheme.Modules.exteriorPower_obj
