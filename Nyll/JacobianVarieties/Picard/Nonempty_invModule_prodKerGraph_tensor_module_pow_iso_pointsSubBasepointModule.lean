/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.JacobianVarieties.Picard.AbelJacobiFamily
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Mathlib.Util.WithWeakNamespace

/-!
# Relative Picard varieties and fibre cohomology

Identify the tensor product of graph-ideal inverse modules and basepoint factors with the point-
difference line bundle.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs
namespace Nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace TensorList
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

open _root_.AlgebraicGeometry.RelPicard.Scheme
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
  [IsSeparated a] [SmoothOfRelativeDimension 1 a]

/-- Interchange the middle factors in a tensor product of four sheaf modules. -/
noncomputable def shuffle {X : Scheme.{u}} (X₁ X₂ Y₁ Y₂ : X.Modules) :
    (X₁ ⊗ X₂) ⊗ (Y₁ ⊗ Y₂) ≅ (X₁ ⊗ Y₁) ⊗ (X₂ ⊗ Y₂) :=
  (α_ X₁ X₂ (Y₁ ⊗ Y₂)) ≪≫
    whiskerLeftIso X₁ ((α_ X₂ Y₁ Y₂).symm ≪≫ whiskerRightIso (β_ X₂ Y₁) Y₂ ≪≫ α_ Y₁ X₂ Y₂) ≪≫
    (α_ X₁ Y₁ (X₂ ⊗ Y₂)).symm

lemma isInvertible_ker (P : Spec (CommRingCat.of k) ⟶ A) (hP : P ≫ a = 𝟙 _) :
    (graphOver a P hP).ker.IsInvertible :=
by
  have hbase : MorphismProperty.IsStableUnderBaseChange
      (C := Scheme.{u}) (fun {_ _} f => SmoothOfRelativeDimension 1 f) :=
    smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  have : SmoothOfRelativeDimension 1 (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {_ _ : Scheme.{u}} f => SmoothOfRelativeDimension 1 f)
      (IsPullback.of_hasPullback a (𝟙 (Spec (CommRingCat.of k)))) inferInstance
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd a (𝟙 _)) (graphOver a P hP)
    (graphOver_snd a P hP)

lemma isInvertible_prodKerGraph {r : ℕ} (P : Fin r → (Spec (CommRingCat.of k) ⟶ A)) (hP : ∀ i,
  P i ≫ a = 𝟙 _) :
    (prodKerGraph a P hP).IsInvertible := by
  induction r with
  | zero => rw [prodKerGraph_zero]; exact IdealSheafData.isInvertible_top
  | succ r ih =>
    rw [prodKerGraph_eq_prod, Fin.prod_univ_succ]
    exact (isInvertible_ker (P 0) (hP 0)).mul (ih (fun i => P i.succ) (fun i => hP i.succ))

lemma isInvertible_pow {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) (n : ℕ) :
    (I ^ n).IsInvertible := by
  induction n with
  | zero => rw [pow_zero, Scheme.IdealSheafData.one_eq_top]; exact IdealSheafData.isInvertible_top
  | succ n ih => rw [pow_succ]; exact ih.mul hI

theorem main (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) {r : ℕ}
    (P : Fin r → (Spec (CommRingCat.of k) ⟶ A)) (hP : ∀ i, P i ≫ a = 𝟙 _) :
    Nonempty ((prodKerGraph a P hP).invModule ⊗ ((RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^
      r).module ≅
      pointsSubBasepointModule (a := a) ε
        (List.ofFn fun i => (⟨P i, hP i⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a))) := by
  induction r with
  | zero =>
    have h1 : prodKerGraph a P hP = ⊤ := prodKerGraph_zero a P hP
    have h2 : (RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ 0 = ⊤ := by rw [pow_zero,
      Scheme.IdealSheafData.one_eq_top]
    rw [List.ofFn_zero, pointsSubBasepointModule_nil, h1, h2]
    exact Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso
      IdealSheafData.isInvertible_top
  | succ r ih =>
    let I₀ := (graphOver a (P 0) (hP 0)).ker
    let J := prodKerGraph a (fun i => P i.succ) (fun i => hP i.succ)
    let Iε := (RelEffCartierDiv.ofPoint a ε.1 ε.2).I
    have hprod : prodKerGraph a P hP = I₀ * J := by
      simp only [I₀, J, prodKerGraph_eq_prod]
      rw [Fin.prod_univ_succ]
    have hpow : Iε ^ (r + 1) = Iε * Iε ^ r := pow_succ' Iε r
    have hI₀ : I₀.IsInvertible := isInvertible_ker (P 0) (hP 0)
    have hJ : J.IsInvertible := isInvertible_prodKerGraph _ _
    have hIε : Iε.IsInvertible := isInvertible_ker ε.1 ε.2
    have hIεr : (Iε ^ r).IsInvertible := isInvertible_pow hIε r
    obtain ⟨e₁⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor hI₀ hJ
    obtain ⟨e₂⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor hIε hIεr
    obtain ⟨e₃⟩ := ih (fun i => P i.succ) (fun i => hP i.succ)
    rw [List.ofFn_succ, pointsSubBasepointModule_cons]
    have c₁ : (prodKerGraph a P hP).invModule ≅ (I₀ * J).invModule := eqToIso (by rw [hprod])
    have c₂ : ((RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ (r + 1)).module ≅ (Iε * Iε ^ r).module :=
      eqToIso
        (by rw [show (RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ (r + 1) = Iε * Iε ^ r from hpow])
    exact ⟨(c₁ ⊗ᵢ c₂) ≪≫ (e₁ ⊗ᵢ e₂) ≪≫ shuffle _ _ _ _ ≪≫ whiskerLeftIso _ e₃⟩

end AlgebraicGeometry.RelPicard.TensorList

with_weak_namespace _root_.JacobianVarieties.Picard.Proofs
with_weak_namespace Nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule
with_weak_namespace AlgebraicGeometry
open RelPicard in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard
theorem nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) {r : ℕ}
    (P : Fin r → (Spec (CommRingCat.of k) ⟶ A)) (hP : ∀ i, P i ≫ a = 𝟙 _) :
    Nonempty ((prodKerGraph a P hP).invModule ⊗ ((RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^
      r).module ≅
      pointsSubBasepointModule (a := a) ε
        (List.ofFn fun i => (⟨P i, hP i⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a))) :=
  TensorList.main ε P hP
end Nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule
end JacobianVarieties.Picard.Proofs
end ProofImplementation
