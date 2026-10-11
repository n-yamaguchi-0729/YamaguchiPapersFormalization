/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.ConstantMorphism
import Nyll.EtaleCohomology.Constructible.LocallyConstant
import Nyll.EtaleCohomology.Sites.ConstantPullback
import Nyll.EtaleCohomology.Sites.PullbackStalks
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Kernels and cokernels of finite type locally constant sheaves

The finite local models of the actual sheaf morphism give the kernel and
cokernel models. Noetherian coefficients are needed for kernels; cokernels
are finite type over any commutative ring.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits
namespace EtaleCohomology
variable {X : Scheme.{u}} {R : Type u} [CommRing R]

private lemma constant_kernel [IsNoetherianRing R]
    (M N : ModuleCat.{u} R) [Module.Finite R M]
    (φ : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj N) :
    IsEtaleFiniteTypeLocallyConstant R (kernel φ) := by
  obtain ⟨𝒰, h𝒰⟩ := exists_constantMorphism_cover M N φ
  refine ⟨𝒰, fun i => ?_⟩
  obtain ⟨l, eM, eN, hl⟩ := h𝒰 i
  let C := constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u} R)
  have : PreservesFiniteLimits C := by
    change PreservesFiniteLimits
      (Functor.const (𝒰.X i).Etaleᵒᵖ ⋙ presheafToSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u} R))
    infer_instance
  have hk : Module.Finite R (kernel l : ModuleCat.{u} R) :=
    Module.Finite.of_injective (kernel.ι l).hom
      ((ModuleCat.mono_iff_injective (kernel.ι l)).mp inferInstance)
  exact ⟨kernel l, hk, ⟨PreservesKernel.iso (etalePullback (𝒰.f i) R) φ ≪≫
    kernel.mapIso _ (C.map l) eM eN hl ≪≫ (PreservesKernel.iso C l).symm⟩⟩

private lemma constant_cokernel
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (φ : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj N) :
    IsEtaleFiniteTypeLocallyConstant R (cokernel φ) := by
  obtain ⟨𝒰, h𝒰⟩ := exists_constantMorphism_cover M N φ
  refine ⟨𝒰, fun i => ?_⟩
  obtain ⟨l, eM, eN, hl⟩ := h𝒰 i
  let C := constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u} R)
  have : PreservesFiniteLimits C := by
    change PreservesFiniteLimits
      (Functor.const (𝒰.X i).Etaleᵒᵖ ⋙ presheafToSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u} R))
    infer_instance
  have : PreservesFiniteColimits C := by
    change PreservesFiniteColimits
      (Functor.const (𝒰.X i).Etaleᵒᵖ ⋙ presheafToSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u} R))
    infer_instance
  have hk : Module.Finite R (cokernel l : ModuleCat.{u} R) :=
    Module.Finite.of_surjective (cokernel.π l).hom
      ((ModuleCat.epi_iff_surjective (cokernel.π l)).mp inferInstance)
  exact ⟨cokernel l, hk, ⟨PreservesCokernel.iso (etalePullback (𝒰.f i) R) φ ≪≫
    cokernel.mapIso _ (C.map l) eM eN hl ≪≫ (PreservesCokernel.iso C l).symm⟩⟩

/-- Kernels of maps of finite type locally constant sheaves are finite type
locally constant over a noetherian coefficient ring. -/
theorem IsEtaleFiniteTypeLocallyConstant.kernel [IsNoetherianRing R]
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (φ : G ⟶ H)
    (hG : IsEtaleFiniteTypeLocallyConstant R G)
    (hH : IsEtaleFiniteTypeLocallyConstant R H) :
    IsEtaleFiniteTypeLocallyConstant R (kernel φ) := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  apply IsEtaleLocallyConstantWith.of_cover 𝒰
  intro a
  obtain ⟨M, hM, ⟨eM⟩⟩ := h𝒰 a
  obtain ⟨𝒱, h𝒱⟩ := hH.pullback (𝒰.f a)
  apply IsEtaleLocallyConstantWith.of_cover 𝒱
  intro b
  obtain ⟨N, hN, ⟨eN⟩⟩ := h𝒱 b
  have : Module.Finite R M := hM
  let P := etalePullback (𝒱.f b) R
  let eG := P.mapIso eM ≪≫ (etalePullbackConstantIso (𝒱.f b) R).app M
  let φ' := P.map ((etalePullback (𝒰.f a) R).map φ)
  let l := eG.inv ≫ φ' ≫ eN.hom
  have hl : φ' ≫ eN.hom = eG.hom ≫ l := by
    dsimp only [l]
    rw [Iso.hom_inv_id_assoc]
  exact (constant_kernel M N l).of_iso
    (P.mapIso (PreservesKernel.iso (etalePullback (𝒰.f a) R) φ) ≪≫
      PreservesKernel.iso P ((etalePullback (𝒰.f a) R).map φ) ≪≫
      kernel.mapIso φ' l eG eN hl).symm

/-- Cokernels preserve finite type local constancy over any coefficient ring. -/
theorem IsEtaleFiniteTypeLocallyConstant.cokernel
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (φ : G ⟶ H)
    (hG : IsEtaleFiniteTypeLocallyConstant R G)
    (hH : IsEtaleFiniteTypeLocallyConstant R H) :
    IsEtaleFiniteTypeLocallyConstant R (cokernel φ) := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  apply IsEtaleLocallyConstantWith.of_cover 𝒰
  intro a
  obtain ⟨M, hM, ⟨eM⟩⟩ := h𝒰 a
  obtain ⟨𝒱, h𝒱⟩ := hH.pullback (𝒰.f a)
  apply IsEtaleLocallyConstantWith.of_cover 𝒱
  intro b
  obtain ⟨N, hN, ⟨eN⟩⟩ := h𝒱 b
  have : Module.Finite R M := hM
  have : Module.Finite R N := hN
  let P := etalePullback (𝒱.f b) R
  let eG := P.mapIso eM ≪≫ (etalePullbackConstantIso (𝒱.f b) R).app M
  let φ' := P.map ((etalePullback (𝒰.f a) R).map φ)
  let l := eG.inv ≫ φ' ≫ eN.hom
  have hl : φ' ≫ eN.hom = eG.hom ≫ l := by
    dsimp only [l]
    rw [Iso.hom_inv_id_assoc]
  exact (constant_cokernel M N l).of_iso
    (P.mapIso (PreservesCokernel.iso (etalePullback (𝒰.f a) R) φ) ≪≫
      PreservesCokernel.iso P ((etalePullback (𝒰.f a) R).map φ) ≪≫
      cokernel.mapIso φ' l eG eN hl).symm

end EtaleCohomology
