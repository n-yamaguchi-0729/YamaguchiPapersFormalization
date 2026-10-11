/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.LocallyConstant
import EtaleCohomology.Sites.ConstantPullback
import EtaleCohomology.Sites.PullbackStalks
import EtaleCohomology.Sites.SheafFunctors
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Products of locally constant module sheaves

Refining the two trivializing étale covers gives constant models for a binary
product. Both inverse image and the constant-sheaf functor preserve binary
products, and a product of finitely generated modules is finitely generated.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

/-- Binary products preserve finite type local constancy over any coefficient ring. -/
theorem IsEtaleFiniteTypeLocallyConstant.prod
    {X : Scheme.{u}} {R : Type u} [CommRing R]
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : IsEtaleFiniteTypeLocallyConstant R G)
    (hH : IsEtaleFiniteTypeLocallyConstant R H) :
    IsEtaleFiniteTypeLocallyConstant R (G ⨯ H) := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  apply IsEtaleLocallyConstantWith.of_cover 𝒰
  intro a
  obtain ⟨M, hM, ⟨eM⟩⟩ := h𝒰 a
  obtain ⟨𝒱, h𝒱⟩ := hH.pullback (𝒰.f a)
  refine ⟨𝒱, fun b => ?_⟩
  obtain ⟨N, hN, ⟨eN⟩⟩ := h𝒱 b
  have : Module.Finite R M := hM
  have : Module.Finite R N := hN
  let em : M ⨯ N ≅ ModuleCat.of R (M × N) :=
    limit.isoLimitCone (ModuleCat.binaryProductLimitCone M N)
  have hMN : Module.Finite R (M ⨯ N : ModuleCat.{u} R) :=
    Module.Finite.equiv em.toLinearEquiv.symm
  let C : ModuleCat.{u} R ⥤ Sheaf (𝒱.X b).smallEtaleTopology (ModuleCat.{u} R) :=
    constantSheaf (𝒱.X b).smallEtaleTopology (ModuleCat.{u} R)
  have : PreservesFiniteLimits C := by
    change PreservesFiniteLimits
      (Functor.const (𝒱.X b).Etaleᵒᵖ ⋙ presheafToSheaf (𝒱.X b).smallEtaleTopology (ModuleCat.{u} R))
    infer_instance
  let eG : (etalePullback (𝒱.f b) R).obj ((etalePullback (𝒰.f a) R).obj G) ≅
      C.obj M :=
    (etalePullback (𝒱.f b) R).mapIso eM ≪≫ (etalePullbackConstantIso (𝒱.f b) R).app M
  exact ⟨M ⨯ N, hMN,
    ⟨(etalePullback (𝒱.f b) R).mapIso
        (PreservesLimitPair.iso (etalePullback (𝒰.f a) R) G H) ≪≫
      PreservesLimitPair.iso (etalePullback (𝒱.f b) R)
        ((etalePullback (𝒰.f a) R).obj G) ((etalePullback (𝒰.f a) R).obj H) ≪≫
      prod.mapIso eG eN ≪≫ (PreservesLimitPair.iso C M N).symm⟩⟩

/-- In particular, the square used to express addition is finite type locally constant. -/
theorem IsEtaleFiniteTypeLocallyConstant.selfProd
    {X : Scheme.{u}} {R : Type u} [CommRing R]
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : IsEtaleFiniteTypeLocallyConstant R G) :
    IsEtaleFiniteTypeLocallyConstant R (G ⨯ G) := hG.prod hG

end EtaleCohomology
