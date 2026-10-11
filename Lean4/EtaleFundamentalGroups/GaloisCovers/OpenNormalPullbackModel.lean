/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.OpenNormalExtendedQuotientKernel
import EtaleFundamentalGroups.GaloisCovers.PullbackComponentNaturality

/-!
# Geometric models of open-normal pullbacks

Every open normal subgroup of the target fundamental group determines an
actual pointed finite-etale Galois cover and an actual pointed Galois
component of its pullback.  This file packages those choices uniformly, so
the local finite-cover extension argument can be passed directly to the
open-normal prosolvable criterion.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.PreGaloisCategory
open ProCGroups.FiniteStepSolvableQuotients

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]

/-- An actual geometric realization of the restriction of a fundamental
group map over one open normal subgroup of its target. -/
structure OpenNormalPullbackModel
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (U : OpenNormalSubgroup π₁ᵉᵗ(xi ≫ f)) where
  /-- The finite etale Galois cover of the target realizing the subgroup. -/
  targetCover : FiniteEtale Y
  /-- The chosen geometric point in the fiber of the target cover. -/
  targetPoint : (fiber (xi ≫ f)).obj targetCover
  /-- The Galois component of the pulled-back target cover. -/
  sourceCover : FiniteEtale X
  /-- The inclusion of the source component into the pullback cover. -/
  inclusion : sourceCover ⟶ (pullback f).obj targetCover
  /-- The chosen geometric point in the fiber of the source component. -/
  sourcePoint : (fiber xi).obj sourceCover
  /-- The target cover is a Galois object. -/
  targetIsGalois : IsGalois targetCover
  /-- The source component is a Galois object. -/
  sourceIsGalois : IsGalois sourceCover
  /-- The component inclusion is a monomorphism. -/
  inclusionMono : Mono inclusion
  /-- The source fundamental group identifies with the inverse-image subgroup. -/
  sourceEquiv :
    π₁ᵉᵗ((fiberObjEquivHom xi sourceCover sourcePoint).left) ≃ₜ*
      ProCGroups.OpenNormalSubgroup.comap
        (fundamentalGroupHom f xi).toMonoidHom
        (fundamentalGroupHom f xi).continuous_toFun U
  /-- The target-cover fundamental group identifies with the target subgroup. -/
  targetEquiv :
    π₁ᵉᵗ((fiberObjEquivHom xi sourceCover sourcePoint).left ≫
      (inclusion.left ≫ Limits.pullback.fst targetCover.hom f)) ≃ₜ* U
  /-- The fundamental group map agrees with restriction under these identifications. -/
  commutes : ∀ a,
    targetEquiv
        (fundamentalGroupHom
          (inclusion.left ≫ Limits.pullback.fst targetCover.hom f)
          (fiberObjEquivHom xi sourceCover sourcePoint).left a) =
      ProCGroups.ContinuousMonoidHom.restrictPreimage
        (fundamentalGroupHom f xi) (U : Subgroup π₁ᵉᵗ(xi ≫ f))
        (sourceEquiv a)

/-- The geometric pullback-component construction supplies a model for every
open normal subgroup. -/
theorem nonempty_openNormalPullbackModel
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (U : OpenNormalSubgroup π₁ᵉᵗ(xi ≫ f)) :
    Nonempty (OpenNormalPullbackModel f xi U) := by
  obtain ⟨A, x, Z, i, z, hA, hZ, hi, hsq⟩ :=
    exists_openNormal_galoisPullbackComponent_fundamentalGroup_square f xi U
  dsimp only at hsq
  obtain ⟨eSource, eTarget, hcomm⟩ := hsq
  exact ⟨
    { targetCover := A
      targetPoint := x
      sourceCover := Z
      inclusion := i
      sourcePoint := z
      targetIsGalois := hA
      sourceIsGalois := hZ
      inclusionMono := hi
      sourceEquiv := eSource
      targetEquiv := eTarget
      commutes := hcomm }⟩

/-- A fixed actual model for an open normal subgroup. -/
noncomputable def openNormalPullbackModel
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (U : OpenNormalSubgroup π₁ᵉᵗ(xi ≫ f)) :
    OpenNormalPullbackModel f xi U :=
  Classical.choice (nonempty_openNormalPullbackModel f xi U)

namespace OpenNormalPullbackModel

variable {f : X ⟶ Y} {xi : Spec (.of Omega) ⟶ X}
variable {U : OpenNormalSubgroup π₁ᵉᵗ(xi ≫ f)}

/-- The source scheme in the selected geometric model. -/
abbrev sourceScheme (M : OpenNormalPullbackModel f xi U) : Scheme.{u} :=
  M.sourceCover.left

/-- The target scheme in the selected geometric model. -/
abbrev targetScheme (M : OpenNormalPullbackModel f xi U) : Scheme.{u} :=
  M.targetCover.left

/-- The actual morphism from the pullback component to the target cover. -/
abbrev hom (M : OpenNormalPullbackModel f xi U) :
    M.sourceScheme ⟶ M.targetScheme :=
  M.inclusion.left ≫ Limits.pullback.fst M.targetCover.hom f

/-- The geometric point on the source component. -/
abbrev geometricPoint (M : OpenNormalPullbackModel f xi U) :
    Spec (.of Omega) ⟶ M.sourceScheme :=
  (fiberObjEquivHom xi M.sourceCover M.sourcePoint).left

noncomputable instance sourceConnectedSpace
    (M : OpenNormalPullbackModel f xi U) : ConnectedSpace M.sourceScheme := by
  let : IsGalois M.sourceCover := M.sourceIsGalois
  exact FiniteEtale.connectedSpace_left_of_isConnected M.sourceCover

noncomputable instance targetConnectedSpace
    (M : OpenNormalPullbackModel f xi U) : ConnectedSpace M.targetScheme := by
  let : IsGalois M.targetCover := M.targetIsGalois
  exact FiniteEtale.connectedSpace_left_of_isConnected M.targetCover

end OpenNormalPullbackModel

/-- Specializing the general open-normal kernel bridge to the uniformly
selected actual pullback components leaves only the geometric cover-extension
input.  No fundamental-group square is assumed. -/
theorem
    fundamentalGroupHom_openNormalFiniteDiscreteAbelianMapsKillKernel_of_pullbackModel_extensions
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (extend : ∀ (U : OpenNormalSubgroup π₁ᵉᵗ(xi ≫ f))
      (W : FiniteEtale (openNormalPullbackModel f xi U).sourceScheme)
      (_hW : IsGalois W),
      IsMulCommutative (Aut W) →
        Σ Z : FiniteEtale (openNormalPullbackModel f xi U).targetScheme,
          (pullback (openNormalPullbackModel f xi U).hom).obj Z ≅ W) :
    OpenNormalFiniteDiscreteAbelianMapsKillKernel
      (fundamentalGroupHom f xi) := by
  exact
    fundamentalGroupHom_openNormalFiniteDiscreteAbelianMapsKillKernel_of_local_extensions
      f xi
      (fun U ↦ (openNormalPullbackModel f xi U).sourceScheme)
      (fun U ↦ (openNormalPullbackModel f xi U).targetScheme)
      (fun U ↦ (openNormalPullbackModel f xi U).hom)
      (fun U ↦ (openNormalPullbackModel f xi U).geometricPoint)
      (fun U ↦ (openNormalPullbackModel f xi U).sourceEquiv)
      (fun U ↦ (openNormalPullbackModel f xi U).targetEquiv)
      (fun U ↦ (openNormalPullbackModel f xi U).commutes)
      extend

end AlgebraicGeometry.FiniteEtale
