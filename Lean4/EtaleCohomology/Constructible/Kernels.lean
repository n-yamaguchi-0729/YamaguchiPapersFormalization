/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.Basic
import EtaleCohomology.Constructible.LocallyConstantKernels
import EtaleCohomology.Sites.PullbackStalks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Kernels and cokernels of constructible sheaves

A common finite adapted stratification reduces both operations to their
finite type locally constant counterparts. The argument applies on every
affine open without any noetherian hypothesis on the scheme.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits
namespace EtaleCohomology
variable {X : Scheme.{u}} {R : Type u} [CommRing R]

/-- A common adapted stratification remains adapted to the kernel. -/
lemma ConstructibleStratification.IsAdaptedTo.kernel [IsNoetherianRing R]
    {S : ConstructibleStratification X}
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (φ : G ⟶ H)
    (hG : S.IsAdaptedTo R G) (hH : S.IsAdaptedTo R H) :
    S.IsAdaptedTo R (kernel φ) := by
  intro i
  exact (IsEtaleFiniteTypeLocallyConstant.kernel
    ((etalePullback (S.map i) R).map φ) (hG i) (hH i)).of_iso
    (PreservesKernel.iso (etalePullback (S.map i) R) φ).symm

/-- A common adapted stratification remains adapted to the cokernel. -/
lemma ConstructibleStratification.IsAdaptedTo.cokernel
    {S : ConstructibleStratification X}
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (φ : G ⟶ H)
    (hG : S.IsAdaptedTo R G) (hH : S.IsAdaptedTo R H) :
    S.IsAdaptedTo R (cokernel φ) := by
  intro i
  exact (IsEtaleFiniteTypeLocallyConstant.cokernel
    ((etalePullback (S.map i) R).map φ) (hG i) (hH i)).of_iso
    (PreservesCokernel.iso (etalePullback (S.map i) R) φ).symm

/-- Finite stratifiability is preserved by kernels over noetherian coefficients. -/
lemma HasFiniteConstructibleStratification.kernel [IsNoetherianRing R]
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (φ : G ⟶ H)
    (hG : HasFiniteConstructibleStratification R G)
    (hH : HasFiniteConstructibleStratification R H) :
    HasFiniteConstructibleStratification R (kernel φ) := by
  obtain ⟨S, hS, hT⟩ := hG.exists_common hH
  exact ⟨S, hS.kernel φ hT⟩

/-- Finite stratifiability is preserved by cokernels. -/
lemma HasFiniteConstructibleStratification.cokernel
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (φ : G ⟶ H)
    (hG : HasFiniteConstructibleStratification R G)
    (hH : HasFiniteConstructibleStratification R H) :
    HasFiniteConstructibleStratification R (cokernel φ) := by
  obtain ⟨S, hS, hT⟩ := hG.exists_common hH
  exact ⟨S, hS.cokernel φ hT⟩

/-- Constructible module sheaves over a noetherian ring are closed under kernels. -/
theorem IsEtaleConstructible.kernel [IsNoetherianRing R]
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (φ : G ⟶ H)
    (hG : IsEtaleConstructible R G) (hH : IsEtaleConstructible R H) :
    IsEtaleConstructible R (kernel φ) := by
  intro U
  exact (HasFiniteConstructibleStratification.kernel
    ((etalePullback U.1.ι R).map φ) (hG U) (hH U)).of_iso
    (PreservesKernel.iso (etalePullback U.1.ι R) φ).symm

/-- Constructible module sheaves are closed under cokernels. -/
theorem IsEtaleConstructible.cokernel
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (φ : G ⟶ H)
    (hG : IsEtaleConstructible R G) (hH : IsEtaleConstructible R H) :
    IsEtaleConstructible R (cokernel φ) := by
  intro U
  exact (HasFiniteConstructibleStratification.cokernel
    ((etalePullback U.1.ι R).map φ) (hG U) (hH U)).of_iso
    (PreservesCokernel.iso (etalePullback U.1.ι R) φ).symm

end EtaleCohomology
