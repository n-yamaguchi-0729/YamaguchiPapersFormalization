/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isImmersion_proj.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem

/-!
# exists is Affine Open forall mem of is Immersion proj
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.exists_isAffineOpen_forall_mem_of_isImmersion_proj

universe u v

open CategoryTheory

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry

section ProjOpen

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace Proj
open _root_.AlgebraicGeometry.Proj
end Proj
open scoped Proj in
theorem Proj.exists_basicOpen_le_forall_mem_of_finset (U : (Proj 𝒜).Opens) (S : Finset (Proj 𝒜))
    (hS : ∀ x ∈ S, x ∈ U) :
    ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧ Proj.basicOpen 𝒜 f ≤ U ∧ ∀ x ∈ S, x ∈ Proj.basicOpen 𝒜 f
      := by
  classical
  set Z : Set (Proj 𝒜) := (U : Set (Proj 𝒜))ᶜ with hZdef
  have hZ : IsClosed Z := U.isOpen.isClosed_compl
  set J : HomogeneousIdeal 𝒜 := ProjectiveSpectrum.vanishingIdeal Z with hJdef
  have hZJ : ProjectiveSpectrum.zeroLocus 𝒜 (J : Set A) = Z := by
    exact (ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure 𝒜
      (Z : Set (ProjectiveSpectrum 𝒜))).trans hZ.closure_eq
  have havoid : ∀ p ∈ S.image (fun x : Proj 𝒜 => x.asHomogeneousIdeal),
      ¬ (J ⊓ HomogeneousIdeal.irrelevant 𝒜 ≤ p) := by
    intro p hp hle
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hp
    change (J ⊓ HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ x.asHomogeneousIdeal.toIdeal at hle
    rw [HomogeneousIdeal.toIdeal_inf, x.isPrime.inf_le] at hle
    rcases hle with hle | hle
    · have hxZ : x ∈ Z := by
        rw [← hZJ]
        exact (ProjectiveSpectrum.mem_zeroLocus 𝒜 x _).mpr hle
      exact hxZ (hS x hxS)
    · exact x.not_irrelevant_le hle
  obtain ⟨n, f, hn, hfn, hfI, hf⟩ :=
    (J ⊓ HomogeneousIdeal.irrelevant 𝒜).exists_homogeneous_pos_mem_forall_notMem inf_le_right
      (S.image fun x : Proj 𝒜 => x.asHomogeneousIdeal)
      (fun p hp => by
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hp
        exact x.isPrime)
      havoid
  refine ⟨n, f, hn, hfn, ?_, ?_⟩
  · intro y hy
    by_contra hyU
    have hyZ : y ∈ Z := hyU
    rw [← hZJ] at hyZ
    have hfJ : f ∈ J := (inf_le_left : J ⊓ HomogeneousIdeal.irrelevant 𝒜 ≤ J) hfI
    exact (Proj.mem_basicOpen 𝒜 f y).mp hy ((ProjectiveSpectrum.mem_zeroLocus 𝒜 y _).mp hyZ hfJ)
  · intro x hx
    rw [Proj.mem_basicOpen]
    exact hf _ (Finset.mem_image_of_mem _ hx)

open scoped Proj in
theorem Proj.exists_isAffineOpen_le_forall_mem_of_finset (U : (Proj 𝒜).Opens) (S : Finset (Proj 𝒜))
    (hS : ∀ x ∈ S, x ∈ U) :
    ∃ V : (Proj 𝒜).Opens, IsAffineOpen V ∧ V ≤ U ∧ ∀ x ∈ S, x ∈ V := by
  obtain ⟨n, f, hn, hfn, hle, hmem⟩ := Proj.exists_basicOpen_le_forall_mem_of_finset 𝒜 U S hS
  exact ⟨_, Proj.isAffineOpen_basicOpen 𝒜 f hfn hn, hle, hmem⟩

end ProjOpen

namespace IsAffineOpen
open _root_.AlgebraicGeometry.IsAffineOpen
end IsAffineOpen
namespace IsAffineOpen
private theorem _root_.AlgebraicGeometry.IsAffineOpen.ι_preimage_of_le {Y : Scheme.{u}} {U V :
  Y.Opens} (hV : IsAffineOpen V) (h : V ≤ U) :
    IsAffineOpen (U.ι ⁻¹ᵁ V) := by
  have himg : IsAffineOpen (U.ι ''ᵁ (U.ι ⁻¹ᵁ V)) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr h]
    exact hV
  have : IsAffine (U.ι ''ᵁ U.ι ⁻¹ᵁ V) := himg
  exact IsAffine.of_isIso (U.ι.isoImage (U.ι ⁻¹ᵁ V)).hom

end IsAffineOpen
open _root_.AlgebraicGeometry

theorem exists_isAffineOpen_forall_mem_of_isImmersion {X Y : Scheme.{u}} (ι : X ⟶ Y) [IsImmersion ι]
    (hY : ∀ (U : Y.Opens) (T : Finset Y), (∀ y ∈ T, y ∈ U) →
      ∃ V : Y.Opens, IsAffineOpen V ∧ V ≤ U ∧ ∀ y ∈ T, y ∈ V)
    (S : Finset X) : ∃ W : X.Opens, IsAffineOpen W ∧ ∀ x ∈ S, x ∈ W := by
  classical
  set U := ι.coborderRange
  set g := ι.liftCoborder
  have hg : g ≫ U.ι = ι := ι.liftCoborder_ι
  obtain ⟨V, hV, hVU, hmem⟩ := hY U (S.image ι.base) (by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    rw [← hg]
    exact (g.base x).2)
  refine ⟨g ⁻¹ᵁ (U.ι ⁻¹ᵁ V), (hV.ι_preimage_of_le hVU).preimage g, fun x hx => ?_⟩
  change x ∈ (g ≫ U.ι) ⁻¹ᵁ V
  rw [hg]
  exact hmem _ (Finset.mem_image_of_mem _ hx)

end AlgebraicGeometry

theorem _root_.AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isImmersion_proj
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
      [GradedRing 𝒜]
    {X : AlgebraicGeometry.Scheme.{u}} (ι : X ⟶ AlgebraicGeometry.Proj 𝒜)
      [AlgebraicGeometry.IsImmersion ι]
    (S : Finset X) :
    ∃ W : X.Opens, AlgebraicGeometry.IsAffineOpen W ∧ ∀ x ∈ S, x ∈ W :=
  AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isImmersion ι
    (fun U T hT => AlgebraicGeometry.Proj.exists_isAffineOpen_le_forall_mem_of_finset 𝒜 U T hT) S
end AlgebraicCurves.Geometry.Schemes.Proofs.exists_isAffineOpen_forall_mem_of_isImmersion_proj
end ProofImplementation
