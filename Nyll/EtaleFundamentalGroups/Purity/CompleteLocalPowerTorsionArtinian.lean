/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Purity.ArtinianSocleFiniteLength
public import Nyll.EtaleFundamentalGroups.Purity.CompleteLocalResidueFieldHullArtinian
public import Nyll.EtaleFundamentalGroups.Purity.EssentialModuleExtension
public import Nyll.EtaleFundamentalGroups.Purity.FiniteLengthInjectiveEmbedding
public import Nyll.EtaleFundamentalGroups.Purity.MaximalIdealPowerTorsionSocle
public import Nyll.EtaleFundamentalGroups.Purity.ModuleInjectiveHull
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

/-!
# Artinianness from the socle over a complete local ring

Constructing an Artinian injective hull of the residue field shows that
any module with a finite-length essential submodule is Artinian.  In a
maximal-ideal-power torsion module the socle is essential, so it suffices
that the socle be Artinian.  In particular an Artinian scalar kernel for
a member of the maximal ideal suffices.
-/

@[expose] public section

namespace EtaleFundamentalGroups.Purity

universe u v

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [IsAdicComplete (maximalIdeal R) R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Over a complete Noetherian local ring, a finite-length essential
submodule forces the entire module to be Artinian. -/
theorem isArtinian_of_completeLocal_finiteLength_essential_submodule
    (N : Submodule R M) (hN : IsEssentialSubmodule N) (hlen : IsFiniteLength R N) :
    IsArtinian R M := by
  obtain ⟨E, i, hi, hess, hEinj⟩ :=
    exists_module_injective_hull (ModuleCat.of R (R ⧸ maximalIdeal R))
  let : Module.Injective R E := hEinj
  let : IsArtinian R E := isArtinian_of_completeLocal_residueFieldHull i hi hess
  exact isArtinian_of_finiteLength_essential_submodule i hi hess N hN hlen

/-- Maximal-ideal-power torsion and an Artinian socle imply that a module
over a complete Noetherian local ring is Artinian. -/
theorem isArtinian_of_maximalIdealPower_torsion_of_artinian_socle
    [IsArtinian R (Submodule.torsionBySet R M (maximalIdeal R))]
    (hM : ∀ z : M, ∃ n : ℕ, ∀ a ∈ maximalIdeal R ^ n, a • z = 0) :
    IsArtinian R M :=
  isArtinian_of_completeLocal_finiteLength_essential_submodule
    (Submodule.torsionBySet R M (maximalIdeal R))
    (isEssentialSubmodule_torsionBySet_maximalIdeal_of_power_torsion hM)
    (isFiniteLength_torsionBySet_maximalIdeal_of_artinian M)

/-- A scalar kernel containing the socle gives the Artinian criterion
used with coefficient exact sequences in local cohomology. -/
theorem isArtinian_of_maximalIdealPower_torsion_of_artinian_scalarKernel
    (x : R) (hx : x ∈ maximalIdeal R)
    [IsArtinian R (LinearMap.ker (x • (LinearMap.id : M →ₗ[R] M)))]
    (hM : ∀ z : M, ∃ n : ℕ, ∀ a ∈ maximalIdeal R ^ n, a • z = 0) :
    IsArtinian R M := by
  have hle : Submodule.torsionBySet R M (maximalIdeal R) ≤
      LinearMap.ker (x • (LinearMap.id : M →ₗ[R] M)) := by
    intro z hz
    change x • z = 0
    exact (Submodule.mem_torsionBySet_iff
      (R := R) (M := M) (maximalIdeal R : Set R) z).mp hz ⟨x, hx⟩
  let : IsArtinian R (Submodule.torsionBySet R M (maximalIdeal R)) :=
    isArtinian_of_le hle
  exact isArtinian_of_maximalIdealPower_torsion_of_artinian_socle hM

end EtaleFundamentalGroups.Purity
