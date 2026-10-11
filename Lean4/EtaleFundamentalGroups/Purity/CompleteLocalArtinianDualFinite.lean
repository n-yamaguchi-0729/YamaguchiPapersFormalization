/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.ArtinianSocleFiniteLength
import EtaleFundamentalGroups.Purity.CompleteLocalResidueFieldHullArtinian
import EtaleFundamentalGroups.Purity.EssentialModuleExtension
import EtaleFundamentalGroups.Purity.FiniteLengthInjectiveEmbedding
import EtaleFundamentalGroups.Purity.MaximalIdealPowerTorsionSocle
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.FiniteLength

/-!
# Finite duals of Artinian power-torsion modules

The finite-length socle of an Artinian maximal-ideal-power torsion module
embeds in a finite product of residue-field hulls.  Injectivity extends
this embedding to the module, and essentialness keeps it injective.
The coordinate maps generate its dual: extend an arbitrary dual map to
the finite product and use the scalar description of each endomorphism
of the hull.  Completeness enters only through this scalar description.
-/

namespace EtaleFundamentalGroups.Purity

universe u v

open IsLocalRing
open scoped BigOperators

variable {R E : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [IsAdicComplete (maximalIdeal R) R]
variable [AddCommGroup E] [Module R E] [Module.Injective R E]

/-- The dual into a residue-field injective hull of an Artinian module
whose elements are killed by maximal-ideal powers is finitely generated
over the complete Noetherian local ring. -/
theorem finite_linearMap_to_completeLocal_residueFieldHull_of_artinian
    (i : (R ⧸ maximalIdeal R) →ₗ[R] E) (hi : Function.Injective i)
    (hess : IsEssentialSubmodule (LinearMap.range i))
    {A : Type v} [AddCommGroup A] [Module R A] [IsArtinian R A]
    (hA : ∀ z : A, ∃ n : ℕ, ∀ a ∈ maximalIdeal R ^ n, a • z = 0) :
    Module.Finite R (A →ₗ[R] E) := by
  classical
  let N : Submodule R A := Submodule.torsionBySet R A (maximalIdeal R)
  have hN : IsEssentialSubmodule N :=
    isEssentialSubmodule_torsionBySet_maximalIdeal_of_power_torsion hA
  have hlength : IsFiniteLength R N :=
    isFiniteLength_torsionBySet_maximalIdeal_of_artinian A
  obtain ⟨n, j, hj⟩ := exists_injective_linearMap_pi_of_finiteLength i hi hess hlength
  obtain ⟨f, hf⟩ := Module.Injective.extension_property
    R (Fin n → E) N A N.subtype N.subtype_injective j
  have hdisjoint : Disjoint N (LinearMap.ker f) := by
    apply Submodule.disjoint_def.mpr
    intro z hzN hzf
    have hjz : j ⟨z, hzN⟩ = 0 := by
      rw [← hf]
      exact hzf
    have hz : (⟨z, hzN⟩ : N) = 0 := hj (hjz.trans j.map_zero.symm)
    exact congrArg Subtype.val hz
  have hfinj : Function.Injective f := LinearMap.ker_eq_bot.mp (hN _ hdisjoint)
  let generators : Fin n → (A →ₗ[R] E) :=
    fun k => (LinearMap.proj k).comp f
  have hspan : Submodule.span R (Set.range generators) = ⊤ := by
    apply le_antisymm le_top
    intro g _hg
    obtain ⟨g', hg'⟩ := Module.Injective.extension_property
      R E A (Fin n → E) f hfinj g
    have hscalar (k : Fin n) : ∃ r : R, ∀ z : E,
        (g'.comp (LinearMap.single R (fun _ : Fin n => E) k)) z = r • z :=
      exists_smul_eq_of_completeLocal_residueFieldHull i hi hess
        (g'.comp (LinearMap.single R (fun _ : Fin n => E) k))
    let r : Fin n → R := fun k => Classical.choose (hscalar k)
    have hr (k : Fin n) (z : E) :
        (g'.comp (LinearMap.single R (fun _ : Fin n => E) k)) z = r k • z :=
      Classical.choose_spec (hscalar k) z
    have hgsum : g = ∑ k : Fin n, r k • generators k := by
      ext z
      rw [LinearMap.sum_apply]
      calc
        g z = g' (f z) := (LinearMap.congr_fun hg' z).symm
        _ = g' (∑ k : Fin n, Pi.single k (f z k)) := by
          rw [Finset.univ_sum_single]
        _ = ∑ k : Fin n, g' (Pi.single k (f z k)) := map_sum g' _ _
        _ = ∑ k : Fin n, (r k • generators k) z := by
          apply Finset.sum_congr rfl
          intro k _hk
          exact hr k (f z k)
    rw [hgsum]
    apply Submodule.sum_mem
    intro k _hk
    exact Submodule.smul_mem _ (r k)
      (Submodule.subset_span (Set.mem_range_self k))
  exact Module.Finite.of_fg_top
    (hspan ▸ Submodule.fg_span (Set.finite_range generators))

end EtaleFundamentalGroups.Purity
