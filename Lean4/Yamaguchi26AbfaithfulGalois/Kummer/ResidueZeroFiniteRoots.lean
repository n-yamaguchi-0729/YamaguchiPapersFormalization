/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import ValuedFieldTheory.Ramification.HilbertRamification.DiscreteAbsoluteCenter
import ValuedFieldTheory.Valuation.Henselian.FiniteResidueRootLifting
import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Henselian
import ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
import GaloisCohomology.Kummer.Concrete.PrimaryRootsDivisibility
import Yamaguchi26AbfaithfulGalois.GroupTheory.FiniteFieldExtensions
import Yamaguchi26AbfaithfulGalois.GroupTheory.Faithful
import Yamaguchi26AbfaithfulGalois.GroupTheory.SlimFieldExtensions

/-!
# Finite residue root groups from slimness

Slimness over a residue-zero Henselian discrete valuation forces finite
primary root groups in every finite residue extension. Ab-faithfulness
provides the corresponding specialization.
-/

namespace Yamaguchi26AbfaithfulGalois

open ValuationTheory.DiscreteValuationField
open ProCGroups.FiniteStepSolvableQuotients

universe u v

/-- Slimness over a residue-zero Henselian DVF forces finite primary
root groups in every finite residue extension. -/
theorem finitePrimePowerRoots_of_residueZero_slim
    {K : Type u} [Field K] (D : HenselianDVF.{u, v} K) [CharZero D.residueField]
    (hK : IsSlim Gal(AlgebraicClosure K/K))
    (E : Type u) [Field E] [Algebra D.residueField E] [FiniteDimensional D.residueField E]
    (p : ℕ) (hp : p.Prime) : Finite (CommGroup.primaryComponent Eˣ p) := by
  classical
  by_contra hfinite
  have : Infinite (CommGroup.primaryComponent Eˣ p) := not_finite_iff_infinite.mp hfinite
  have : Fact p.Prime := ⟨hp⟩
  have : CharZero K := by
    refine ⟨fun m n h => ?_⟩
    apply Nat.cast_injective (R := D.residueField)
    have hv : (m : D.valuation.valuationSubring) = n := Subtype.ext h
    have hr := congrArg (IsLocalRing.residue D.valuation.valuationSubring) hv
    simpa only [map_natCast] using hr
  obtain ⟨Γ, hΓ, z, hz⟩ :=
    Valuation.chevalley_hasSomeExtensionTo (L := AlgebraicClosure K) D.valuation
  let : LinearOrderedCommGroupWithZero Γ := hΓ
  have : D.valuation.HasExtension z := hz
  obtain ⟨F, hfd, hF⟩ :=
    ValuationTheory.Henselian.exists_finiteIntermediateField_lifting_residue_roots
      D.valuation z E
  have : FiniteDimensional K F := hfd
  have hFroots (n : ℕ) : ∃ ζ : F, IsPrimitiveRoot ζ (p ^ n) := by
    apply hF (p ^ n) (pow_pos hp.pos n)
    obtain ⟨ζ, hζ⟩ := KummerTheory.exists_primitiveRoot_prime_pow_of_infinite_primary (K := E) p n
    exact ⟨(ζ : E), IsPrimitiveRoot.coe_units_iff.mpr hζ⟩
  let FD : HenselianDVF F := FiniteExtensionLocalization.henselianDVF D
  have : D.valuation.HasExtension FD.valuation :=
    FiniteExtensionLocalization.henselianDVF_hasExtension D
  have : CharZero FD.residueField :=
    charZero_of_injective_algebraMap (algebraMap D.residueField FD.residueField).injective
  have hFF : Subgroup.center Gal(AlgebraicClosure F/F) = ⊥ :=
    center_eq_bot_absoluteGaloisGroup_of_finiteExtension_of_isSlim hK
  obtain ⟨σ, hσc, hσ⟩ :=
    FD.exists_ne_one_mem_absoluteGalois_center_of_all_primePowerRoots p hFroots
  apply hσ
  rw [hFF] at hσc
  exact hσc

/-- The ab-faithful specialization of the slimness obstruction. -/
theorem finitePrimePowerRoots_of_residueZero_abFaithful
    {K : Type u} [Field K] (D : HenselianDVF.{u, v} K) [CharZero D.residueField]
    (hK : IsAbFaithful Gal(AlgebraicClosure K/K))
    (E : Type u) [Field E] [Algebra D.residueField E] [FiniteDimensional D.residueField E]
    (p : ℕ) (hp : p.Prime) : Finite (CommGroup.primaryComponent Eˣ p) :=
  finitePrimePowerRoots_of_residueZero_slim D (isSlim_of_isAbFaithful hK) E p hp

end Yamaguchi26AbfaithfulGalois
