/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.PureRadical.HenselianClassification

/-!
# Coordinates on intermediate fields of a pure radical extension

The intermediate-field equality is converted here into the concrete
generator needed by the one-divisor normalization argument.  If
`e = [L : K]`, `d = [L : F]`, and `m = [F : K]`, then the generator is
`β = α ^ d`, it satisfies `β ^ m = π`, and `m * d = e`.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe u v w x

/-- Concrete generator and degree coordinates for an intermediate field of
a pure radical extension. -/
theorem exists_intermediateField_generator_pow_eq_of_pureRadical
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (α : L) (hα : α ≠ 0) (π : K)
    (hpow : α ^ Module.finrank K L = algebraMap K L π)
    (hgen : IntermediateField.adjoin K {α} = ⊤)
    (hroots : ∀ ζ : L, ζ ^ Module.finrank K L = 1 →
      ζ ∈ Set.range (algebraMap K L))
    (F : IntermediateField K L) :
    ∃ β : F,
      (β : L) = α ^ Module.finrank F L ∧
        β ^ Module.finrank K F = algebraMap K F π ∧
          IntermediateField.adjoin K ({(β : L)} : Set L) = F ∧
            Module.finrank K F * Module.finrank F L =
              Module.finrank K L := by
  let d := Module.finrank F L
  have hclass :
      F = IntermediateField.adjoin K
        {α ^ d} := by
    simpa only [d] using
      intermediateField_eq_adjoin_pow_finrank_of_pureRadical
        α hα ⟨π, hpow.symm⟩ hgen hroots F
  have hmem : α ^ d ∈ F := by
    rw [hclass]
    exact IntermediateField.subset_adjoin K _ (Set.mem_singleton _)
  let β : F := ⟨α ^ d, hmem⟩
  refine ⟨β, by rfl, ?_, ?_, Module.finrank_mul_finrank K F L⟩
  · apply Subtype.ext
    change (α ^ d) ^ Module.finrank K F =
      algebraMap K L π
    calc
      (α ^ d) ^ Module.finrank K F =
          α ^ (d * Module.finrank K F) := by
        rw [pow_mul]
      _ = α ^ (Module.finrank K F * d) := by
        rw [Nat.mul_comm]
      _ = α ^ Module.finrank K L := by
        dsimp only [d]
        rw [Module.finrank_mul_finrank K F L]
      _ = algebraMap K L π := hpow
  · simpa only [β, d] using hclass.symm

/-- Henselian integral-model source for the concrete intermediate-field
generator.  The roots-of-unity condition is derived from the normal local
model and the residue-field equivalence. -/
theorem exists_intermediateField_generator_pow_eq_of_henselian_pureRadical
    {A : Type u} {B : Type v} {K : Type w} {L : Type x}
    [CommRing A] [CommRing B] [IsDomain B]
    [HenselianLocalRing A] [IsLocalRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra B L] [Algebra K L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing B L] [IsIntegrallyClosed B]
    [Algebra.IsIntegral A B] [IsLocalHom (algebraMap A B)]
    [FiniteDimensional K L]
    (α : L) (hα : α ≠ 0) (π : K)
    (hpow : α ^ Module.finrank K L = algebraMap K L π)
    (hgen : IntermediateField.adjoin K {α} = ⊤)
    (hdegreeUnit : IsUnit (Module.finrank K L : A))
    (hresidue : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap A B)))
    (F : IntermediateField K L) :
    ∃ β : F,
      (β : L) = α ^ Module.finrank F L ∧
        β ^ Module.finrank K F = algebraMap K F π ∧
          IntermediateField.adjoin K ({(β : L)} : Set L) = F ∧
            Module.finrank K F * Module.finrank F L =
              Module.finrank K L := by
  apply exists_intermediateField_generator_pow_eq_of_pureRadical
    α hα π hpow hgen
  intro ζ hζpow
  exact rootOfUnity_mem_fractionBase_of_henselian_of_residue_bijective
    hdegreeUnit hresidue ζ hζpow

end EtaleFundamentalGroups.Kummer
