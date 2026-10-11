/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.FormalHilbert90.AbsoluteCyclotomicOrientation
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Cyclotomic extensions and infinite orientations

Adjoining every primary root of unity gives the primary cyclotomic
extension. Infinite degree of that extension forces the absolute
cyclotomic orientation to have infinite image.
-/

namespace Yamaguchi26AbfaithfulGalois
universe u

/-- The actual field obtained by adjoining every p-power root of unity. -/
noncomputable def primaryCyclotomicExtension (K : Type u) [Field K] (p : ℕ) :
    IntermediateField K (SeparableClosure K) :=
  IntermediateField.adjoin K
    (Set.range (fun z : CommGroup.primaryComponent (SeparableClosure K)ˣ p =>
      (z.val : SeparableClosure K)))

/-- Infinite degree of the cyclotomic extension forces the absolute cyclotomic
orientation to have infinite image. -/
theorem infinite_range_absoluteCyclotomicOrientation_of_infinite_extension
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NeZero (p : K)]
    (hdegree : ¬ FiniteDimensional K (primaryCyclotomicExtension K p)) :
    Set.Infinite (Set.range (absoluteCyclotomicOrientation p K)) := by
  classical
  have : NeZero (p : SeparableClosure K) := ⟨by
    intro hp
    apply NeZero.ne (p : K)
    apply (algebraMap K (SeparableClosure K)).injective
    rw [map_natCast, map_zero]
    exact hp⟩
  let χ := galoisCyclotomicOrientation p K (SeparableClosure K)
  have hsep : Set.Infinite (Set.range χ) := by
    intro hfin
    have : Finite (Set.range χ) := hfin.to_subtype
    have hcont : Continuous (fun σ : Gal(SeparableClosure K/K) =>
        (⟨χ σ, σ, rfl⟩ : Set.range χ)) := χ.continuous.subtype_mk _
    let oneχ : Set.range χ := ⟨1, 1, map_one χ⟩
    have hopen : IsOpen (χ.toMonoidHom.ker : Set Gal(SeparableClosure K/K)) := by
      have ho := (isOpen_discrete ({oneχ} : Set (Set.range χ))).preimage hcont
      convert ho using 1
      ext σ
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    let E := IntermediateField.fixedField χ.toMonoidHom.ker
    have hfix : E.fixingSubgroup = χ.toMonoidHom.ker :=
      InfiniteGalois.fixingSubgroup_fixedField
        ⟨χ.toMonoidHom.ker, isClosed_eq χ.continuous continuous_const⟩
    have : FiniteDimensional K E := (InfiniteGalois.isOpen_iff_finite E).mp (by
      rw [hfix]
      exact hopen)
    have hle : primaryCyclotomicExtension K p ≤ E := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨z, rfl⟩
      exact KummerTheory.primaryUnit_mem_fixedField_cyclotomic_ker p z
    apply hdegree
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  intro hfin
  apply hsep
  have hrange : Set.range χ = Set.range (absoluteCyclotomicOrientation p K) := by
    ext a
    constructor
    · rintro ⟨τ, rfl⟩
      obtain ⟨σ, rfl⟩ :=
        (ValuationTheory.Completion.separableClosureAutContinuousEquiv K).surjective τ
      exact ⟨σ, rfl⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨ValuationTheory.Completion.separableClosureAutContinuousEquiv K σ, rfl⟩
  exact hrange ▸ hfin

end Yamaguchi26AbfaithfulGalois
