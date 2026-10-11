/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.RelativeAbelianModPowerAction
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteAbelianizationAction
import Nyll.ProCGroups.Abelian.PowerQuotientAction
import Nyll.ProCGroups.FiniteGroups.PrimeOrderHom
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.ProlongationDiscrete
import Mathlib.FieldTheory.Galois.Basic

/-!
# Reducing finite Galois faithfulness to prime degree

Prime-degree detection yields faithful mod-prime abelianization actions
for finite Galois extensions by passing to fixed fields of prime-order
subgroups in a hypothetical kernel.
-/

namespace Yamaguchi26AbfaithfulGalois

open KummerTheory ProCGroups.Abelian ProCGroups.FiniteStepSolvableQuotients
open ValuationTheory.DiscreteValuationField

universe u v

private noncomputable def relativeModPowerAction
    (K L : Type u) [Field K] [Field L] [Algebra K L] (p : ℕ) :
    Gal(L/K) →* MulAut (abelianModPower Gal(AlgebraicClosure L/L) p) where
  toFun τ := powerQuotientAction p (absoluteGaloisAbelianizationAction τ.toRingEquiv)
  map_one' := by
    change powerQuotientAction p (absoluteGaloisAbelianizationAction 1) = 1
    rw [map_one, map_one]
  map_mul' τ σ := by
    change powerQuotientAction p
      (absoluteGaloisAbelianizationAction (τ.toRingEquiv * σ.toRingEquiv)) = _
    rw [map_mul, map_mul]

private theorem relativeModPowerAction_apply
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (p : ℕ) (τ : Gal(L/K)) (z : abelianModPower Gal(AlgebraicClosure L/L) p) :
    relativeModPowerAction K L p τ z =
      relativeGaloisAbelianModPowerTransform K L p τ z := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom (α := TopologicalAbelianization Gal(AlgebraicClosure L/L)) p).range z
  obtain ⟨σ, rfl⟩ := TopologicalAbelianization.surjective_mk _ a
  change QuotientGroup.mk' _ (absoluteGaloisAbelianizationAction τ.toRingEquiv
      (TopologicalAbelianization.mk _ σ)) = _
  rw [absoluteGaloisAbelianizationAction_apply_mk]
  rfl

/-- Prime-degree detection makes the actual mod-p action faithful for every
finite Galois extension. A prime-order subgroup of the kernel would give a
prime-degree extension over its fixed field, contradicting detection there. -/
theorem relativeGaloisAbelianModPowerTransform_faithful_of_primeDegree_detection
    (p : ℕ) [Fact p.Prime]
    (hdetect : ∀ (F E : Type u) [Field F] [Field E] [Algebra F E]
      [IsGalois F E] [CharZero F]
      (base : DVF.{u, v} F) [CharP base.residueField p]
      (r : ℕ) [Fact r.Prime], Module.finrank F E = r →
        ∃ τ : Gal(E/F), τ ≠ 1 ∧
          ∃ z : abelianModPower Gal(AlgebraicClosure E/E) p,
            relativeGaloisAbelianModPowerTransform F E p τ z ≠ z)
    {K : Type u} [Field K] [CharZero K]
    (base : DVF.{u, v} K) [CharP base.residueField p]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    ∀ τ : Gal(L/K),
      (∀ z : abelianModPower Gal(AlgebraicClosure L/L) p,
        relativeGaloisAbelianModPowerTransform K L p τ z = z) → τ = 1 := by
  classical
  let ρ := relativeModPowerAction K L p
  have hfaith : Function.Injective ρ := by
    by_contra hρ
    obtain ⟨C, hCprime, hCker⟩ :=
      exists_prime_card_subgroup_le_ker_of_not_injective ρ hρ
    let F : IntermediateField K L := IntermediateField.fixedField C
    have : Fact (Nat.card C).Prime := ⟨hCprime⟩
    have hdegree : Module.finrank F L = Nat.card C :=
      IntermediateField.finrank_fixedField_eq_card C
    obtain ⟨target, _, hres⟩ := base.exists_extension_residueChar (L := F) p
    have : CharP target.residueField p := hres
    obtain ⟨τ, _hτ, z, hz⟩ := hdetect F L target (Nat.card C) hdegree
    let e : C ≃* Gal(L/F) := IntermediateField.subgroupEquivAlgEquiv C
    let s : C := e.symm τ
    have hs : ρ (s : Gal(L/K)) = 1 := hCker s.property
    have he : (s : Gal(L/K)).toRingEquiv = τ.toRingEquiv :=
      congrArg AlgEquiv.toRingEquiv (e.apply_symm_apply τ)
    have hzfix := congrArg
      (fun a : MulAut (abelianModPower Gal(AlgebraicClosure L/L) p) => a z) hs
    change relativeModPowerAction K L p (s : Gal(L/K)) z = z at hzfix
    rw [relativeModPowerAction_apply] at hzfix
    apply hz
    change abelianModPowerMap p
      (ContinuousMonoidHom.toContinuousMonoidHom
        (absoluteGaloisConjugateContinuousEquiv τ.toRingEquiv)) z = z
    change abelianModPowerMap p
      (ContinuousMonoidHom.toContinuousMonoidHom
        (absoluteGaloisConjugateContinuousEquiv (s : Gal(L/K)).toRingEquiv)) z = z at hzfix
    rw [he] at hzfix
    exact hzfix
  intro τ hτ
  apply hfaith
  rw [map_one]
  apply MulEquiv.ext
  intro z
  change relativeModPowerAction K L p τ z = z
  rw [relativeModPowerAction_apply]
  exact hτ z

end Yamaguchi26AbfaithfulGalois
