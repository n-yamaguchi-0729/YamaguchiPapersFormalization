/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.CompletePrimeOrderDetection
import Nyll.GaloisCohomology.Kummer.Concrete.CompletionAbelianModPower
import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.RelativeModPowerNaturality
import Nyll.ValuedFieldTheory.Valuation.Completion.StableGalois
import Nyll.ValuedFieldTheory.Valuation.Completion.DiscreteValuedCompletion

/-!
# Detecting prime-degree automorphisms through a stable completion

When a prolongation is invariant under the Galois group, its completion has the
same Galois degree. The complete-field detection theorem detects an automorphism
there, and the injective
weak-approximation map transports the detection to the original field.
-/

namespace Yamaguchi26AbfaithfulGalois
open KummerTheory ValuationTheory.DiscreteValuationField ProCGroups.Abelian
open Field.absoluteGaloisGroup
universe u v

/-- A prime-degree extension with invariant prolongation is detected by its
completed extension and the injection on mod-prime abelianizations. -/
theorem prime_order_detection_of_stable_valuation
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [CharZero K] (base : DVF.{u, v} K) (target : DVF.{u, v} L)
    [base.valuation.HasExtension target.valuation]
    (p r : ℕ) [Fact p.Prime] [Fact r.Prime]
    [CharP base.residueField p]
    (hdegree : Module.finrank K L = r)
    (hstable : ∀ τ : Gal(L/K),
      target.valuation.IsEquiv (target.valuation.comap τ.toRingEquiv.toRingHom)) :
    ∃ τ : Gal(L/K), τ ≠ 1 ∧
      ∃ z : abelianModPower Gal(AlgebraicClosure L/L) p,
        relativeGaloisAbelianModPowerTransform K L p τ z ≠ z := by
  have : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (hdegree.symm ▸ (Fact.out : r.Prime).pos)
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let _ : Algebra base.valuation.Completion target.valuation.Completion :=
    DVF.completionAlgebra base target
  have : FiniteDimensional base.valuation.Completion target.valuation.Completion :=
    DVF.completion_finiteDimensional base target
  have : IsGalois base.valuation.Completion target.valuation.Completion :=
    DVF.completion_isGalois_of_stable base target hstable
  have : CharZero base.valuation.Completion :=
    charZero_of_injective_algebraMap (algebraMap K base.valuation.Completion).injective
  let baseHat : CompleteDVF.{u,v} base.valuation.Completion :=
    { ValueGroup := base.ValueGroup
      valuation := Valued.v
      instCompleteDiscrete := Valuation.completion_isCompleteDiscrete base.valuation }
  have : CharP baseHat.residueField p := Valuation.completion_residueChar base.valuation p
  have hdegreeHat : Module.finrank base.valuation.Completion target.valuation.Completion = r :=
    (DVF.finrank_completion_eq_of_galois_stable base target hstable).trans hdegree
  have hdetect := prime_order_detection (K := base.valuation.Completion)
    (L := target.valuation.Completion) baseHat p r hdegreeHat
  rcases hdetect with ⟨τHat, hτHat, z, hz⟩
  obtain ⟨τ, hτ⟩ := DVF.completionAlgEquiv_surjective base target hstable τHat
  subst τHat
  refine ⟨τ, ?_, abelianModPowerMap p (map (algebraMap L target.valuation.Completion)) z, ?_⟩
  · intro heq
    apply hτHat
    apply AlgEquiv.ext
    intro x
    have hh : Continuous (DVF.completionAlgEquiv base target τ (hstable τ)) :=
      UniformSpace.Completion.continuous_map
    have hone : (fun y => DVF.completionAlgEquiv base target τ (hstable τ) y) =
        (fun y => y) := by
      apply UniformSpace.Completion.ext hh continuous_id
      intro y
      have hy := DVF.completionAlgEquiv_algebraMap base target τ (hstable τ)
        (WithVal.equiv target.valuation y)
      have hy' : τ (WithVal.equiv target.valuation y) = WithVal.equiv target.valuation y := by
        rw [heq]
        rfl
      exact hy.trans (congrArg (algebraMap L target.valuation.Completion) hy')
    exact congrFun hone x
  · intro heq
    apply hz
    apply completion_abelianModPowerMap_injective target p
    exact (relativeGaloisAbelianModPowerTransform_naturality p
      (algebraMap L target.valuation.Completion) τ
      (DVF.completionAlgEquiv base target τ (hstable τ))
      (DVF.completionAlgEquiv_algebraMap base target τ (hstable τ)) z).trans heq
end Yamaguchi26AbfaithfulGalois
