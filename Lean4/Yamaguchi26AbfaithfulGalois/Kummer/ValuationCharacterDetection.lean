/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Yamaguchi26AbfaithfulGalois.Kummer.WeakApproximationForCharacters
import Yamaguchi26AbfaithfulGalois.Kummer.RelativeAbelianModPowerAction
import GaloisCohomology.Kummer.Concrete.AbsoluteRestrictionConjugation
import ValuedFieldTheory.Valuation.Completion.DiscreteRingEquiv

/-!
# Characters detecting an automorphism that moves a valuation

Weak approximation prescribes a nonzero character on one completion and the
zero character on its inequivalent conjugate. These characters detect the
relative Galois action on abelianization modulo a prime.
-/

namespace Yamaguchi26AbfaithfulGalois
open KummerTheory ValuationTheory.DiscreteValuationField ProCGroups.Abelian
open Field.absoluteGaloisGroup
universe u v

private theorem completion_character_prescribed_pair
    {L : Type u} [Field L] (D : Fin 2 → DVF.{u, v} L)
    (hD : Pairwise (fun i j => ¬ (D i).valuation.IsEquiv (D j).valuation))
    (p : ℕ) [Fact p.Prime]
    (χ : Gal(AlgebraicClosure (D 0).valuation.Completion/(D 0).valuation.Completion) →ₜ*
      Multiplicative (ZMod p)) :
    ∃ ψ : Gal(AlgebraicClosure L/L) →ₜ* Multiplicative (ZMod p),
      completionCharacterRestriction (D 0) p ψ = χ ∧
      completionCharacterRestriction (D 1) p ψ = 1 := by
  let chars : (i : Fin 2) →
      Gal(AlgebraicClosure (D i).valuation.Completion/(D i).valuation.Completion) →ₜ*
        Multiplicative (ZMod p) :=
    Fin.cases (motive := fun i : Fin 2 =>
      Gal(AlgebraicClosure (D i).valuation.Completion/(D i).valuation.Completion) →ₜ*
        Multiplicative (ZMod p)) χ (fun _ => 1)
  obtain ⟨ψ, hψ⟩ := (weakApproximationForCharacters 2 D hD p).1 chars
  exact ⟨ψ, congrFun hψ 0, congrFun hψ 1⟩

/-- A nonzero local character and an inequivalent conjugate valuation detect
the relative action modulo a prime. -/
theorem exists_moved_mod_prime_of_inequivalent_completions
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (D : Fin 2 → DVF.{u, v} L)
    (hD : Pairwise (fun i j => ¬ (D i).valuation.IsEquiv (D j).valuation))
    (p : ℕ) [Fact p.Prime] (τ : Gal(L/K))
    (hτ : (D 1).valuation.IsEquiv ((D 0).valuation.comap τ.toRingEquiv.toRingHom))
    (χ : Gal(AlgebraicClosure (D 0).valuation.Completion/(D 0).valuation.Completion) →ₜ*
      Multiplicative (ZMod p))
    (a : Gal(AlgebraicClosure (D 0).valuation.Completion/(D 0).valuation.Completion))
    (ha' : χ a ≠ 1) :
    ∃ z : abelianModPower Gal(AlgebraicClosure L/L) p,
      relativeGaloisAbelianModPowerTransform K L p τ.symm z ≠ z := by
  obtain ⟨ψ, hψ0, hψ1⟩ := completion_character_prescribed_pair D hD p χ
  let e : (D 1).valuation.Completion ≃+* (D 0).valuation.Completion :=
    DVF.completionRingEquiv (D 1) (D 0) τ.toRingEquiv hτ
  have heq : (algebraMap L (D 0).valuation.Completion).comp τ.toRingEquiv.toRingHom =
      e.toRingHom.comp (algebraMap L (D 1).valuation.Completion) := by
    ext x
    exact (DVF.completionRingEquiv_algebraMap (D 1) (D 0) τ.toRingEquiv
      hτ x).symm
  let b : Gal(AlgebraicClosure L/L) := map (algebraMap L (D 0).valuation.Completion) a
  refine ⟨abelianModPowerMk _ p b, ?_⟩
  intro hfix
  have hpow : ∀ c : Multiplicative (ZMod p), c ^ p = 1 := by
    intro c
    apply Multiplicative.toAdd.injective
    change p • c.toAdd = (0 : ZMod p)
    simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hχfix := congrArg (abelianModPowerLift p ψ hpow) hfix
  change ψ (absoluteGaloisConjugate τ.symm.toRingEquiv b) = ψ b at hχfix
  have hmapfix : ψ (map τ.toRingEquiv.toRingHom b) = ψ b :=
    (character_map_symm_eq_absoluteGaloisConjugate τ.symm.toRingEquiv ψ b).trans hχfix
  have hzero : ψ (map τ.toRingEquiv.toRingHom b) = 1 := by
    exact (DFunLike.congr_fun (character_map_comp τ.toRingEquiv.toRingHom
      (algebraMap L (D 0).valuation.Completion) ψ) a).symm.trans
      ((congrArg (fun f : L →+* (D 0).valuation.Completion => ψ (map f a)) heq).trans
        ((DFunLike.congr_fun (character_map_comp
          (algebraMap L (D 1).valuation.Completion) e.toRingHom ψ) a).trans
            (DFunLike.congr_fun hψ1 (map e.toRingHom a))))
  apply ha'
  exact (DFunLike.congr_fun hψ0 a).symm.trans (hmapfix.symm.trans hzero)
end Yamaguchi26AbfaithfulGalois
