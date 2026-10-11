/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.QuadraticSquareClasses
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.DyadicNorm
import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.TrivialAction
import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.RelativeAbelianModPowerAction
import Nyll.ProCGroups.Abelian.AbelianModPower
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Nontrivial dyadic mod-two action

The dyadic detection result retained from the earlier manuscript. A quadratic norm outside the two
square classes gives a nonsquare norm in the extension. Trivial conjugation
on the actual mod-two abelianization would make every norm a square by
Kummer theory, which is a contradiction.
-/

namespace Yamaguchi26AbfaithfulGalois

open KummerTheory ValuationTheory.DiscreteValuationField ProCGroups.Abelian

universe u v

/-- Dyadic mod-two detection: a quadratic extension acts
nontrivially on `G_Lᵃᵇ/2` in residue characteristic two. -/
theorem dyadic_mod_two
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [CharZero K] (base : HenselianDVF.{u, v} K)
    [CharP base.residueField 2]
    (hdegree : Module.finrank K L = 2) :
    ∃ τ : Gal(L/K), τ ≠ 1 ∧
      ∃ z : abelianModPower Gal(AlgebraicClosure L/L) 2,
        relativeGaloisAbelianModPowerTransform K L 2 τ z ≠ z := by
  classical
  have : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; decide)
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have : Algebra.IsQuadraticExtension K L := ⟨hdegree⟩
  have : IsGalois K L := inferInstance
  have hcard : Nat.card Gal(L/K) = 2 :=
    (IsGalois.card_aut_eq_finrank K L).trans hdegree
  obtain ⟨τ, hτ, _⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).mp hcard
  refine ⟨τ, hτ, ?_⟩
  by_contra hnone
  have hfixed (z : abelianModPower Gal(AlgebraicClosure L/L) 2) :
      relativeGaloisAbelianModPowerTransform K L 2 τ z = z :=
    not_not.mp (fun hz => hnone ⟨z, hz⟩)
  have hcharacters
      (χ : Gal(AlgebraicClosure L/L) →ₜ* Multiplicative (ZMod 2))
      (σ : Gal(AlgebraicClosure L/L)) :
      χ (absoluteGaloisConjugate τ.toRingEquiv σ) = χ σ := by
    have hpow : ∀ a : Multiplicative (ZMod 2), a ^ 2 = 1 := by
      intro a
      apply Multiplicative.toAdd.injective
      change 2 • a.toAdd = (0 : ZMod 2)
      simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    let χbar := abelianModPowerLift 2 χ hpow
    have heq := congrArg χbar (hfixed
      ((ProCGroups.Abelian.TopologicalAbelianization.mk _ σ :
        TopologicalAbelianization _) :
          abelianModPower Gal(AlgebraicClosure L/L) 2))
    exact heq
  have hmu : (primitiveRoots 2 L).Nonempty :=
    ⟨-1, (mem_primitiveRoots (by decide : 0 < 2)).mpr
      (IsPrimitiveRoot.neg_one 0 (by decide))⟩
  have hroots (ξ : L) (hξ : ξ ^ 2 = 1) : τ.toRingEquiv ξ = ξ ^ 1 := by
    rw [pow_one]
    rcases eq_or_eq_neg_of_sq_eq_sq ξ (1 : L)
      (by simpa only [one_pow] using hξ) with hp | hn
    · rw [hp, map_one]
    · rw [hn, map_neg, map_one]
  let n : ℕ+ := ⟨2, by decide⟩
  have : NeZero ((n : ℕ) : L) := ⟨by change (2 : L) ≠ 0; norm_num⟩
  have hunits := (kummer_trivial_action_criterion L n hmu
    τ.toRingEquiv 1 hroots).mp hcharacters
  obtain ⟨a, α, hα0, hαsq, hanti, hns⟩ := exists_quadratic_antiInvariant hdegree τ hτ
  obtain ⟨x, y, hn, hna⟩ := base.exists_quadraticForm_outside_squareClasses a hns
  let z : L := algebraMap K L x + α * algebraMap K L y
  have hnorm : z * τ z = algebraMap K L (x ^ 2 - a * y ^ 2) := by
    calc
      z * τ z = (algebraMap K L x) ^ 2 - α ^ 2 * (algebraMap K L y) ^ 2 := by
        dsimp only [z]
        rw [map_add, map_mul, τ.commutes, τ.commutes, hanti]
        ring
      _ = algebraMap K L (x ^ 2 - a * y ^ 2) := by
        rw [hαsq, map_sub, map_mul, map_pow, map_pow]
  have hnormns : ¬ IsSquare (algebraMap K L (x ^ 2 - a * y ^ 2)) := by
    intro hs
    exact ((isSquare_algebraMap_iff_of_quadratic hdegree τ hτ a α hα0 hαsq hanti _).mp
      hs).elim hn hna
  have hz0 : z ≠ 0 := by
    intro hz
    apply hnormns
    rw [← hnorm, hz, zero_mul]
    exact ⟨0, (zero_mul 0).symm⟩
  let u : Lˣ := Units.mk0 z hz0
  have hu := hunits u
  rw [pow_one] at hu
  have hmem : u⁻¹ * Units.map τ.toRingEquiv.toMonoidHom u ∈
      (powMonoidHom 2 : Lˣ →* Lˣ).range := QuotientGroup.eq.mp hu.symm
  obtain ⟨b, hb⟩ := hmem
  have hbval : (b : L) ^ 2 = z⁻¹ * τ z := congrArg Units.val hb
  have hprod : z * (b : L) ^ 2 = τ z := by
    rw [hbval, ← mul_assoc, mul_inv_cancel₀ hz0, one_mul]
  apply hnormns
  refine ⟨z * (b : L), ?_⟩
  rw [← hnorm, ← hprod]
  ring

end Yamaguchi26AbfaithfulGalois
