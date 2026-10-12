/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.WeilPairing.Divisorial
import Nyll.JacobianVarieties.Pic0.Pic0_exists_injective_conorm_of_constantFieldExtension_of_isAlgClosed
import Nyll.AlgebraicCurves.Divisors.ConstantExtensionEvaluation
import Nyll.AlgebraicCurves.Places.Place_isRational_iff_deg_eq_one

/-!
# Divisorial Weil pairing under algebraically closed constant extension

The actual unique valuation lifts define conorm on divisors and Picard
groups. Transporting a Weil datum along those lifts preserves its pairing
through the coefficient embedding. Hence the constructed divisorial Weil
pairings commute with this actual conorm, without an assumed pairing
comparison.
-/

noncomputable section

open AlgebraicCurve
open JacobianVarieties.Pic0.Proofs.ConormInjectivity.AlgebraicCurve.ConDesc

namespace JacobianVarieties.WeilPairing

attribute [local instance] IsCurveOver.toHasPrincipalDivisors

variable {K F K' F' : Type*}
  [Field K] [Field F] [Field K'] [Field F']
  [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
  [IsScalarTower K K' F'] [IsScalarTower K F F']
  [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
  (hfg : ∃ x : F, Transcendental K x ∧
    FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
  (hfg' : ∃ x : F', Transcendental K' x ∧
    FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
  (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)

omit [IsAlgClosed K'] [IsCurveOver K' F'] in
/-- The divisor of an extended function is the actual conorm of its divisor. -/
theorem ord_map_eq_mul_con
    (n : ℕ) (D : Divisor K F) (f : F) (hf : f ≠ 0)
    (hdiv : ∀ v : Place K F, v.ord f = (n : ℤ) * D v)
    (v' : Place K' F') :
    v'.ord (algebraMap F F' f) = (n : ℤ) * con hfg hfg' hgen D v' := by
  classical
  by_cases hv : ∃ v, lift hfg hfg' hgen v = v'
  · obtain ⟨v, rfl⟩ := hv
    rw [ord_lift, con_apply_lift]
    exact hdiv v
  · push Not at hv
    rw [ord_eq_zero_of_forall_comap_ne hfg v' (lift_new hfg hfg' hgen v' hv) hf,
      con_apply_of_forall_ne hfg hfg' hgen D v' hv, mul_zero]

/-- Transport a Weil datum by the actual constant-extension conorm. -/
def constantExtensionDatum {n : ℕ} (d : WeilDatum K F n) : WeilDatum K' F' n where
  D₁ := con hfg hfg' hgen d.D₁
  D₂ := con hfg hfg' hgen d.D₂
  f₁ := algebraMap F F' d.f₁
  f₂ := algebraMap F F' d.f₂
  f₁_ne_zero := (map_ne_zero _).mpr d.f₁_ne_zero
  f₂_ne_zero := (map_ne_zero _).mpr d.f₂_ne_zero
  ord_f₁ := ord_map_eq_mul_con hfg hfg' hgen n d.D₁ d.f₁ d.f₁_ne_zero d.ord_f₁
  ord_f₂ := ord_map_eq_mul_con hfg hfg' hgen n d.D₂ d.f₂ d.f₂_ne_zero d.ord_f₂
  disjoint := by
    intro v'
    classical
    by_cases hv : ∃ v, lift hfg hfg' hgen v = v'
    · obtain ⟨v, rfl⟩ := hv
      rw [con_apply_lift, con_apply_lift]
      exact d.disjoint v
    · push Not at hv
      exact Or.inl (con_apply_of_forall_ne hfg hfg' hgen d.D₁ v' hv)
  rational := fun v' _ =>
    v'.isRational_iff_deg_eq_one.mpr (IsCurveOver.deg_eq_one_of_isAlgClosed v')

/-- The transported pairing value is the coefficient image of the original
value; this follows from actual residue evaluation. -/
theorem constantExtensionDatum_pairing {n : ℕ} (d : WeilDatum K F n) :
    (constantExtensionDatum hfg hfg' hgen d).pairing = algebraMap K K' d.pairing := by
  have hcoeff (a : K) : algebraMap F F' (algebraMap K F a) =
      algebraMap K' F' (algebraMap K K' a) :=
    (IsScalarTower.algebraMap_apply K F F' a).symm.trans
      (IsScalarTower.algebraMap_apply K K' F' a)
  have heval (f : F) (D : Divisor K F)
      (hrat : ∀ v ∈ D.support, v.IsRational)
      (hmem : ∀ v ∈ D.support, f ∈ v.toValuationSubring) :
      Divisor.evalFun (algebraMap F F' f) (con hfg hfg' hgen D) =
        algebraMap K K' (Divisor.evalFun f D) :=
    Divisor.evalFun_mapDomain_of_comap (algebraMap K K') (algebraMap F F') hcoeff
      (lift hfg hfg' hgen) (lift_injective hfg hfg' hgen) (comap_lift hfg hfg' hgen)
      D f hrat hmem
  change Divisor.evalFun (algebraMap F F' d.f₁) (con hfg hfg' hgen d.D₂) /
    Divisor.evalFun (algebraMap F F' d.f₂) (con hfg hfg' hgen d.D₁) = _
  rw [heval d.f₁ d.D₂ (fun v hv => d.rational_of_mem_support_right hv)
      (fun v hv => v.mem_toValuationSubring_of_ord_nonneg_alt d.f₁_ne_zero
        (d.ord_f₁_eq_zero_of_mem_support hv).ge),
    heval d.f₂ d.D₁ (fun v hv => d.rational_of_mem_support_left hv)
      (fun v hv => v.mem_toValuationSubring_of_ord_nonneg_alt d.f₂_ne_zero
        (d.ord_f₂_eq_zero_of_mem_support hv).ge)]
  exact (map_div₀ (algebraMap K K') _ _).symm

/-- The actual conorm homomorphism restricted to n-torsion classes. -/
def constantExtensionTorsion (n : ℕ) : Pic0.torsion K F n →+ Pic0.torsion K' F' n where
  toFun x := ⟨conPic0 hfg hfg' hgen x.1, by
    rw [Pic0.mem_torsion, ← map_zsmul, Pic0.mem_torsion.mp x.2, map_zero]⟩
  map_zero' := Subtype.ext (conPic0 hfg hfg' hgen).map_zero
  map_add' x y := Subtype.ext ((conPic0 hfg hfg' hgen).map_add x.1 y.1)

private theorem constantExtensionDatum_classLeft {n : ℕ} [NeZero n] (d : WeilDatum K F n) :
    (constantExtensionDatum hfg hfg' hgen d).classLeft =
      constantExtensionTorsion hfg hfg' hgen n d.classLeft := by
  apply Subtype.ext
  change Pic0.mk (constantExtensionDatum hfg hfg' hgen d).degZeroLeft =
    conPic0 hfg hfg' hgen (Pic0.mk d.degZeroLeft)
  rw [conPic0_mk]
  apply congrArg Pic0.mk
  apply Subtype.ext
  rfl

private theorem constantExtensionDatum_classRight {n : ℕ} [NeZero n] (d : WeilDatum K F n) :
    (constantExtensionDatum hfg hfg' hgen d).classRight =
      constantExtensionTorsion hfg hfg' hgen n d.classRight := by
  apply Subtype.ext
  change Pic0.mk (constantExtensionDatum hfg hfg' hgen d).degZeroRight =
    conPic0 hfg hfg' hgen (Pic0.mk d.degZeroRight)
  rw [conPic0_mk]
  apply congrArg Pic0.mk
  apply Subtype.ext
  rfl

/-- Constructed divisorial Weil pairings commute with the actual conorm
under algebraically closed constant extension. -/
theorem pair_constantExtension {n : ℕ} [NeZero n]
    (w : DivisorialWeilPairingData K F n) (w' : DivisorialWeilPairingData K' F' n)
    (x y : Pic0.torsion K F n) :
    w'.pair (constantExtensionTorsion hfg hfg' hgen n x)
      (constantExtensionTorsion hfg hfg' hgen n y) = algebraMap K K' (w.pair x y) := by
  obtain ⟨d, hx, hy⟩ := w.exists_datum x y
  have h := w'.compatible (constantExtensionDatum hfg hfg' hgen d)
  rw [constantExtensionDatum_classLeft, constantExtensionDatum_classRight, hx, hy,
    constantExtensionDatum_pairing] at h
  rw [← w.compatible d, hx, hy] at h
  exact h

end JacobianVarieties.WeilPairing
