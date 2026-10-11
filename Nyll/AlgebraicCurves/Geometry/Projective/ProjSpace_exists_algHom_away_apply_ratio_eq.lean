/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic

/-!
# Algebra maps from projective affine charts
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_exists_algHom_away_apply_ratio_eq

universe u v

open _root_.MvPolynomial
open _root_.HomogeneousLocalization
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace ProjSpace
open _root_.AlgebraicGeometry.ProjSpace
namespace ChartLift
open _root_.AlgebraicGeometry.ProjSpace
open _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1))
  {B : Type v} [CommRing B] [Algebra R B] (b : Fin (n + 1) → B) (hb : b i = 1)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- Evaluation on the localization where the chosen projective coordinate is invertible. -/
noncomputable def lift0 : Localization.Away (X i : MvPolynomial (Fin (n + 1)) R) →+* B :=
  IsLocalization.Away.lift (X i : MvPolynomial (Fin (n + 1)) R)
    (g := (MvPolynomial.aeval b : MvPolynomial (Fin (n + 1)) R →ₐ[R] B).toRingHom)
    (by simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, hb]; exact isUnit_one)

theorem lift0_algebraMap (p : MvPolynomial (Fin (n + 1)) R) :
    lift0 R n i b hb (algebraMap _ _ p) = MvPolynomial.aeval b p :=
  IsLocalization.Away.lift_eq _ _ _

/-- Evaluation of homogeneous affine-chart coordinates as an algebra homomorphism. -/
noncomputable def liftAway : Away 𝒜 (X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B where
  toRingHom := (lift0 R n i b hb).comp (algebraMap (Away 𝒜 (X i : MvPolynomial (Fin (n + 1)) R))
      (Localization.Away (X i : MvPolynomial (Fin (n + 1)) R)))
  commutes' r := by
    change lift0 R n i b hb ((algebraMap R (Away 𝒜 (X i : MvPolynomial (Fin (n + 1)) R)) r).val) =
        algebraMap R B r
    rw [ProjSpace.val_algebraMap, lift0_algebraMap, MvPolynomial.aeval_C]

theorem liftAway_ratio (k : Fin (n + 1)) : liftAway R n i b hb (ProjSpace.ratio R n i k) = b k := by
  change lift0 R n i b hb (ProjSpace.ratio R n i k).val = b k
  rw [ProjSpace.ratio, Away.val_mk, Localization.mk_eq_mk', lift0, IsLocalization.Away.lift,
      IsLocalization.lift_mk'_spec]
  change MvPolynomial.aeval b (X k) = MvPolynomial.aeval b (X i ^ 1) * b k
  simp only [pow_one, MvPolynomial.aeval_X, hb, one_mul]

include hb in
theorem exists_algHom :
    ∃ φ : Away 𝒜 (X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B, ∀ k, φ (ProjSpace.ratio R n i k) = b
        k :=
  ⟨liftAway R n i b hb, liftAway_ratio R n i b hb⟩

end AlgebraicGeometry.ProjSpace.ChartLift

section
attribute [local instance] MvPolynomial.gradedAlgebra
theorem _root_.AlgebraicGeometry.ProjSpace.exists_algHom_away_apply_ratio_eq
    (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1))
    {B : Type v} [CommRing B] [Algebra R B] (b : Fin (n + 1) → B) (hb : b i = 1) :
    ∃ φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B,
      ∀ k, φ (ProjSpace.ratio R n i k) = b k :=
  AlgebraicGeometry.ProjSpace.ChartLift.exists_algHom R n i b hb
end
end ProjSpace_exists_algHom_away_apply_ratio_eq
end AlgebraicCurves.Geometry.Projective.Proofs
end ProofImplementation
