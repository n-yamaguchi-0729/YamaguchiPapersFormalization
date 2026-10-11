/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Ring.RingNF
import SchemeTheory.ProjectiveSpace.Basic
import SchemeTheory.ProjectiveSpace.Cover
import AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import AlgebraicCurves.Hilbert.Functor.Basic
import AlgebraicCurves.Foundations.Algebra.Nat_MacaulayPow
import AlgebraicCurves.Geometry.Projective.ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal

/-!
# Proj Space app away To Section linear Form mul eq zero imp of forall mul mem imp
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
  AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

/--
The homogeneous fraction represented by `F` divided by the `d`th power of the chosen coordinate.
-/
noncomputable def awayMk {n : ℕ} (k : Type) [Field k] (i : Fin (n + 1)) (d : ℕ) (F : MvPolynomial
  (Fin (n + 1)) k)
    (hF : F.IsHomogeneous d) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
      (MvPolynomial.X i) :=
  HomogeneousLocalization.mk
    { deg := d
      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
        (MvPolynomial.isHomogeneous_X_pow i d)⟩
      den_mem := ⟨d, rfl⟩ }

theorem val_awayMk {n : ℕ} (k : Type) [Field k] (i : Fin (n + 1)) (d : ℕ) (F : MvPolynomial (Fin (n
  + 1)) k)
    (hF : F.IsHomogeneous d) :
    (awayMk k i d F hF).val = Localization.mk F (⟨MvPolynomial.X i ^ d, ⟨d, rfl⟩⟩ :
      Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k)) := by
  rw [awayMk, HomogeneousLocalization.val_mk]

theorem awayMk_mul {n : ℕ} (k : Type) [Field k] (i : Fin (n + 1)) (d d' : ℕ) (F F' : MvPolynomial
  (Fin (n + 1)) k)
    (hF : F.IsHomogeneous d) (hF' : F'.IsHomogeneous d') :
    awayMk k i d F hF * awayMk k i d' F' hF' = awayMk k i (d + d') (F * F') (hF.mul hF') := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, val_awayMk, val_awayMk, val_awayMk, Localization.mk_mul,
    Localization.mk_eq_mk_iff]
  exact Localization.r_of_eq (by simp only [Submonoid.coe_mul]; ring)

theorem awayMk_X_pow_mul {n : ℕ} (k : Type) [Field k] (i : Fin (n + 1)) (N d : ℕ) (F : MvPolynomial
  (Fin (n + 1)) k)
    (hF : F.IsHomogeneous d) :
    awayMk k i (N + d) (MvPolynomial.X i ^ N * F) ((MvPolynomial.isHomogeneous_X_pow i N).mul hF) =
      awayMk k i d F hF := by
  apply HomogeneousLocalization.val_injective
  rw [val_awayMk, val_awayMk, Localization.mk_eq_mk_iff]
  exact Localization.r_of_eq (by simp only; ring)

end ProjSpace_app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp
end AlgebraicCurves.Geometry.Projective.Proofs

namespace AlgebraicGeometry

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.MvPolynomial _root_.AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

open _root_.AlgebraicCurves.Geometry.Projective.Proofs in
open ProjSpace_app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp in
theorem ProjSpace.app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp
    (n m : ℕ) (k : Type) [Field k]
    (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
      [IsClosedImmersion ιk]
    (hZ : (∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        (F ∈ J ↔ ∀ i : Fin (n + 1), (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin
          (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }))) = 0)))
    (a : Fin (n + 1) → k)
    (hnzd : ∀ e : ℕ, m ≤ e → ∀ f : MvPolynomial (Fin (n + 1)) k, f.IsHomogeneous e →
      (∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j) * f ∈ J → f ∈ J) :
    ∀ (i : Fin (n + 1)) (t : Γ(Zk, ιk ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n
      + 1)) k) (MvPolynomial.X i))),
        (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X
          i))
          (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
            (HomogeneousLocalization.mk
              { deg := 1
                num := ⟨(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j),
                  (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
                  (MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ =>
                    MvPolynomial.isHomogeneous_C_mul_X (a j) j)⟩
                den := ⟨MvPolynomial.X i ^ 1, (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
                  (MvPolynomial.isHomogeneous_X_pow i 1)⟩
                den_mem := ⟨1, rfl⟩ }))) * t = 0 → t = 0 := by
  classical
  intro i t ht
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k with h𝒜
  have hXi : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k) ∈ 𝒜 1 := ProjSpace.X_mem_one k n i
  have haff : IsAffineOpen (Proj.basicOpen 𝒜 (MvPolynomial.X i)) := Proj.isAffineOpen_basicOpen 𝒜
    (MvPolynomial.X i) hXi one_pos
  set ℓ : MvPolynomial (Fin (n + 1)) k := ∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X
    j with hℓ
  have hℓhom : ℓ.IsHomogeneous 1 := by
    rw [hℓ]; exact MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ =>
      MvPolynomial.isHomogeneous_C_mul_X (a j) j
  have hZ' : ∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
      (F ∈ J ↔ ∀ i : Fin (n + 1), (ιk.app (Proj.basicOpen 𝒜 (MvPolynomial.X i)))
        (Proj.awayToSection 𝒜 (MvPolynomial.X i) (awayMk k i d F hF)) = 0) :=
    hZ
  have ht' : (ιk.app (Proj.basicOpen 𝒜 (MvPolynomial.X i))) (Proj.awayToSection 𝒜 (MvPolynomial.X
    i) (awayMk k i 1 ℓ hℓhom)) * t = 0 := ht
  clear hZ ht
  obtain ⟨s, rfl⟩ := ιk.app_surjective (Proj.basicOpen 𝒜 (MvPolynomial.X i)) haff t
  obtain ⟨z, rfl⟩ : ∃ z, Proj.awayToSection 𝒜 (MvPolynomial.X i) z = s := by
    obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso (Proj.basicOpenIsoAway 𝒜 (MvPolynomial.X
      i) hXi one_pos).hom).2 s
    exact ⟨z, hz⟩
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  obtain ⟨j, hj⟩ := c.den_mem
  have hj' : MvPolynomial.X i ^ j = (c.den : MvPolynomial (Fin (n + 1)) k) := hj
  have hdeg : j = c.deg :=
    DirectSum.degree_eq_of_mem_mem 𝒜 ((MvPolynomial.mem_homogeneousSubmodule j _).2
      (MvPolynomial.isHomogeneous_X_pow i j))
      (hj' ▸ c.den.2) (pow_ne_zero j (MvPolynomial.X_ne_zero i))
  subst hdeg
  have hHe : (c.num : MvPolynomial (Fin (n + 1)) k).IsHomogeneous c.deg :=
    (MvPolynomial.mem_homogeneousSubmodule c.deg _).1 c.num.2
  have ez : HomogeneousLocalization.mk c = awayMk k i c.deg (c.num : MvPolynomial (Fin (n + 1)) k)
    hHe := by
    apply HomogeneousLocalization.val_injective
    rw [val_awayMk, HomogeneousLocalization.val_mk]
    congr 1
    exact Subtype.ext hj'.symm
  rw [ez] at ht' ⊢
  rw [← map_mul, ← map_mul, awayMk_mul] at ht'
  have hmem : Proj.awayToSection 𝒜 (MvPolynomial.X i) (awayMk k i (1 + c.deg) (ℓ * (c.num :
    MvPolynomial (Fin (n + 1)) k)) (hℓhom.mul hHe)) ∈
      ιk.ker.ideal ⟨Proj.basicOpen 𝒜 (MvPolynomial.X i), haff⟩ := by
    rw [Scheme.Hom.ker_apply]
    exact ht'
  obtain ⟨N, hNm, hN⟩ :=
    AlgebraicGeometry.ProjSpace.exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal n k
    ιk.ker i (1 + c.deg)
    (ℓ * (c.num : MvPolynomial (Fin (n + 1)) k)) (hℓhom.mul hHe) hmem m
  have hJ1 : MvPolynomial.X i ^ N * (ℓ * (c.num : MvPolynomial (Fin (n + 1)) k)) ∈ J := by
    refine (hZ' (N + (1 + c.deg))
      (by omega) _ ((MvPolynomial.isHomogeneous_X_pow i N).mul (hℓhom.mul hHe))).2 fun j' => ?_
    have := hN j'
    rw [Scheme.Hom.ker_apply] at this
    exact this
  have hJ2 : MvPolynomial.X i ^ N * (c.num : MvPolynomial (Fin (n + 1)) k) ∈ J := by
    apply hnzd (N + c.deg) (by omega) _ ((MvPolynomial.isHomogeneous_X_pow i N).mul hHe)
    have : ℓ * (MvPolynomial.X i ^ N * (c.num : MvPolynomial (Fin (n + 1)) k)) = MvPolynomial.X i ^
      N * (ℓ * (c.num : MvPolynomial (Fin (n + 1)) k)) := by ring
    rw [this]; exact hJ1
  have h0 := (hZ' (N + c.deg) (by omega) _ ((MvPolynomial.isHomogeneous_X_pow i N).mul hHe)).1 hJ2 i
  rw [awayMk_X_pow_mul] at h0
  exact h0
end AlgebraicGeometry
end ProofImplementation
