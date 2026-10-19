/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Unramified.Basic
import Mathlib.Algebra.Polynomial.Derivation

/-!
# The derivative criterion for a monogenic etale algebra

For an adjoined-root algebra, formal unramifiedness forces the derivative of
the defining polynomial at the distinguished root to be a unit.  The proof
descends the usual polynomial derivative to the quotient by the derivative
value.  This descended derivation sends the distinguished root to one, while
formal unramifiedness says that every such derivation is zero.
-/

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/--
If `AdjoinRoot f` is formally unramified over its coefficient ring, then the
derivative of `f` at the distinguished root is a unit.

No monicity hypothesis is needed for this direction.
-/
theorem isUnit_aeval_derivative_of_formallyUnramified
    {R : Type u} [CommRing R] (f : R[X])
    [Algebra.FormallyUnramified R (AdjoinRoot f)] :
    IsUnit (aeval (AdjoinRoot.root f) f.derivative) := by
  let d : AdjoinRoot f := aeval (AdjoinRoot.root f) f.derivative
  let I : Ideal (AdjoinRoot f) := Ideal.span {d}
  let q : AdjoinRoot f →ₐ[R] AdjoinRoot f ⧸ I := Ideal.Quotient.mkₐ R I
  let L₀ : R[X] →ₗ[R] AdjoinRoot f ⧸ I :=
    q.toLinearMap.comp
      ((AdjoinRoot.mkₐ f).toLinearMap.comp Polynomial.derivative'.toLinearMap)
  have hL₀ : ∀ p : R[X],
      p ∈ (Ideal.span {f} : Ideal R[X]).restrictScalars R → L₀ p = 0 := by
    intro p hp
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hp
    change Ideal.Quotient.mk I
      (AdjoinRoot.mk f (derivative (f * g))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change AdjoinRoot.mk f (derivative (f * g)) ∈ I
    rw [Polynomial.derivative_mul, map_add, map_mul, map_mul,
      AdjoinRoot.mk_self, zero_mul, add_zero]
    apply I.mul_mem_right
    change AdjoinRoot.mk f f.derivative ∈ Ideal.span ({d} : Set (AdjoinRoot f))
    apply Ideal.subset_span
    change AdjoinRoot.mk f f.derivative =
      aeval (AdjoinRoot.root f) f.derivative
    exact (AdjoinRoot.aeval_eq _).symm
  have hL₀ker :
      (Ideal.span {f} : Ideal R[X]).restrictScalars R ≤ LinearMap.ker L₀ := by
    intro p hp
    exact LinearMap.mem_ker.mpr (hL₀ p hp)
  let L : AdjoinRoot f →ₗ[R] AdjoinRoot f ⧸ I :=
    (Submodule.liftQ _ L₀ hL₀ker).comp
      (Submodule.Quotient.restrictScalarsEquiv R
        (Ideal.span {f} : Ideal R[X])).symm.toLinearMap
  have hL_mk (p : R[X]) :
      L (AdjoinRoot.mk f p) = q (AdjoinRoot.mk f p.derivative) := by
    change
      (Submodule.restrictScalars R (Ideal.span {f} : Ideal R[X])).liftQ L₀
          hL₀ker
          ((Submodule.Quotient.restrictScalarsEquiv R
            (Ideal.span {f} : Ideal R[X])).symm (Submodule.Quotient.mk p)) =
        q (AdjoinRoot.mk f p.derivative)
    rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk,
      Submodule.liftQ_apply]
    rfl
  let D : Derivation R (AdjoinRoot f) (AdjoinRoot f ⧸ I) :=
    Derivation.mk' L (by
      intro x y
      induction x using AdjoinRoot.induction_on with
      | ih p =>
          induction y using AdjoinRoot.induction_on with
          | ih g =>
              rw [← (AdjoinRoot.mk f).map_mul p g, hL_mk, hL_mk, hL_mk,
                Polynomial.derivative_mul]
              simp only [map_add, map_mul, Algebra.smul_def]
              ac_rfl)
  have hD_root : D (AdjoinRoot.root f) = 1 := by
    change L (AdjoinRoot.mk f X) = 1
    rw [hL_mk]
    simp [q]
  have hD_zero : D = 0 := by
    apply
      (KaehlerDifferential.linearMapEquivDerivation
        R (AdjoinRoot f)).symm.injective
    apply LinearMap.ext
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp only [map_zero]
  have hOne : (1 : AdjoinRoot f ⧸ I) = 0 := by
    calc
      (1 : AdjoinRoot f ⧸ I) = D (AdjoinRoot.root f) := hD_root.symm
      _ = (0 : Derivation R (AdjoinRoot f) (AdjoinRoot f ⧸ I))
          (AdjoinRoot.root f) := Derivation.congr_fun hD_zero _
      _ = 0 := rfl
  change IsUnit d
  rw [← Ideal.span_singleton_eq_top]
  change I = ⊤
  exact Ideal.Quotient.zero_eq_one_iff.mp hOne.symm

end EtaleFundamentalGroups.Kummer
