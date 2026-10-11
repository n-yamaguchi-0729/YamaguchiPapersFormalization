/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Nyll.ValuedFieldTheory.Valuation.Completion.TensorProductDecomposition

/-!
# Selecting an absolute-value completion from a tensor component

For a finite separable field extension `L / K`, the completion tensor
decomposition identifies `L ⊗[K] K̂` with the finite product of the
completions `Lₓ` over all exact extensions `w` of a fixed nontrivial absolute
value on `K`.

This file proves that every maximal ideal of the tensor product is the kernel
of one of the canonical coordinate maps.  The coordinate is obtained from the
prime-spectrum classification of a finite product; it is not supplied as an
assumption.
-/

noncomputable section

open scoped TensorProduct
open AlgebraicNumberTheory.Valuations

namespace EtaleFundamentalGroups

universe uK uL

/-- The canonical map from the completion tensor product to the completion
selected by an exact absolute-value extension. -/
noncomputable def completionTensorAbsoluteValueCoordinateHom
    {K : Type uK} {L : Type uL}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    L ⊗[K] vK.Completion →+* w.1.Completion := by
  classical
  letI := Algebra.TensorProduct.rightAlgebra
    (R := K) (A := L) (B := vK.Completion)
  letI : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u ↦ AbsoluteValue.completionAlgebra vK u.1 u.2
  exact
    (Pi.evalRingHom (fun u : AbsoluteValueExtension vK L ↦ u.1.Completion) w).comp
      (completionTensorDecomposition
        (K := K) (L := L) vK hvK).toRingEquiv.toRingHom

@[simp]
theorem completionTensorAbsoluteValueCoordinateHom_tmul
    {K : Type uK} {L : Type uL}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) (a : L) (b : vK.Completion) :
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    completionTensorAbsoluteValueCoordinateHom vK hvK w (a ⊗ₜ[K] b) =
      AbsoluteValue.toCompletionAlgHom (K := K) w.1 a *
        algebraMap vK.Completion w.1.Completion b := by
  classical
  let := Algebra.TensorProduct.rightAlgebra
    (R := K) (A := L) (B := vK.Completion)
  let : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u ↦ AbsoluteValue.completionAlgebra vK u.1 u.2
  exact completionTensorDecomposition_tmul_apply
    (K := K) (L := L) vK hvK a b w

/-- Every maximal tensor component is a canonical absolute-value completion
coordinate.  The chosen extension is produced from the finite-product prime
spectrum, and the coordinate prime is zero because its ring is a field. -/
theorem exists_completionTensorAbsoluteValueCoordinate_ker_eq
    {K : Type uK} {L : Type uL}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (m : Ideal (L ⊗[K] vK.Completion)) [m.IsMaximal] :
    ∃ w : AbsoluteValueExtension vK L,
      RingHom.ker (completionTensorAbsoluteValueCoordinateHom vK hvK w) = m := by
  classical
  let := completionTensorDecomposition_extensionFintype
    (K := K) (L := L) vK hvK
  let := Algebra.TensorProduct.rightAlgebra
    (R := K) (A := L) (B := vK.Completion)
  let : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u ↦ AbsoluteValue.completionAlgebra vK u.1 u.2
  let e := completionTensorDecomposition
    (K := K) (L := L) vK hvK
  let m' := m.map e.toRingEquiv.toRingHom
  have hm'max : m'.IsMaximal :=
    (inferInstance : m.IsMaximal).map_bijective
      e.toRingEquiv.toRingHom e.bijective
  have hm' : m'.IsPrime := hm'max.isPrime
  let p' : PrimeSpectrum
      (∀ u : AbsoluteValueExtension vK L, u.1.Completion) :=
    ⟨m', hm'⟩
  obtain ⟨w, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p'
  have hqbot : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime q.asIdeal
  have hkerEval :
      RingHom.ker
          (Pi.evalRingHom
            (fun u : AbsoluteValueExtension vK L ↦ u.1.Completion) w) =
        m' := by
    change (⊥ : Ideal w.1.Completion).comap
      (Pi.evalRingHom
        (fun u : AbsoluteValueExtension vK L ↦ u.1.Completion) w) = m'
    rw [← hqbot]
    exact congr_arg PrimeSpectrum.asIdeal hq
  refine ⟨w, ?_⟩
  rw [completionTensorAbsoluteValueCoordinateHom, ← RingHom.comap_ker,
    hkerEval]
  exact Ideal.comap_map_of_bijective e.toRingEquiv.toRingHom e.bijective

end EtaleFundamentalGroups

end
