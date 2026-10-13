/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Regular.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Finite sums of effective Cartier divisors

On a common affine neighbourhood, flat restriction preserves the regularity
of each local defining equation. Their product is again a non-zero-divisor
and generates the product ideal sheaf. This constructs the effective Cartier
property for arbitrary finite products, including the empty divisor.
-/

open CategoryTheory
open scoped BigOperators

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}}

private theorem isRegular_restrict {U V : X.affineOpens} (hVU : V ≤ U)
    (a : Γ(X, U.1)) (ha : IsRegular a) :
    IsRegular ((X.presheaf.map (homOfLE (X := X.Opens) hVU).op).hom a) := by
  let f : Γ(X, U.1) →+* Γ(X, V.1) :=
    (X.presheaf.map (homOfLE (X := X.Opens) hVU).op).hom
  let : Algebra Γ(X, U.1) Γ(X, V.1) := f.toAlgebra
  have hflat : f.Flat := by
    have h := Scheme.Hom.flat_appLE (𝟙 X) U.2 V.2 hVU
    change f.Flat at h
    exact h
  have : Module.Flat Γ(X, U.1) Γ(X, V.1) := hflat
  have hregular := IsSMulRegular.of_flat (S := Γ(X, V.1)) ha.left
  change IsSMulRegular Γ(X, V.1) (f a) at hregular
  exact (Commute.isRegular_iff (Commute.all (f a))).mpr hregular

/-- Multiplying two effective Cartier ideals at a point gives an effective
Cartier ideal there, with the product of the restricted defining equations. -/
theorem IsEffectiveCartierAt.mul {I J : X.IdealSheafData} {x : X}
    (hI : I.IsEffectiveCartierAt x) (hJ : J.IsEffectiveCartierAt x) :
    (I * J).IsEffectiveCartierAt x := by
  obtain ⟨U, hxU, a, ha, hIa⟩ := hI
  obtain ⟨V, hxV, b, hb, hJb⟩ := hJ
  obtain ⟨W, hW, hxW, hWUV⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := U.1 ⊓ V.1) (x := x) ⟨hxU, hxV⟩
  let T : X.affineOpens := ⟨W, hW⟩
  have hTU : T ≤ U := hWUV.trans inf_le_left
  have hTV : T ≤ V := hWUV.trans inf_le_right
  let f : Γ(X, U.1) →+* Γ(X, T.1) := (X.presheaf.map (homOfLE (X := X.Opens) hTU).op).hom
  let g : Γ(X, V.1) →+* Γ(X, T.1) := (X.presheaf.map (homOfLE (X := X.Opens) hTV).op).hom
  refine ⟨T, hxW, f a * g b,
    (isRegular_restrict hTU a ha).mul (isRegular_restrict hTV b hb), ?_⟩
  have hI' : I.ideal T = Ideal.span {f a} := by
    rw [← I.map_ideal hTU, hIa, Ideal.map_span, Set.image_singleton]
    rfl
  have hJ' : J.ideal T = Ideal.span {g b} := by
    rw [← J.map_ideal hTV, hJb, Ideal.map_span, Set.image_singleton]
    rfl
  change I.ideal T * J.ideal T = Ideal.span {f a * g b}
  rw [hI', hJ', Ideal.span_singleton_mul_span_singleton]

/-- The product ideal represents the sum of two effective Cartier divisors. -/
theorem IsEffectiveCartier.mul {I J : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier) :
    (I * J).IsEffectiveCartier :=
  fun x => (hI x).mul (hJ x)

/-- Finite products of effective Cartier ideal sheaves are effective Cartier. -/
theorem isEffectiveCartier_finset_prod {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) (hI : ∀ i ∈ s, (I i).IsEffectiveCartier) :
    (∏ i ∈ s, I i).IsEffectiveCartier := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty]
      exact isEffectiveCartier_top
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hI i (Finset.mem_insert_self i s)).mul
        (ih (fun j hj => hI j (Finset.mem_insert_of_mem hj)))

end AlgebraicGeometry.Scheme.IdealSheafData
