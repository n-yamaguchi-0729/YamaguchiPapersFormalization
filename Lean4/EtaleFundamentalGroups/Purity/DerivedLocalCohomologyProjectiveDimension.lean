/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.DerivedLocalCohomology
import EtaleFundamentalGroups.Purity.LocalCohomologyProjectiveDimension

/-!
# Projective-dimension vanishing for derived local cohomology

Uniform projective-dimension bounds make every object of the derived Ext
ideal-powers diagram trivial.  This gives the derived-colimit counterpart of
the existing vanishing results for Mathlib's legacy local-cohomology object.
-/

noncomputable section

open CategoryTheory Limits
open scoped Pointwise

namespace EtaleFundamentalGroups

universe u

/-- A uniform projective-dimension bound on the ideal-power quotients forces
the corresponding derived local-cohomology colimit to vanish. -/
theorem derivedLocalCohomology_isZero_of_quotientPowers_hasProjectiveDimensionLT
    {R : Type u} [CommRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) (d i : ℕ) (hdi : d ≤ i)
    (hpd : ∀ n : ℕ,
      HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ I ^ n)) d) :
    IsZero (derivedLocalCohomology I M i) := by
  apply derivedLocalCohomology_isZero_of_subsingleton_ext_powers
  intro n
  let N : ModuleCat.{u} R := ModuleCat.of R (R ⧸ I ^ n)
  let : HasProjectiveDimensionLT N d := hpd n
  exact HasProjectiveDimensionLT.subsingleton N d i hdi M

/-- Derived local cohomology supported on a principal regular ideal vanishes
in every degree at least two. -/
theorem derivedLocalCohomology_span_singleton_isZero_of_isSMulRegular
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (hxreg : IsSMulRegular R x)
    (hxmem : x ∈ IsLocalRing.maximalIdeal R)
    (M : ModuleCat.{u} R) (i : ℕ) (hi : 2 ≤ i) :
    IsZero (derivedLocalCohomology (Ideal.span {x}) M i) := by
  apply derivedLocalCohomology_isZero_of_quotientPowers_hasProjectiveDimensionLT
    (Ideal.span {x}) M 2 i hi
  intro n
  rcases n with _ | n
  · rw [pow_zero, Ideal.one_eq_top]
    let N : ModuleCat.{u} R := ModuleCat.of R (R ⧸ (⊤ : Ideal R))
    have hN : IsZero N := ModuleCat.isZero_of_subsingleton N
    let : HasProjectiveDimensionLT N 0 :=
      hN.hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge N 0 2 (by omega)
  · rw [Ideal.span_singleton_pow]
    exact quotient_span_singleton_hasProjectiveDimensionLT_two
      (x ^ (n + 1)) (hxreg.pow (n + 1))
      ((IsLocalRing.maximalIdeal R).pow_mem_of_mem hxmem
        (n + 1) (Nat.succ_pos n))

end EtaleFundamentalGroups

end
