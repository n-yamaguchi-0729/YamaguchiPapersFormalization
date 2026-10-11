/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.InjectiveModuleLocalization
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Flat.Localization

/-!
# The two-term principal localization complex

The complex has a coefficient module in degree zero, its localization in
degree one, and zero in higher degrees. Its positive cohomology vanishes
on injective modules over Noetherian rings, and its terms preserve flatness.
-/

noncomputable section

open CategoryTheory Limits

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R]

private def principalLocalizationTerm (x : R) (M : ModuleCat.{u} R) :
    ℕ → ModuleCat.{u} R
  | 0 => M
  | 1 => ModuleCat.of R (LocalizedModule (Submonoid.powers x) M)
  | _ + 2 => ModuleCat.of R PUnit

private def principalLocalizationDifferential (x : R) (M : ModuleCat.{u} R) :
    ∀ n, principalLocalizationTerm x M n ⟶ principalLocalizationTerm x M (n + 1)
  | 0 => ModuleCat.ofHom (LocalizedModule.mkLinearMap (Submonoid.powers x) M)
  | _ + 1 => 0

/-- The augmented principal Čech complex `M → M[1/x]`, in degrees zero
and one. -/
def principalLocalizationComplex (x : R) (M : ModuleCat.{u} R) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (principalLocalizationTerm x M)
    (principalLocalizationDifferential x M) (by
      intro n
      cases n with
      | zero => exact comp_zero
      | succ n => exact zero_comp)

/-- No terms of a principal localization complex occur above degree one. -/
theorem principalLocalizationComplex_isZero_X (x : R) (M : ModuleCat.{u} R)
    (n : ℕ) (hn : 1 < n) :
    IsZero ((principalLocalizationComplex x M).X n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  change IsZero (ModuleCat.of R PUnit)
  exact ModuleCat.isZero_of_subsingleton _

/-- The degree-zero cycles are exactly the elements annihilated by some
power of the principal ideal. -/
theorem principalLocalizationComplex_ker_d_zero (x : R) (M : ModuleCat.{u} R) :
    LinearMap.ker ((principalLocalizationComplex x M).d 0 1).hom =
      Ideal.primaryComponent M (Ideal.span {x}) := by
  change LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers x) M) = _
  exact ker_localizedModule_mkLinearMap_powers M x

/-- A principal localization complex of an injective module is exact in
all strictly positive degrees. -/
theorem principalLocalizationComplex_exactAt_succ
    [IsNoetherianRing R] (x : R) (M : ModuleCat.{u} R) [Module.Injective R M]
    (n : ℕ) : (principalLocalizationComplex x M).ExactAt (n + 1) := by
  cases n with
  | zero =>
    apply (HomologicalComplex.exactAt_iff' _ 0 1 2
      ((ComplexShape.up ℕ).prev_eq' rfl) ((ComplexShape.up ℕ).next_eq' rfl)).mpr
    rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
    intro y _hy
    obtain ⟨z, hz⟩ :=
      localizedModule_mkLinearMap_surjective_of_injective M (Submonoid.powers x) y
    exact ⟨z, hz⟩
  | succ n =>
    apply HomologicalComplex.ExactAt.of_isZero
    exact principalLocalizationComplex_isZero_X x M (n + 1 + 1) (by omega)

/-- Every term of the principal localization complex of a flat module is
flat over the original ring. -/
theorem principalLocalizationComplex_flat_X (x : R) (M : ModuleCat.{u} R)
    [Module.Flat R M] (n : ℕ) :
    Module.Flat R ((principalLocalizationComplex x M).X n) := by
  cases n with
  | zero => exact inferInstanceAs (Module.Flat R M)
  | succ n =>
    cases n with
    | zero =>
      exact Module.Flat.trans R (Localization (Submonoid.powers x))
        (LocalizedModule (Submonoid.powers x) M)
    | succ n =>
      change Module.Flat R PUnit
      infer_instance

end EtaleFundamentalGroups.Purity
