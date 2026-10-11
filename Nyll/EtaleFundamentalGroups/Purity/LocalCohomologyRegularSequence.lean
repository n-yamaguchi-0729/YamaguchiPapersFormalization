/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Depth.Rees
import Nyll.EtaleFundamentalGroups.Purity.DerivedExtLegacyComparison
import Nyll.EtaleFundamentalGroups.Purity.LocalCohomologyExtVanishing

/-!
# Local-cohomology vanishing from regular sequences

A regular sequence in an ideal annihilates the low positive-degree Ext groups by
the Rees theorem.  Combining that result with the comparison between the two Ext
implementations gives the corresponding local-cohomology vanishing.
-/

noncomputable section

open CategoryTheory Limits Opposite
open RingTheory.Sequence

namespace EtaleFundamentalGroups

universe u

/-- If an ideal contains a regular sequence of length greater than `i`, then
local cohomology in degree `i` vanishes. -/
theorem localCohomology_isZero_of_isRegular
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (rs : List R) (mem : ∀ r ∈ rs, r ∈ I) (reg : IsRegular M rs)
    (i : ℕ) (hi : i < rs.length) :
    IsZero ((localCohomology I i).obj M) := by
  apply localCohomology_isZero_of_subsingleton_ext_powers
  intro n
  let N : ModuleCat.{u} R := ModuleCat.of R (R ⧸ I ^ n)
  have hSupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus I := by
    change Module.support R (R ⧸ I ^ n) ⊆ PrimeSpectrum.zeroLocus I
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    rcases n with _ | n
    · simp
    · simp
  have hDerived :
      Subsingleton (CategoryTheory.Abelian.Ext.{u} N M i) :=
    ModuleCat.subsingleton_ext_of_exists_isRegular I N hSupp M smul_lt rs mem reg
      i hi
  exact ModuleCat.subsingleton_of_isZero
    (legacyExt_isZero_of_subsingleton_derivedExt N M i hDerived)

end EtaleFundamentalGroups

end
