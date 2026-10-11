/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyLegacyComparison
import EtaleFundamentalGroups.Purity.LocalCohomologyRegularSequence
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Low-degree local cohomology for punctured hypersurfaces

The derived-to-legacy comparison transports the regular-sequence vanishing
supplied by Rees' theorem to derived local cohomology.  In particular, a
regular pair in the maximal ideal kills degree-one derived local cohomology.
This is the low-degree source available for a connectedness argument around a
principal hypersurface.
-/

noncomputable section

open CategoryTheory Limits IsLocalRing
open RingTheory.Sequence

namespace EtaleFundamentalGroups

universe u

/-- Positive-degree legacy local-cohomology vanishing transports to the
derived-Ext colimit through the natural comparison. -/
theorem derivedLocalCohomology_isZero_of_legacy_succ
    {R : Type u} [CommRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ)
    (h : IsZero ((localCohomology I (n + 1)).obj M)) :
    IsZero (derivedLocalCohomology I M (n + 1)) := by
  have hForget :
      IsZero
        ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
          ((localCohomology I (n + 1)).obj M)) :=
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map_isZero h
  exact hForget.of_iso
    (forgottenLegacyLocalCohomologyIsoDerivedSucc I M n).symm

/-- A regular sequence in the support ideal kills positive-degree derived
local cohomology below the length of the sequence. -/
theorem derivedLocalCohomology_isZero_of_isRegular_succ
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (rs : List R) (mem : ∀ r ∈ rs, r ∈ I) (reg : IsRegular M rs)
    (n : ℕ) (hn : n + 1 < rs.length) :
    IsZero (derivedLocalCohomology I M (n + 1)) := by
  apply derivedLocalCohomology_isZero_of_legacy_succ I M n
  exact localCohomology_isZero_of_isRegular
    I M smul_lt rs mem reg (n + 1) hn

/-- A regular pair in the maximal ideal kills degree-one derived local
cohomology of the structure module. -/
theorem derivedLocalCohomology_maximalIdeal_one_isZero_of_isRegular_pair
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x y : R) (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R)
    (hreg : IsRegular R [x, y]) :
    IsZero
      (derivedLocalCohomology (maximalIdeal R)
        (ModuleCat.of R R) 1) := by
  have hsmul :
      maximalIdeal R •
          (⊤ : Submodule R (ModuleCat.of R R)) < ⊤ := by
    have hne :
        maximalIdeal R •
            (⊤ : Submodule R (ModuleCat.of R R)) ≠ ⊤ :=
      Module.FaithfullyFlat.submodule_ne_top
        (maximalIdeal.isMaximal R)
    exact hne.lt_top
  apply derivedLocalCohomology_isZero_of_isRegular_succ
    (maximalIdeal R) (ModuleCat.of R R) hsmul [x, y] (n := 0)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hx
    · exact hy
  · exact hreg
  · norm_num

end EtaleFundamentalGroups

end
