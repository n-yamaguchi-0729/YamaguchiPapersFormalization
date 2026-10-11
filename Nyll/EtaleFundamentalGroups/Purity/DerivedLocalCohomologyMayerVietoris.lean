/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.IdealQuotientMayerVietorisDerivedExtMiddle

/-!
# Mayer--Vietoris vanishing for derived local cohomology

The exact filtered-colimit window in positions two, three, and four of the
ideal-quotient derived-Ext sequence has support terms `I ⊓ J`, `I ⊔ J`, and
the biproduct of the `I`- and `J`-support terms.  Thus vanishing of the two
outer objects forces vanishing for the supremum support.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The local-cohomology Mayer--Vietoris vanishing implication obtained from
the exact filtered colimit of the derived-Ext powers sequences. -/
theorem derivedLocalCohomology_sup_isZero_of_mayerVietoris
    (I J : Ideal R) (M : ModuleCat.{u} R)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁)
    (hInf : IsZero (derivedLocalCohomology (I ⊓ J) M n₀))
    (hI : IsZero (derivedLocalCohomology I M n₁))
    (hJ : IsZero (derivedLocalCohomology J M n₁)) :
    IsZero (derivedLocalCohomology (I ⊔ J) M n₁) := by
  let S :=
    idealQuotientMayerVietorisDerivedExtPowersAdjacentColimitShortComplex
      I J M n₀ n₁ h 2 (by omega)
  have hS : S.Exact :=
    idealQuotientMayerVietorisDerivedExtPowersAdjacentColimitShortComplex_exact
      I J M n₀ n₁ h 2 (by omega)
  have hX₁ : IsZero S.X₁ := by
    change IsZero
      (colimit
        (idealQuotientMayerVietorisDerivedExtPowersDiagram
            I J M n₀ n₁ h ⋙
          (evaluation (Fin 6) AddCommGrpCat.{u}).obj ⟨2, by omega⟩))
    exact hInf.of_iso
      (idealQuotientMayerVietorisDerivedExtPowersInfColimitIso
        I J M n₀ n₁ h)
  have hX₃ : IsZero S.X₃ := by
    change IsZero
      (colimit
        (idealQuotientMayerVietorisDerivedExtPowersDiagram
            I J M n₀ n₁ h ⋙
          (evaluation (Fin 6) AddCommGrpCat.{u}).obj ⟨4, by omega⟩))
    exact
      idealQuotientMayerVietorisDerivedExtPowersMiddleColimit_isZero
        I J M n₀ n₁ h hI hJ
  have hX₂ : IsZero S.X₂ := hS.isZero_of_both_isZero hX₁ hX₃
  exact
    (idealQuotientMayerVietorisDerivedExtPowersSupColimitIso
      I J M n₀ n₁ h).isZero_iff.mp hX₂

end EtaleFundamentalGroups

end
