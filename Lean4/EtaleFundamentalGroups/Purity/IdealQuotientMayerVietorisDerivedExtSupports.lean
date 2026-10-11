/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.DerivedLocalCohomologySimultaneousPowers
import EtaleFundamentalGroups.Purity.IdealQuotientMayerVietorisDerivedExtColimit

/-!
# Support terms in the derived local-cohomology Mayer--Vietoris sequence

The third term in degree `n₀` of the finite derived-Ext sequence is the
simultaneous-intersection support, and the following term in degree `n₁` is
the simultaneous-supremum support.  Cofinality identifies their filtered
colimits with derived local cohomology at `I ⊓ J` and `I ⊔ J`.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The index-two term of the derived-Ext powers diagram is the derived
local-cohomology diagram along simultaneous intersections. -/
def idealQuotientMayerVietorisDerivedExtPowersInfTermIso
    (I J : Ideal R) (M : ModuleCat.{u} R)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    (idealQuotientMayerVietorisDerivedExtPowersDiagram
        I J M n₀ n₁ h ⋙
      (evaluation (Fin 6) AddCommGrpCat.{u}).obj ⟨2, by omega⟩) ≅
      derivedLocalCohomologyDiagram (idealInfPowersDiagram I J) M n₀ :=
  Iso.refl _

/-- The index-three term of the derived-Ext powers diagram is the derived
local-cohomology diagram along simultaneous suprema. -/
def idealQuotientMayerVietorisDerivedExtPowersSupTermIso
    (I J : Ideal R) (M : ModuleCat.{u} R)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    (idealQuotientMayerVietorisDerivedExtPowersDiagram
        I J M n₀ n₁ h ⋙
      (evaluation (Fin 6) AddCommGrpCat.{u}).obj ⟨3, by omega⟩) ≅
      derivedLocalCohomologyDiagram (idealSupPowersDiagram I J) M n₁ :=
  Iso.refl _

/-- The colimit of the index-two term is local cohomology supported on the
intersection. -/
def idealQuotientMayerVietorisDerivedExtPowersInfColimitIso
    (I J : Ideal R) (M : ModuleCat.{u} R)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    colimit (idealQuotientMayerVietorisDerivedExtPowersDiagram
        I J M n₀ n₁ h ⋙
      (evaluation (Fin 6) AddCommGrpCat.{u}).obj ⟨2, by omega⟩) ≅
      derivedLocalCohomology (I ⊓ J) M n₀ :=
  HasColimit.isoOfNatIso
      (idealQuotientMayerVietorisDerivedExtPowersInfTermIso
        I J M n₀ n₁ h) ≪≫
    derivedLocalCohomologyOfInfPowersIso I J M n₀

/-- The colimit of the index-three term is local cohomology supported on the
supremum. -/
def idealQuotientMayerVietorisDerivedExtPowersSupColimitIso
    (I J : Ideal R) (M : ModuleCat.{u} R)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    colimit (idealQuotientMayerVietorisDerivedExtPowersDiagram
        I J M n₀ n₁ h ⋙
      (evaluation (Fin 6) AddCommGrpCat.{u}).obj ⟨3, by omega⟩) ≅
      derivedLocalCohomology (I ⊔ J) M n₁ :=
  HasColimit.isoOfNatIso
      (idealQuotientMayerVietorisDerivedExtPowersSupTermIso
        I J M n₀ n₁ h) ≪≫
    derivedLocalCohomologyOfSupPowersIso I J M n₁

end EtaleFundamentalGroups

end
