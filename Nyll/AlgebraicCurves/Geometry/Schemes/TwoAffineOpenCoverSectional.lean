/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoAffineOpenCoverSectional.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechLaurentChart

/-!
# Two Affine Open Cover Sectional
-/

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

open CategoryTheory CategoryTheory.Limits Opposite

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of
  R))

/-- A family of pairwise disjoint sections of `c` contained in the first affine open whose
images form the complement of the second affine open. -/
structure IsSectional {ι : Type v} (σ : ι → (Spec (.of R) ⟶ X)) : Prop where
  /-- Each `σ i` is a section of `c`. -/
  comp_eq : ∀ i, σ i ≫ c = 𝟙 _
  /-- The image of each section lies in the first affine open. -/
  range_subset : ∀ i, Set.range (σ i).base ⊆ (𝒱.U0 : Set X)
  /-- The section images cover exactly the complement of the second affine open. -/
  compl_eq_iUnion : (𝒱.U1 : Set X)ᶜ = ⋃ i, Set.range (σ i).base
  /-- The images of distinct sections are disjoint. -/
  pairwise_disjoint : Pairwise fun i j => Disjoint (Set.range (σ i).base) (Set.range (σ j).base)

variable {𝒱 c}

/-- The algebra homomorphism from `A0` to `R` obtained by evaluating a section whose image lies
in the first affine open. -/
def sectionAlgHom (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ c = 𝟙 _) (hU : Set.range σ.base ⊆ (𝒱.U0 : Set
  X)) :
    (𝒱.cover c).A0 →ₐ[R] R :=
  letI := algebraOfHom c 𝒱.U0
  { (σ.appLE 𝒱.U0 ⊤ (fun x _ => hU ⟨x, rfl⟩) ≫ (Scheme.ΓSpecIso (.of R)).hom).hom with
    commutes' := fun r => by
      have hcTop : 𝒱.U0 ≤ c ⁻¹ᵁ (⊤ : (Spec (.of R)).Opens) := by
        rw [Scheme.Hom.preimage_top]
        exact le_top
      have hσTop : (⊤ : (Spec (.of R)).Opens) ≤ σ ⁻¹ᵁ 𝒱.U0 := by
        intro y _hy
        exact hU ⟨y, rfl⟩
      change ((Scheme.ΓSpecIso (.of R)).inv ≫ (c.appLE ⊤ 𝒱.U0 hcTop ≫ σ.appLE 𝒱.U0 ⊤ hσTop) ≫
        (Scheme.ΓSpecIso (.of R)).hom).hom r = r
      rw [Scheme.Hom.appLE_comp_appLE]
      suffices key : ∀ (φ : Spec (.of R) ⟶ Spec (.of R)), φ = 𝟙 _ → ∀ (e : (⊤ : (Spec (.of
        R)).Opens) ≤ φ ⁻¹ᵁ ⊤),
          (Scheme.ΓSpecIso (.of R)).inv ≫ φ.appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso (.of R)).hom = 𝟙 _ by
        rw [key _ hσ]; rfl
      rintro φ rfl e
      have hid : (𝟙 (Spec (.of R)) : Spec (.of R) ⟶ Spec (.of R)).appLE ⊤ ⊤ e = 𝟙 _ := by
        change (𝟙 (Spec (.of R)) : Spec (.of R) ⟶ Spec (.of R)).app ⊤ ≫ (Spec (.of R)).presheaf.map
          _ = _
        rw [Scheme.Hom.id_app]
        erw [Category.id_comp]
        exact (congrArg (Spec (.of R)).presheaf.map (Subsingleton.elim _ _)).trans ((Spec (.of
          R)).presheaf.map_id _)
      rw [hid, Category.id_comp, Iso.inv_hom_id] }

/-- The residue map associated with the `i`th Laurent chart of the cover. -/
abbrev sectionResidue {ι : Type v} (Λ : ι → (𝒱.cover c).LaurentChart) (i : ι) :
    Ω[(𝒱.cover c).A01⁄R] →ₗ[R] R :=
  (Λ i).residue

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
