/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOver_baseChange_baseChange_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.BaseChange
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver

/-!
# Relative Group Law exists scheme Hom Over base Change base Change iso
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_exists_schemeHomOver_baseChange_baseChange_iso

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem _root_.GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOver_baseChange_baseChange_iso
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] {R'' : Type u} [CommRing R'']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    (j : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R'))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    ∃ (u : SchemeHomOver (RelativeGroupLaw.baseChangeStr j (RelativeGroupLaw.baseChangeStr ι f))
          (RelativeGroupLaw.baseChangeStr (j ≫ ι) f))
      (v : SchemeHomOver (RelativeGroupLaw.baseChangeStr (j ≫ ι) f)
          (RelativeGroupLaw.baseChangeStr j (RelativeGroupLaw.baseChangeStr ι f))),
      u.1 ≫ v.1 = 𝟙 _ ∧ v.1 ≫ u.1 = 𝟙 _ ∧
      u.1 ≫ pullback.fst f (j ≫ ι) = pullback.fst (pullback.snd f ι) j ≫ pullback.fst f ι ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R''))
        (x y : SchemeHomOver t (RelativeGroupLaw.baseChangeStr j (RelativeGroupLaw.baseChangeStr ι
          f))),
        NeronModelInfra.schemeHomOverComp (((G.baseChange ι).baseChange j).mul t x y) u =
          (G.baseChange (j ≫ ι)).mul t (NeronModelInfra.schemeHomOverComp x u)
            (NeronModelInfra.schemeHomOverComp y u) := by
  classical
  let e := pullbackLeftPullbackSndIso f ι j
  have he_snd : e.hom ≫ pullback.snd f (j ≫ ι) = pullback.snd (pullback.snd f ι) j :=
    pullbackLeftPullbackSndIso_hom_snd f ι j
  have he_fst : e.hom ≫ pullback.fst f (j ≫ ι) = pullback.fst (pullback.snd f ι) j ≫ pullback.fst f
    ι :=
    pullbackLeftPullbackSndIso_hom_fst f ι j
  have hv_snd : e.inv ≫ pullback.snd (pullback.snd f ι) j = pullback.snd f (j ≫ ι) := by
    rw [← he_snd, Iso.inv_hom_id_assoc]
  let u : SchemeHomOver (RelativeGroupLaw.baseChangeStr j (RelativeGroupLaw.baseChangeStr ι f))
      (RelativeGroupLaw.baseChangeStr (j ≫ ι) f) := ⟨e.hom, he_snd⟩
  let v : SchemeHomOver (RelativeGroupLaw.baseChangeStr (j ≫ ι) f)
      (RelativeGroupLaw.baseChangeStr j (RelativeGroupLaw.baseChangeStr ι f)) := ⟨e.inv, hv_snd⟩
  have mul_val_congr : ∀ {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
      (X Y : SchemeHomOver t₁ f) (X' Y' : SchemeHomOver t₂ f), X.1 = X'.1 → Y.1 = Y'.1 →
      (G.mul t₁ X Y).1 = (G.mul t₂ X' Y').1 := by
    intro T t₁ t₂ h X Y X' Y' hX hY
    subst h
    rw [show X = X' from Subtype.ext hX, show Y = Y' from Subtype.ext hY]
  refine ⟨u, v, e.hom_inv_id, e.inv_hom_id, he_fst, ?_⟩
  intro T t x y
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
    change (((G.baseChange ι).baseChange j).mul t x y).1 ≫ e.hom ≫ pullback.fst f (j ≫ ι) = _
    rw [he_fst, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, ←
      Category.assoc,
      pullback.lift_fst, RelativeGroupLaw.baseChange_mul,
        RelativeGroupLaw.baseChangePointOfBase_coe,
      pullback.lift_fst]
    rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe,
      pullback.lift_fst]
    apply mul_val_congr (Category.assoc t j ι)
    · rw [RelativeGroupLaw.baseChangePointToBase_coe, RelativeGroupLaw.baseChangePointToBase_coe,
        RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe,
          Category.assoc,
        Category.assoc, he_fst]
    · rw [RelativeGroupLaw.baseChangePointToBase_coe, RelativeGroupLaw.baseChangePointToBase_coe,
        RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe,
          Category.assoc,
        Category.assoc, he_fst]
  · have h1 := (NeronModelInfra.schemeHomOverComp (((G.baseChange ι).baseChange j).mul t x y) u).2
    have h2 := ((G.baseChange (j ≫ ι)).mul t (NeronModelInfra.schemeHomOverComp x u)
      (NeronModelInfra.schemeHomOverComp y u)).2
    exact h1.trans h2.symm
end RelativeGroupLaw_exists_schemeHomOver_baseChange_baseChange_iso
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation
