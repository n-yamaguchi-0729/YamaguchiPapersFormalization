/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.OpenCurveCoverCharacter
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenFunctionField
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_root_fromNormalization_kummer_existsUnique_lift
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_pow_eq_of_section_fromNormalization_kummer
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Splitting and the kernel of the actual open Kummer class

A section of the actual normalized cover is equivalent to an actual nth
power in the original function field. Consequently the kernel of the
derived H¹ class is exactly the previously defined subgroup of powers.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicCurve.CurveModel.OpenKummer

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
  (w : Pic0.openKummerUnits K F S n)
  {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hinterior : ∀ (y : X) (x : closedPoints M.C),
    x.val = j y → M.placeOfPoint x ∉ S)
  (hn : IsUnit ((n : ℕ) : K))

/-- An actual function-field root gives a section on the open curve. -/
theorem exists_section_of_pow (b : F) (hb : b ^ (n : ℕ) = (w.val : F)) :
    ∃ s : X ⟶ (M.openKummerCover S n hn w j hj hinterior).left,
      s ≫ (M.openKummerCover S n hn w j hj hinterior).hom = 𝟙 X := by
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : Smooth (j ≫ M.toBase) := inferInstance
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  let g : X.functionField := j.functionFieldMap hj (M.ffEquiv (w.val : F))
  let h : X.functionField := j.functionFieldMap hj (M.ffEquiv b)
  have hg : g ≠ 0 := (map_ne_zero (j.functionFieldMap hj)).mpr ((map_ne_zero M.ffEquiv).mpr
    (Units.ne_zero w.val))
  have hpow : h ^ (n : ℕ) = g := by
    change (j.functionFieldMap hj (M.ffEquiv b)) ^ (n : ℕ) = j.functionFieldMap hj (M.ffEquiv
      (w.val : F))
    rw [← map_pow, ← map_pow, hb]
  have hh : h ≠ 0 := by
    intro hz
    rw [hz, zero_pow n.ne_zero] at hpow
    exact hg hpow.symm
  have hleft : g / h ^ (n : ℕ) = 1 := by rw [hpow, div_self hg]
  have hright : h ^ (n : ℕ) / g = 1 := by rw [hpow, div_self hg]
  obtain ⟨v, T, hv, -, -, -, hlift⟩ :=
    exists_root_fromNormalization_kummer_existsUnique_lift (j ≫ M.toBase)
      (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk (j ≫ M.toBase) x).2)
      (n : ℕ) hn g hg 1 (fun _ : Fin 1 => ⊤) (by rw [iSup_const])
      (fun _ : Fin 1 => h) (fun _ => hh) (fun _ x _ => by
        rw [hleft, hright]
        exact ⟨⟨1, map_one (algebraMap (X.presheaf.stalk x) X.functionField)⟩,
          ⟨1, map_one (algebraMap (X.presheaf.stalk x) X.functionField)⟩⟩)
  have hvone : v 0 = 1 := by
    apply TopCat.Presheaf.section_ext X.sheaf ⊤
    intro x hx
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    change algebraMap (X.presheaf.stalk x) X.functionField
        (X.presheaf.germ ⊤ x hx (v 0)) =
      algebraMap (X.presheaf.stalk x) X.functionField
        (X.presheaf.germ ⊤ x hx 1)
    rw [hv 0 x hx, hleft, map_one, map_one]
  obtain ⟨s, hs, -⟩ := hlift 0 X (𝟙 X) (Scheme.Hom.preimage_top (𝟙 X)) 1 (by
    rw [map_one, one_pow, hvone, map_one])
  exact ⟨s, hs.1⟩


/-- A section forces a root in the original function field, using the
canonical function-field equivalence of the open immersion. -/
theorem exists_pow_of_section
    (s : X ⟶ (M.openKummerCover S n hn w j hj hinterior).left)
    (hs : s ≫ (M.openKummerCover S n hn w j hj hinterior).hom = 𝟙 X) :
    ∃ b : F, b ^ (n : ℕ) = (w.val : F) := by
  have hw : j.functionFieldMap hj (M.ffEquiv (w.val : F)) ≠ 0 :=
    (map_ne_zero (j.functionFieldMap hj)).mpr
      ((map_ne_zero M.ffEquiv).mpr (Units.ne_zero w.val))
  obtain ⟨b, hb⟩ := exists_pow_eq_of_section_fromNormalization_kummer
    (n : ℕ) (j.functionFieldMap hj (M.ffEquiv (w.val : F))) hw s hs
  let e : F ≃+* X.functionField :=
    M.ffEquiv.trans j.functionFieldRingEquivOfIsOpenImmersion
  refine ⟨e.symm b, e.injective ?_⟩
  rw [map_pow, e.apply_symm_apply]
  exact hb

/-- The actual covering section criterion is precisely the actual
power subgroup, with no Picard or cohomology comparison assumed. -/
theorem mem_openKummerPowers_iff_exists_section :
    w ∈ Pic0.openKummerPowers K F S n ↔
      ∃ s : X ⟶ (M.openKummerCover S n hn w j hj hinterior).left,
        s ≫ (M.openKummerCover S n hn w j hj hinterior).hom = 𝟙 X := by
  constructor
  · rintro ⟨b, hb⟩
    exact exists_section_of_pow M S n w j hj hinterior hn
      (b : F) (congrArg Units.val hb)
  · rintro ⟨s, hs⟩
    obtain ⟨b, hb⟩ := exists_pow_of_section M S n w j hj hinterior hn s hs
    have hb0 : b ≠ 0 := by
      intro hz
      rw [hz, zero_pow n.ne_zero] at hb
      exact Units.ne_zero w.val hb.symm
    change ∃ t : Fˣ, t ^ (n : ℕ) = w.val
    refine ⟨Units.mk0 b hb0, Units.ext ?_⟩
    exact hb

/-- The genuine derived H¹ class vanishes exactly on actual powers. -/
theorem kummerEtaleClass_eq_zero_iff_mem_powers
    [IsSepClosed K] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) :
    kummerEtaleClass M S n w j hj hinterior hn ξ = 0 ↔
      w ∈ Pic0.openKummerPowers K F S n :=
  (kummerEtaleClass_eq_zero_iff_exists_section M S n w j hj hinterior hn ξ).trans
    (mem_openKummerPowers_iff_exists_section M S n w j hj hinterior hn).symm

end AlgebraicCurve.CurveModel.OpenKummer
