/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.CurveCover
import Nyll.JacobianVarieties.Kummer.DivisorClasses
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_root_fromNormalization_kummer_existsUnique_lift
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.SchemeTheory.LocalGeometry.SmoothStalkNormality
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Splitting of the actual Kummer cover

An actual root of a Kummer function constructs a section of its normalized
finite etale cover. Use a single open set with local denominator equal to that
root: the normalized equation is then the unit equation, so the existing local
root universal property constructs the section on the original curve.

Over algebraically closed constants, the actual divisorial Kummer comparison
therefore identifies vanishing of the torsion divisor class with existence of
a section of the actual cover. The integer must be invertible in the base
field; the statement includes positive characteristic only away from it.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]

/-- An actual root supplies a section of the actual normalized Kummer cover. -/
theorem exists_section_kummerCover_of_pow (M : CurveModel K F) (n : ℕ+)
    (hn : IsUnit ((n : ℕ) : K)) (u : Pic0.kummerUnits K F n)
    (w : F) (hw : w ^ (n : ℕ) = (u.val : F)) :
    ∃ s : M.C ⟶ (M.kummerCover n hn u).left,
      s ≫ (M.kummerCover n hn u).hom = 𝟙 M.C := by
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  let g : M.C.functionField := M.ffEquiv (u.val : F)
  let h : M.C.functionField := M.ffEquiv w
  have hg : g ≠ 0 := (map_ne_zero M.ffEquiv).mpr (Units.ne_zero u.val)
  have hpow : h ^ (n : ℕ) = g := by
    change (M.ffEquiv w) ^ (n : ℕ) = M.ffEquiv (u.val : F)
    rw [← map_pow, hw]
  have hh : h ≠ 0 := by
    intro hz
    rw [hz, zero_pow n.ne_zero] at hpow
    exact hg hpow.symm
  have hleft : g / h ^ (n : ℕ) = 1 := by rw [hpow, div_self hg]
  have hright : h ^ (n : ℕ) / g = 1 := by rw [hpow, div_self hg]
  obtain ⟨v, T, hv, -, -, -, hlift⟩ :=
    exists_root_fromNormalization_kummer_existsUnique_lift M.toBase
      (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase x).2)
      (n : ℕ) hn g hg 1 (fun _ : Fin 1 => ⊤) (by rw [iSup_const])
      (fun _ : Fin 1 => h) (fun _ => hh) (fun _ x _ => by
        rw [hleft, hright]
        exact ⟨⟨1, map_one (algebraMap (M.C.presheaf.stalk x) M.C.functionField)⟩,
          ⟨1, map_one (algebraMap (M.C.presheaf.stalk x) M.C.functionField)⟩⟩)
  have hvone : v 0 = 1 := by
    apply TopCat.Presheaf.section_ext M.C.sheaf ⊤
    intro x hx
    apply IsFractionRing.injective (M.C.presheaf.stalk x) M.C.functionField
    change algebraMap (M.C.presheaf.stalk x) M.C.functionField
        (M.C.presheaf.germ ⊤ x hx (v 0)) =
      algebraMap (M.C.presheaf.stalk x) M.C.functionField
        (M.C.presheaf.germ ⊤ x hx 1)
    rw [hv 0 x hx, hleft, map_one, map_one]
  obtain ⟨s, hs, -⟩ := hlift 0 M.C (𝟙 M.C) (Scheme.Hom.preimage_top (𝟙 M.C)) 1 (by
    rw [map_one, one_pow, hvone, map_one])
  exact ⟨s, hs.1⟩

/-- A Kummer cover of a curve over algebraically closed constants has a section
exactly when the actual divided principal-divisor class vanishes. -/
theorem kummerClass_eq_one_iff_exists_section [IsAlgClosed K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (M : CurveModel K F) (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    (u : Pic0.kummerUnits K F n) :
    Pic0.kummerClass n u = 1 ↔
      ∃ s : M.C ⟶ (M.kummerCover n hn u).left,
        s ≫ (M.kummerCover n hn u).hom = 𝟙 M.C := by
  constructor
  · intro hu
    have hker : u ∈ (Pic0.kummerClass (K := K) (F := F) n).ker := hu
    rw [Pic0.kummerClass_ker] at hker
    obtain ⟨w, hw⟩ := hker
    exact M.exists_section_kummerCover_of_pow n hn u (w : F) (congrArg Units.val hw)
  · rintro ⟨s, hs⟩
    exact M.kummerClass_eq_one_of_section n hn u s hs

end AlgebraicCurve.CurveModel
