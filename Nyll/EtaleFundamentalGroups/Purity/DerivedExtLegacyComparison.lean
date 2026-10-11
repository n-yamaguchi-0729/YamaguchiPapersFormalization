/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-!
# Comparison of the two Ext implementations used by local cohomology and depth

`localCohomology` is currently defined using the legacy derived-functor object
`_root_.Ext`, whereas the depth API uses `CategoryTheory.Abelian.Ext`.  This file
records the vanishing comparison needed to pass from the latter to the former.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u v

/-- Vanishing of degree-zero derived-category Ext forces vanishing of the
degree-zero legacy Ext object. -/
theorem legacyExt_isZero_of_subsingleton_derivedExt_zero
    {R : Type u} [CommRing R] [Small.{v} R]
    (X Y : ModuleCat.{v} R)
    (hExt : Subsingleton (CategoryTheory.Abelian.Ext.{v} X Y 0)) :
    IsZero (((_root_.Ext R (ModuleCat.{v} R) 0).obj (op X)).obj Y) := by
  let P := CategoryTheory.projectiveResolution X
  refine IsZero.of_iso ?_ (P.isoExt 0 Y)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [HomologicalComplex.exactAt_iff' _ 0 0 1 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro f hf
  change (P.complex.X 0 ⟶ Y) at f
  change P.complex.d 1 0 ≫ f = 0 at hf
  change ∃ g : P.complex.X 0 ⟶ Y, P.complex.d 0 0 ≫ g = f
  let c := CokernelCofork.ofπ f hf
  let g : X ⟶ Y := P.isColimitCokernelCofork.desc c
  have hfac : P.π.f 0 ≫ g = f := P.isColimitCokernelCofork.fac c WalkingParallelPair.one
  have hHom : Subsingleton (X ⟶ Y) :=
    CategoryTheory.Abelian.Ext.addEquiv₀.subsingleton_congr.mp hExt
  have hg : g = 0 := hHom.elim _ _
  refine ⟨0, ?_⟩
  rw [← hfac, hg]
  exact (Limits.comp_zero (f := P.π.f 0) (Z := Y)).symm

/-- Vanishing of positive-degree derived-category Ext forces vanishing of the
corresponding legacy Ext object.  Both sides are computed using the same
projective resolution. -/
theorem legacyExt_isZero_of_subsingleton_derivedExt_succ
    {R : Type u} [CommRing R] [Small.{v} R]
    (X Y : ModuleCat.{v} R) (n : ℕ)
    (hExt : Subsingleton (CategoryTheory.Abelian.Ext.{v} X Y (n + 1))) :
    IsZero (((_root_.Ext R (ModuleCat.{v} R) (n + 1)).obj (op X)).obj Y) := by
  let P := CategoryTheory.projectiveResolution X
  refine IsZero.of_iso ?_ (P.isoExt (n + 1) Y)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro f hf
  change (P.complex.X (n + 1) ⟶ Y) at f
  change P.complex.d (n + 2) (n + 1) ≫ f = 0 at hf
  change ∃ g : P.complex.X n ⟶ Y, P.complex.d (n + 1) n ≫ g = f
  have hz : P.extMk f (n + 2) (by omega) hf = 0 :=
    hExt.elim _ _
  rw [P.extMk_eq_zero_iff f (n + 2) (by omega) hf n (by omega)] at hz
  obtain ⟨g, hg⟩ := hz
  exact ⟨g, hg⟩

/-- Vanishing of derived-category Ext in any degree forces vanishing of the
corresponding legacy Ext object used by `localCohomology`. -/
theorem legacyExt_isZero_of_subsingleton_derivedExt
    {R : Type u} [CommRing R] [Small.{v} R]
    (X Y : ModuleCat.{v} R) (i : ℕ)
    (hExt : Subsingleton (CategoryTheory.Abelian.Ext.{v} X Y i)) :
    IsZero (((_root_.Ext R (ModuleCat.{v} R) i).obj (op X)).obj Y) := by
  cases i with
  | zero => exact legacyExt_isZero_of_subsingleton_derivedExt_zero X Y hExt
  | succ n => exact legacyExt_isZero_of_subsingleton_derivedExt_succ X Y n hExt

end EtaleFundamentalGroups

end
