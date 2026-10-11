/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Geometry.AbelianSchemes.AffineLineConstancy
import AlgebraicCurves.Geometry.Projective.ProjSpace_specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq
import SchemeTheory.ProjectiveSpace.BaseChange
import SchemeTheory.ProjectiveSpace.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Morphisms from the projective line to an abelian variety are constant

Each standard chart is the actual affine line. Their constant values agree
at the common rational point with homogeneous coordinates `(1,1)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry HomogeneousLocalization Polynomial
open AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace
  (awayChartEquiv awayChartEquiv_X)

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GoodReductionJacobian

namespace ProjectiveLineConstancy

variable (k : Type u) [Field k]

private abbrev otherUnique (i : Fin 2) : Unique {j : Fin 2 // j ≠ i} where
  default := ⟨⟨1 - i.val, by omega⟩, by
    intro h
    have h' := congrArg Fin.val h
    change 1 - i.val = i.val at h'
    have hi := i.isLt
    omega⟩
  uniq j := by
    apply Subtype.ext
    apply Fin.ext
    have hi := i.isLt
    have hj := j.val.isLt
    have hne : j.val.val ≠ i.val := fun h => j.property (Fin.ext h)
    change j.val.val = 1 - i.val
    omega

private def chartEquiv (i : Fin 2) :
    k[X] ≃ₐ[k] Away (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i) :=
  let _ : Unique {j : Fin 2 // j ≠ i} := otherUnique i
  (MvPolynomial.uniqueAlgEquiv k {j : Fin 2 // j ≠ i}).symm.trans
    (awayChartEquiv (S := k) 1 i)

private def ones (i : Fin 2) :
    Away (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i) →ₐ[k] k :=
  (MvPolynomial.aeval (fun _ : {j : Fin 2 // j ≠ i} => (1 : k))).comp
    (awayChartEquiv (S := k) 1 i).symm.toAlgHom

private lemma ones_ratio (i j : Fin 2) : ones k i (ProjSpace.ratio k 1 i j) = 1 := by
  by_cases h : j = i
  · rw [h, ProjSpace.ratio_self, map_one]
  · rw [← awayChartEquiv_X (S := k) 1 i ⟨j, h⟩]
    change MvPolynomial.aeval (fun _ : {l : Fin 2 // l ≠ i} => (1 : k))
      ((awayChartEquiv (S := k) 1 i).symm
        ((awayChartEquiv (S := k) 1 i) (MvPolynomial.X ⟨j, h⟩))) = 1
    rw [AlgEquiv.symm_apply_apply, MvPolynomial.aeval_X]

private lemma ones_chart_eq (i j : Fin 2) :
    Spec.map (CommRingCat.ofHom (ones k i).toRingHom) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i)
        (ProjSpace.X_mem_one k 1 i) one_pos =
    Spec.map (CommRingCat.ofHom (ones k j).toRingHom) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X j)
        (ProjSpace.X_mem_one k 1 j) one_pos :=
  ProjSpace.specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq
    k 1 k (fun _ => 1) i j isUnit_one isUnit_one (ones k i) (ones k j)
    (fun l => by rw [ones_ratio, mul_one]) (fun l => by rw [ones_ratio, mul_one])

end ProjectiveLineConstancy

open ProjectiveLineConstancy in
/-- Every morphism over a field from the projective line to an abelian variety is constant. -/
theorem exists_eq_const_of_projectiveLine
    (k : Type u) [Field k] {A : Scheme.{u}} {fA : A ⟶ Spec (CommRingCat.of k)}
    (hA : AbelianSchemePropertyBundle k fA)
    (q : Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k) ⟶ A)
    (hq : q ≫ fA = ProjSpace.π k 1) :
    ∃ a : Spec (CommRingCat.of k) ⟶ A,
      a ≫ fA = 𝟙 _ ∧ q = ProjSpace.π k 1 ≫ a := by
  let chart (i : Fin 2) := Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (MvPolynomial.X i) (ProjSpace.X_mem_one k 1 i) one_pos
  let π (i : Fin 2) := Spec.map (CommRingCat.ofHom
    (algebraMap k (Away (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i))))
  have hc (i : Fin 2) : chart i ≫ ProjSpace.π k 1 = π i :=
    ProjSpace.awayι_comp_π k 1 i
  have hconst (i : Fin 2) : ∃ a : Spec (CommRingCat.of k) ⟶ A,
      a ≫ fA = 𝟙 _ ∧ chart i ≫ q = π i ≫ a := by
    let e := chartEquiv k i
    let v := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
    have : IsIso (CommRingCat.ofHom e.symm.toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr e.symm.bijective
    have : IsIso v := inferInstance
    have hv : v ≫ π i = Spec.map (CommRingCat.ofHom (algebraMap k k[X])) := by
      change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k _)) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun f : k →+* k[X] => Spec.map (CommRingCat.ofHom f))
        e.symm.toAlgHom.comp_algebraMap
    obtain ⟨a, ha, hqa⟩ := exists_eq_const_of_affineLine k hA (v ≫ chart i ≫ q)
      (by rw [Category.assoc, Category.assoc, hq, hc, hv])
    refine ⟨a, ha, ?_⟩
    apply (cancel_epi v).mp
    rw [← Category.assoc v (π i), hv]
    exact hqa
  choose a ha hqa using hconst
  let pt (i : Fin 2) := Spec.map (CommRingCat.ofHom (ones k i).toRingHom)
  have hp (i : Fin 2) : pt i ≫ π i = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (ones k i).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k _)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hbase : (ones k i).toRingHom.comp
        (algebraMap k (Away (MvPolynomial.homogeneousSubmodule (Fin 2) k)
          (MvPolynomial.X i))) = RingHom.id k := by
      apply RingHom.ext
      intro r
      exact (ones k i).commutes r
    rw [hbase]
    exact Spec.map_id _
  have heq (i : Fin 2) : a i = a 0 := by
    calc
      a i = (pt i ≫ π i) ≫ a i := by rw [hp, Category.id_comp]
      _ = pt i ≫ chart i ≫ q := by rw [Category.assoc, ← hqa]
      _ = pt 0 ≫ chart 0 ≫ q := by rw [← Category.assoc, ones_chart_eq k i 0, Category.assoc]
      _ = a 0 := by rw [hqa, ← Category.assoc, hp, Category.id_comp]
  refine ⟨a 0, ha 0, ?_⟩
  apply Scheme.Cover.hom_ext (ProjSpace.affineOpenCover k 1).openCover
  intro i
  change Fin 2 at i
  change chart i ≫ q = chart i ≫ ProjSpace.π k 1 ≫ a 0
  rw [hqa, heq, ← Category.assoc, hc]

end GoodReductionJacobian
