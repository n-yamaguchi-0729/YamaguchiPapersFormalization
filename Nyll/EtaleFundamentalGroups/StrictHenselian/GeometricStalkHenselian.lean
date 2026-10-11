/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RingHom.Etale


/-!
# Henselianity of the constructed geometric étale stalk

The ring in `GeometricStalk` is the actual filtered colimit over pointed étale
neighborhoods. A monic polynomial descends to one neighborhood because it has
only finitely many coefficients. A simple root at the geometric point then
defines a further neighborhood using the concrete standard étale algebra
`R[X,Y]/(f, Y f' - 1)`. Its universal root gives the required root in the colimit.

The resulting Henselian property is proved, not added as a field of a putative
strict henselization. Identification of its residue field and comparison with
the inertia group in the manuscript still require separate arguments.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Polynomial

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- A monic polynomial over the geometric stalk comes from a monic polynomial
over the sections of one actual pointed étale neighborhood. -/
theorem geometricStalk_monic_exists_representative
    (p : (geometricStalk s)[X]) (hp : p.Monic) :
    ∃ (W : S.Etale) (t : (Scheme.pointEtaleNeighborhoods s).fiber.obj W)
      (q : Γ(W.left, ⊤)[X]), q.Monic ∧ q.map (geometricStalkGerm s W t).hom = p := by
  classical
  obtain ⟨W, t, z, hz⟩ := geometricStalk_exists_representatives s
    (fun i : Fin p.natDegree => p.coeff i)
  let q : Γ(W.left, ⊤)[X] := X ^ p.natDegree +
    ∑ i : Fin p.natDegree, C (z i) * X ^ (i : ℕ)
  refine ⟨W, t, q, monic_X_pow_add (degree_sum_fin_lt z), ?_⟩
  change (X ^ p.natDegree + ∑ i : Fin p.natDegree, C (z i) * X ^ (i : ℕ)).map
    (geometricStalkGerm s W t).hom = p
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, hz]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => C (p.coeff i) * X ^ i) p.natDegree]
  exact hp.as_sum.symm

/-- A simple root at the geometric point lifts by the actual standard étale
neighborhood obtained by adjoining a root and inverting its derivative. -/
theorem geometricStalk_lift_simpleRoot (W : S.Etale)
    (t : (Scheme.pointEtaleNeighborhoods s).fiber.obj W)
    (q : Γ(W.left, ⊤)[X]) (hq : q.Monic) (α : Ω)
    (hroot : (q.map (t.left.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom).eval α = 0)
    (hderivative : (q.derivative.map (t.left.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom).eval α ≠ 0) :
    ∃ a : geometricStalk s,
      (q.map (geometricStalkGerm s W t).hom).IsRoot a ∧
      geometricStalkEvaluation s a = α := by
  let R : CommRingCat.{u} := Γ(W.left, ⊤)
  let φ : R ⟶ CommRingCat.of Ω :=
    t.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom
  let : Algebra R Ω := φ.hom.toAlgebra
  let P : StandardEtalePair R :=
    { f := q
      monic_f := hq
      g := q.derivative
      cond := ⟨1, 0, 1, by rw [mul_one, mul_zero, add_zero, pow_one]⟩ }
  have hα : P.HasMap α := by
    constructor
    · change q.eval₂ φ.hom α = 0
      rw [eval₂_eq_eval_map]
      exact hroot
    · change IsUnit (q.derivative.eval₂ φ.hom α)
      rw [eval₂_eq_eval_map]
      exact isUnit_iff_ne_zero.mpr hderivative
  let B : CommRingCat.{u} := .of P.Ring
  let base : R ⟶ B := CommRingCat.ofHom (algebraMap R P.Ring)
  let ψ : B ⟶ CommRingCat.of Ω := CommRingCat.ofHom (P.lift α hα).toRingHom
  have hbaseψ : base ≫ ψ = φ := by
    apply CommRingCat.hom_ext
    exact (P.lift α hα).comp_algebraMap
  have hpoint : t.left ≫ W.left.toSpecΓ = Spec.map ψ ≫ Spec.map base := by
    have hnatural : t.left ≫ W.left.toSpecΓ =
        (Spec (CommRingCat.of Ω)).toSpecΓ ≫ Spec.map t.left.appTop :=
      Scheme.toSpecΓ_naturality t.left
    have hφ : (Spec (CommRingCat.of Ω)).toSpecΓ ≫ Spec.map t.left.appTop =
        Spec.map φ := by
      change (Spec (CommRingCat.of Ω)).toSpecΓ ≫ Spec.map t.left.appTop =
        Spec.map (t.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom)
      rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
    have hcomp : Spec.map φ = Spec.map ψ ≫ Spec.map base := by
      rw [← Spec.map_comp, hbaseψ]
    exact hnatural.trans (hφ.trans hcomp)
  have : Etale (Spec.map base) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  let V : Scheme.{u} := pullback W.left.toSpecΓ (Spec.map base)
  let j : V ⟶ W.left := pullback.fst W.left.toSpecΓ (Spec.map base)
  let k : V ⟶ Spec B := pullback.snd W.left.toSpecΓ (Spec.map base)
  let l : Spec (CommRingCat.of Ω) ⟶ V := pullback.lift t.left (Spec.map ψ) hpoint
  have hlj : l ≫ j = t.left := pullback.lift_fst _ _ _
  have hlk : l ≫ k = Spec.map ψ := pullback.lift_snd _ _ _
  let T : S.Etale := Scheme.Etale.mk (j ≫ W.hom)
  let f : T ⟶ W := MorphismProperty.Over.homMk j rfl
  let tT : (Scheme.pointEtaleNeighborhoods s).fiber.obj T := Over.homMk l (by
    change l ≫ (j ≫ W.hom) = s
    rw [← Category.assoc, hlj]
    exact Over.w t)
  have htT : (Scheme.pointEtaleNeighborhoods s).fiber.map f tT = t := by
    apply Over.OverMorphism.ext
    exact hlj
  let h : B ⟶ Γ(V, ⊤) := (Scheme.ΓSpecIso B).inv ≫ k.appTop
  have hbase : base ≫ h = j.appTop := by
    change base ≫ (Scheme.ΓSpecIso B).inv ≫ k.appTop = j.appTop
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      ← Scheme.Hom.comp_appTop]
    change (Scheme.ΓSpecIso R).inv ≫
      (pullback.snd W.left.toSpecΓ (Spec.map base) ≫ Spec.map base).appTop = j.appTop
    rw [← pullback.condition, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      Iso.inv_hom_id_assoc]
  let germ : Γ(V, ⊤) ⟶ geometricStalk s := geometricStalkGerm s T tT
  have hgerm : j.appTop ≫ germ = geometricStalkGerm s W t := by
    have heq := (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w f tT (etaleSections S)
    rw [htT] at heq
    exact heq
  have hgermEvaluation : germ ≫ geometricStalkEvaluation s =
      l.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom :=
    geometricStalkGerm_evaluation s T tT
  let e : B ⟶ geometricStalk s := h ≫ germ
  have he : e.hom.comp (algebraMap R P.Ring) =
      (geometricStalkGerm s W t).hom := by
    change (base ≫ e).hom = (geometricStalkGerm s W t).hom
    change (base ≫ (h ≫ germ)).hom = (geometricStalkGerm s W t).hom
    rw [← Category.assoc, hbase, hgerm]
  have heval : e ≫ geometricStalkEvaluation s = ψ := by
    change ((Scheme.ΓSpecIso B).inv ≫ k.appTop ≫ germ) ≫
      geometricStalkEvaluation s = ψ
    rw [Category.assoc, Category.assoc, hgermEvaluation]
    rw [← Category.assoc k.appTop, ← Scheme.Hom.comp_appTop, hlk,
      Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  refine ⟨e P.X, ?_, ?_⟩
  · change (q.map (geometricStalkGerm s W t).hom).eval (e P.X) = 0
    rw [eval_map, ← he, ← Polynomial.hom_eval₂]
    have hPX : q.eval₂ (algebraMap R P.Ring) P.X = 0 := P.hasMap_X.1
    rw [hPX, map_zero]
  · exact (ConcreteCategory.congr_hom heval P.X).trans (P.lift_X α hα)

/-- A simple root in the geometric field of a monic polynomial over the stalk
is the value of an actual root in the stalk. -/
theorem geometricStalk_exists_root_of_evaluation_simpleRoot
    (p : (geometricStalk s)[X]) (hp : p.Monic) (α : Ω)
    (hroot : (p.map (geometricStalkEvaluation s).hom).eval α = 0)
    (hderivative : (p.derivative.map (geometricStalkEvaluation s).hom).eval α ≠ 0) :
    ∃ a : geometricStalk s, p.IsRoot a ∧ geometricStalkEvaluation s a = α := by
  obtain ⟨W, t, q, hq, hqp⟩ := geometricStalk_monic_exists_representative s p hp
  let φ : Γ(W.left, ⊤) ⟶ CommRingCat.of Ω :=
    t.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom
  have hmap : q.map φ.hom = p.map (geometricStalkEvaluation s).hom := by
    rw [← hqp, Polynomial.map_map]
    exact congrArg (fun f : Γ(W.left, ⊤) ⟶ CommRingCat.of Ω => q.map f.hom)
      (geometricStalkGerm_evaluation s W t).symm
  have hroot' : (q.map φ.hom).eval α = 0 := by
    rw [hmap]
    exact hroot
  have hderivative' : (q.derivative.map φ.hom).eval α ≠ 0 := by
    rw [← derivative_map, hmap, derivative_map]
    exact hderivative
  obtain ⟨a, ha, heval⟩ :=
    geometricStalk_lift_simpleRoot s W t q hq α hroot' hderivative'
  refine ⟨a, ?_, heval⟩
  rw [← hqp]
  exact ha

/-- The maximal ideal of the constructed stalk is exactly the kernel of its
evaluation at the geometric point. -/
theorem geometricStalk_mem_maximalIdeal_iff (a : geometricStalk s) :
    a ∈ IsLocalRing.maximalIdeal (geometricStalk s) ↔
      geometricStalkEvaluation s a = 0 := by
  classical
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, geometricStalk_isUnit_iff]
  exact not_not

/-- The étale stalk constructed from genuine pointed neighborhoods is Henselian.
The root is supplied by a concrete standard étale polynomial algebra. -/
instance geometricStalk_henselianLocalRing : HenselianLocalRing (geometricStalk s) where
  is_henselian p hp a₀ hroot hderivative := by
    have hroot' : (p.map (geometricStalkEvaluation s).hom).eval
        (geometricStalkEvaluation s a₀) = 0 := by
      rw [eval_map_apply]
      exact (geometricStalk_mem_maximalIdeal_iff s (p.eval a₀)).mp hroot
    have hderivative' : (p.derivative.map (geometricStalkEvaluation s).hom).eval
        (geometricStalkEvaluation s a₀) ≠ 0 := by
      rw [eval_map_apply]
      exact (geometricStalk_isUnit_iff s (p.derivative.eval a₀)).mp hderivative
    obtain ⟨a, ha, heval⟩ := geometricStalk_exists_root_of_evaluation_simpleRoot s p hp
      (geometricStalkEvaluation s a₀) hroot' hderivative'
    refine ⟨a, ha, ?_⟩
    rw [geometricStalk_mem_maximalIdeal_iff, map_sub, heval, sub_self]

end EtaleFundamentalGroups.StrictHenselian
