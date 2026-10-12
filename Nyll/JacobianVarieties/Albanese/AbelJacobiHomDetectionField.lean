/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Picard.Exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
import Nyll.JacobianVarieties.Pic0.Pic0_mem_closure_mk_single_sub_single
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_curveModel_iso_pullback_of_isAlgClosed
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Schemes.isReduced_of_smooth_of_field
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Mathlib.Algebra.Group.Subgroup.Ker

import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.SchemeTheory.Modules.Monoidal

/-!
# Abel–Jacobi homomorphism detection over any field

For a pointed smooth proper geometrically integral curve over an arbitrary field,
the actual Picard representation supplies an Abel–Jacobi map that detects morphisms
to separated group schemes. Multiplication preservation need only be checked on
points over one algebraically closed extension of the base field.

The curve model and its point-divisor comparison are constructed on that geometric
fibre. Generation of its Picard group proves equality on geometric points; density
on the smooth Picard representation proves equality of the original morphisms.
This is uniqueness of an Albanese factorization, not its existence.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian

open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.RelPicard

open AlgebraicCurves.Geometry.Schemes.Proofs
open SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat

open RigKerGeomPoints renaming ext_of_forall_geometric_point → geometricHomExt in
/-- Over any field, the constructed Abel–Jacobi map detects morphisms preserving
multiplication on geometric points, with an arbitrary separated group scheme as target. -/
theorem exists_abelJacobi_detects_hom_of_field
    (K : Type u) [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    (D : RelativePic0Designation K c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase)
    (hgc : GeometricallyConnected D.toBase) :
    ∃ (L : RelativeGroupLaw K D.toBase) (aj : SchemeHomOver c D.toBase),
      AbelianSchemePropertyBundle K D.toBase ∧
      (L.one (𝟙 (Spec (CommRingCat.of K)))).1 = D.zeroSection ∧
      ε.1 ≫ aj.1 = D.zeroSection ∧
      (∀ (k : Type u) [Field k] (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K))
          (x : SchemeHomOver t c),
        Nonempty ((hD.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans
                  ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule)) ∧
      ∀ (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω],
        let t := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
        ∀ (B : Scheme.{u}) (b : B ⟶ Spec (CommRingCat.of K)), IsSeparated b →
          ∀ (G : RelativeGroupLaw K b) (φ ψ : SchemeHomOver D.toBase b),
            (∀ x y : SchemeHomOver t D.toBase,
              NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
                G.mul t (NeronModelInfra.schemeHomOverComp x φ)
                  (NeronModelInfra.schemeHomOverComp y φ)) →
            (∀ x y : SchemeHomOver t D.toBase,
              NeronModelInfra.schemeHomOverComp (L.mul t x y) ψ =
                G.mul t (NeronModelInfra.schemeHomOverComp x ψ)
                  (NeronModelInfra.schemeHomOverComp y ψ)) →
            aj.1 ≫ φ.1 = aj.1 ≫ ψ.1 → φ = ψ := by
  obtain ⟨L, aj, hA, -, hone, haj, hclass, hpoints⟩ :=
    exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic K c ε D hD hsm hpr hgc
  refine ⟨L, aj, hA, hone, haj, hclass, ?_⟩
  intro Ω _ _ _ t B b hb G φ ψ hφ hψ hagree
  have : IsSeparated b := hb
  have : Smooth D.toBase := hsm
  have : IsReduced D.P := isReduced_of_smooth_of_field D.toBase
  obtain ⟨F, _, _, _, _, M, e, he⟩ :=
    SmoothProperCurve.exists_curveModel_iso_pullback_of_isAlgClosed K c Ω t
  let εΩ : Spec (CommRingCat.of Ω) ⟶ pullback c t :=
    pullback.lift (t ≫ ε.1) (𝟙 _) (by
      rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp])
  let s : SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) M.toBase :=
    ⟨εΩ ≫ e.inv, by
      rw [Category.assoc, ← he, e.inv_hom_id_assoc]
      exact pullback.lift_snd _ _ _⟩
  have hs : s.1 ≫ e.hom ≫ pullback.fst c t = t ≫ ε.1 := by
    change (εΩ ≫ e.inv) ≫ e.hom ≫ pullback.fst c t = _
    rw [Category.assoc, e.inv_hom_id_assoc]
    exact pullback.lift_fst _ _ _
  obtain ⟨pts, hadd, hpoint⟩ := hpoints Ω (algebraMap K Ω) F M e.hom he
  let : Group (SchemeHomOver t b) := G.pointGroup t
  let fφ : Pic0 Ω F →+ Additive (SchemeHomOver t b) :=
    AddMonoidHom.mk' (fun z => Additive.ofMul (NeronModelInfra.schemeHomOverComp (pts z) φ))
      (fun x y => by change _ = G.mul t _ _; rw [hadd]; exact hφ (pts x) (pts y))
  let fψ : Pic0 Ω F →+ Additive (SchemeHomOver t b) :=
    AddMonoidHom.mk' (fun z => Additive.ofMul (NeronModelInfra.schemeHomOverComp (pts z) ψ))
      (fun x y => by change _ = G.mul t _ _; rw [hadd]; exact hψ (pts x) (pts y))
  have heq (z : Pic0 Ω F) : fφ z = fψ z := by
    apply AddMonoidHom.eqOn_closure (s :=
      {y : Pic0 Ω F | ∃ (V : Place Ω F)
        (h : Finsupp.single V (1 : ℤ) - Finsupp.single (M.pointEquivPlace s) 1 ∈
          Divisor.degZero (K := Ω) (F := F)),
        y = Pic0.mk ⟨Finsupp.single V (1 : ℤ) -
          Finsupp.single (M.pointEquivPlace s) 1, h⟩}) ?_
      (Pic0.mem_closure_mk_single_sub_single
        IsCurveOver.forall_deg_eq_one_of_isAlgClosed (M.pointEquivPlace s) z)
    rintro _ ⟨V, hV, rfl⟩
    let x := M.pointEquivPlace.symm V
    obtain ⟨Dv, hDv, hx⟩ := hpoint x s hs
    have hv : M.pointEquivPlace x = V := M.pointEquivPlace.apply_symm_apply V
    rw [hv] at hDv
    have hclass : Dv = ⟨Finsupp.single V (1 : ℤ) -
        Finsupp.single (M.pointEquivPlace s) 1, hV⟩ := Subtype.ext hDv
    rw [hclass] at hx
    apply congrArg Additive.ofMul
    apply Subtype.ext
    change (pts (Pic0.mk _)).1 ≫ φ.1 = (pts (Pic0.mk _)).1 ≫ ψ.1
    rw [hx, Category.assoc, Category.assoc, Category.assoc, Category.assoc,
      Category.assoc, Category.assoc, hagree]
  have hpoint_eq (x : SchemeHomOver t D.toBase) : x.1 ≫ φ.1 = x.1 ≫ ψ.1 := by
    obtain ⟨z, rfl⟩ := pts.surjective x
    exact congrArg (fun a : Additive (SchemeHomOver t b) => a.toMul.1) (heq z)
  apply Subtype.ext
  apply geometricHomExt (R := K) (L := Ω) (algebraMap K Ω).injective
    D.toBase b φ.1 ψ.1 φ.2 ψ.2
  intro x hx
  exact hpoint_eq ⟨x, hx⟩

end AlgebraicGeometry.RelPicard
