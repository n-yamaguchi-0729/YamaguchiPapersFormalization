/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Picard.Exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
import Nyll.JacobianVarieties.Pic0.Pic0_mem_closure_mk_single_sub_single
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Schemes.isReduced_of_smooth_of_field
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Abel–Jacobi maps detect group homomorphisms

For a pointed smooth proper geometrically integral curve model over an algebraically
closed field, choose the actual group law and Abel–Jacobi morphism supplied by the
Picard representation. Two morphisms from that representation into a separated group
scheme are equal if they preserve multiplication and agree after Abel–Jacobi.

The proof uses the proved generation of `Pic0` by point differences, the actual
Picard-to-points equivalence, and density of geometric points on a reduced scheme.
This proves uniqueness of a possible Albanese factorization. Existence of that
factorization, and descent of arbitrary-target sums, are separate assertions.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.RelPicard

open AlgebraicCurves.Geometry.Schemes.Proofs
open SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat

open RigKerGeomPoints renaming ext_of_forall_geometric_point → geometricHomExt in
/-- The actual Abel–Jacobi morphism detects multiplicative morphisms out of the
Picard representation. No properness or commutativity is required of the target group. -/
theorem exists_abelJacobi_detects_hom_of_curveModel
    {K : Type u} [Field K] [IsAlgClosed K]
    {F : Type v} [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F) [GeometricallyIntegral M.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase)
    (D : RelativePic0Designation K M.toBase)
    (hD : RepresentsRelSubPic M.toBase ε (algEquivZeroCut M.toBase ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase)
    (hgc : GeometricallyConnected D.toBase) :
    ∃ (L : RelativeGroupLaw K D.toBase) (aj : SchemeHomOver M.toBase D.toBase),
      AbelianSchemePropertyBundle K D.toBase ∧
      (L.one (𝟙 (Spec (CommRingCat.of K)))).1 = D.zeroSection ∧
      ε.1 ≫ aj.1 = D.zeroSection ∧
      ∀ (B : Scheme.{u}) (b : B ⟶ Spec (CommRingCat.of K)), IsSeparated b →
        ∀ (G : RelativeGroupLaw K b) (φ ψ : SchemeHomOver D.toBase b),
          (∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase,
            NeronModelInfra.schemeHomOverComp (L.mul _ x y) φ =
              G.mul _ (NeronModelInfra.schemeHomOverComp x φ)
                (NeronModelInfra.schemeHomOverComp y φ)) →
          (∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase,
            NeronModelInfra.schemeHomOverComp (L.mul _ x y) ψ =
              G.mul _ (NeronModelInfra.schemeHomOverComp x ψ)
                (NeronModelInfra.schemeHomOverComp y ψ)) →
          aj.1 ≫ φ.1 = aj.1 ≫ ψ.1 → φ = ψ := by
  obtain ⟨L, aj, hA, -, hone, haj, -, hpoints⟩ :=
    exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
      K M.toBase ε D hD hsm hpr hgc
  refine ⟨L, aj, hA, hone, haj, ?_⟩
  intro B b hb G φ ψ hφ hψ hagree
  have : IsSeparated b := hb
  have : Smooth D.toBase := hsm
  have : IsReduced D.P := isReduced_of_smooth_of_field D.toBase
  have hpts := hpoints K (RingHom.id K) F M
  generalize hι : Spec.map (CommRingCat.ofHom (RingHom.id K)) = ι at hpts
  have hιid : ι = 𝟙 _ := by rw [← hι, CommRingCat.ofHom_id, Spec.map_id]
  subst hιid
  let e : M.C ⟶ pullback M.toBase (𝟙 (Spec (CommRingCat.of K))) :=
    pullback.lift (𝟙 M.C) M.toBase (by rw [Category.id_comp, Category.comp_id])
  have hef : e ≫ pullback.fst M.toBase (𝟙 _) = 𝟙 M.C := pullback.lift_fst _ _ _
  have hes : e ≫ pullback.snd M.toBase (𝟙 _) = M.toBase := pullback.lift_snd _ _ _
  have : IsIso e := by
    have : IsIso (e ≫ pullback.fst M.toBase (𝟙 _)) := by rw [hef]; infer_instance
    exact IsIso.of_isIso_comp_right e (pullback.fst M.toBase (𝟙 _))
  obtain ⟨pts, hadd, hpoint⟩ := hpts e hes
  let t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) := 𝟙 _
  let : Group (SchemeHomOver t b) := G.pointGroup t
  let fφ : Pic0 K F →+ Additive (SchemeHomOver t b) :=
    AddMonoidHom.mk' (fun z => Additive.ofMul (NeronModelInfra.schemeHomOverComp (pts z) φ))
      (fun x y => by change _ = G.mul t _ _; rw [hadd]; exact hφ (pts x) (pts y))
  let fψ : Pic0 K F →+ Additive (SchemeHomOver t b) :=
    AddMonoidHom.mk' (fun z => Additive.ofMul (NeronModelInfra.schemeHomOverComp (pts z) ψ))
      (fun x y => by change _ = G.mul t _ _; rw [hadd]; exact hψ (pts x) (pts y))
  have heq (z : Pic0 K F) : fφ z = fψ z := by
    apply AddMonoidHom.eqOn_closure (s :=
      {y : Pic0 K F | ∃ (V : Place K F)
        (h : Finsupp.single V (1 : ℤ) - Finsupp.single (M.pointEquivPlace ε) 1 ∈
          Divisor.degZero (K := K) (F := F)),
        y = Pic0.mk ⟨Finsupp.single V (1 : ℤ) -
          Finsupp.single (M.pointEquivPlace ε) 1, h⟩}) ?_
      (Pic0.mem_closure_mk_single_sub_single
        IsCurveOver.forall_deg_eq_one_of_isAlgClosed (M.pointEquivPlace ε) z)
    rintro _ ⟨V, hV, rfl⟩
    let x := M.pointEquivPlace.symm V
    have hs : ε.1 ≫ e ≫ pullback.fst M.toBase (𝟙 _) = 𝟙 _ ≫ ε.1 := by
      rw [hef, Category.comp_id, Category.id_comp]
    obtain ⟨Dv, hDv, hx⟩ := hpoint x ε hs
    have hv : M.pointEquivPlace x = V := M.pointEquivPlace.apply_symm_apply V
    rw [hv] at hDv
    have hclass : Dv = ⟨Finsupp.single V (1 : ℤ) -
        Finsupp.single (M.pointEquivPlace ε) 1, hV⟩ := Subtype.ext hDv
    rw [hclass, ← Category.assoc e, hef, Category.id_comp] at hx
    apply congrArg Additive.ofMul
    apply Subtype.ext
    change (pts (Pic0.mk _)).1 ≫ φ.1 = (pts (Pic0.mk _)).1 ≫ ψ.1
    rw [hx, Category.assoc, Category.assoc, hagree]
  have hpoint_eq (x : SchemeHomOver t D.toBase) :
      x.1 ≫ φ.1 = x.1 ≫ ψ.1 := by
    obtain ⟨z, rfl⟩ := pts.surjective x
    exact congrArg (fun a : Additive (SchemeHomOver t b) => a.toMul.1) (heq z)
  apply Subtype.ext
  apply geometricHomExt
    (R := K) (L := K) (Function.injective_id) D.toBase b φ.1 ψ.1 φ.2 ψ.2
  intro x hx
  have hxid : x ≫ D.toBase = t := by
    simpa only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id] using hx
  exact hpoint_eq ⟨x, hxid⟩

end AlgebraicGeometry.RelPicard
