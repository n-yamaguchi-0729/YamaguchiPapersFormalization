/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Albanese.AbelJacobiMorphismDetectionField
import Nyll.JacobianVarieties.Albanese.AbelJacobiPointClassUnique
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOverBaseChange
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.BaseChange
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Nyll.JacobianVarieties.Picard.AbelJacobiPointClassBaseChange
import Nyll.JacobianVarieties.Picard.Exists_representsRelSubPic_baseChange
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
import Nyll.JacobianVarieties.Picard.Designation
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Nyll.AlgebraicCurves.Geometry.Schemes.isReduced_of_smooth_of_field
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.SchemeTheory.Modules.Monoidal
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.CategoryTheory.EffectiveEpi.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Finite

/-!
# Descent of an actual Albanese factorization

The factorization over a finite separable extension descends along its finite
faithfully flat spectrum map. Equality on the overlap follows from actual
geometric point classes and uniqueness among all scheme morphisms.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Albanese.SeparableDescent

variable {S S' T C P B : Scheme.{u}}
  (s : S' ⟶ S) (t : T ⟶ S) (v : T ⟶ S') (hv : v ≫ s = t)
  (p : P ⟶ S) (b : B ⟶ S)

private def scalarLeg : pullback p t ⟶ pullback p s :=
  pullback.lift (pullback.fst p t) (pullback.snd p t ≫ v)
    (by rw [Category.assoc, hv, pullback.condition])

private def factorAt
    (ψ : SchemeHomOver (pullback.snd p s) (pullback.snd b s)) :
    SchemeHomOver (pullback.snd p t) (pullback.snd b t) :=
  ⟨pullback.lift (scalarLeg s t v hv p ≫ ψ.1 ≫ pullback.fst b s)
    (pullback.snd p t) (by
      rw [Category.assoc, Category.assoc, pullback.condition,
        ← Category.assoc ψ.1, ψ.2, ← Category.assoc,
        scalarLeg, pullback.lift_snd, Category.assoc, hv]),
    pullback.lift_snd _ _ _⟩

private theorem scalarLeg_natural (c : C ⟶ S) (a : SchemeHomOver c p) :
    (fibreRestrictAlong t p c a).1 ≫ scalarLeg s t v hv p =
      scalarLeg s t v hv c ≫ (fibreRestrictAlong s p c a).1 := by
  apply pullback.hom_ext
  · simp only [Category.assoc, scalarLeg, pullback.lift_fst,
      fibreRestrictAlong_coe_comp_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, scalarLeg, pullback.lift_snd,
      fibreRestrictAlong_coe_comp_snd, fibreRestrictAlong_coe_comp_snd_assoc]

private theorem factorAt_comp (c : C ⟶ S) (a : SchemeHomOver c p)
    (q : SchemeHomOver c b)
    (ψ : SchemeHomOver (pullback.snd p s) (pullback.snd b s))
    (hψ : (fibreRestrictAlong s p c a).1 ≫ ψ.1 = (fibreRestrictAlong s b c q).1) :
    (fibreRestrictAlong t p c a).1 ≫ (factorAt s t v hv p b ψ).1 =
      (fibreRestrictAlong t b c q).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, factorAt, pullback.lift_fst,
      ← Category.assoc, scalarLeg_natural s t v hv p c a,
      Category.assoc, ← Category.assoc (fibreRestrictAlong s p c a).1, hψ,
      fibreRestrictAlong_coe_comp_fst, ← Category.assoc]
    rw [scalarLeg, pullback.lift_fst, fibreRestrictAlong_coe_comp_fst]
  · rw [Category.assoc, (factorAt s t v hv p b ψ).2,
      fibreRestrictAlong_coe_comp_snd, fibreRestrictAlong_coe_comp_snd]

end JacobianVarieties.Albanese.SeparableDescent

open AlgebraicGeometry.SmoothProperCurve

namespace JacobianVarieties.Albanese

private theorem pointed_fibreRestrictAlong
    {K L : Type u} [Field K] [Field L] [Algebra K L] {C B : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (b : B ⟶ Spec (CommRingCat.of K))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    (G : RelativeGroupLaw K b) (q : SchemeHomOver c b)
    (hq : NeronModelInfra.schemeHomOverComp ε q = G.one (𝟙 _)) :
    NeronModelInfra.schemeHomOverComp (sectionBaseChange L ε)
      (fibreRestrictAlong (specMap K L) b c q) =
        (G.baseChange (specMap K L)).one (𝟙 _) := by
  apply (RelativeGroupLaw.baseChangePointEquiv (specMap K L) (𝟙 _)).injective
  change RelativeGroupLaw.baseChangePointToBase (specMap K L) _ =
    RelativeGroupLaw.baseChangePointToBase (specMap K L) _
  rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong,
    RelativeGroupLaw.baseChangePointToBase_one]
  apply Subtype.ext
  change ((sectionBaseChange L ε).1 ≫ pullback.fst c (specMap K L)) ≫ q.1 = _
  have hq' : ε.1 ≫ q.1 = (G.one (𝟙 _)).1 := congrArg Subtype.val hq
  rw [sectionBaseChange_coe_fst, Category.assoc, hq']
  exact congrArg Subtype.val
    (G.one_natural (𝟙 _) (𝟙 _ ≫ specMap K L) (specMap K L)
      ((Category.comp_id _).trans (Category.id_comp _).symm))

end JacobianVarieties.Albanese

open CategoryTheory.MonoidalCategory AlgebraicGeometry.RelPicard
open AlgebraicCurves.Geometry.Schemes.Proofs
open SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat

namespace JacobianVarieties.Albanese

open SeparableDescent
open RigKerGeomPoints renaming ext_of_forall_geometric_point → geometricHomExt in
/-- A factorization obtained over an actual finite separable extension descends
to the ground field. Compatibility on the overlap is proved from the actual
geometric point classes and Abel--Jacobi uniqueness. -/
theorem exists_factorization_of_finite_separable_baseChange
    (K : Type u) [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    (D : RelativePic0Designation K c) [Smooth D.toBase] [IsProper D.toBase]
    [GeometricallyConnected D.toBase]
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (aj : SchemeHomOver c D.toBase)
    (hclass : ∀ (F : Type u) [Field F]
      (t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K))
      (x : SchemeHomOver t c),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of K)) [Smooth b] [IsProper b]
    [GeometricallyIntegral b] (G : RelativeGroupLaw K b) (q : SchemeHomOver c b)
    (hq : NeronModelInfra.schemeHomOverComp ε q = G.one (𝟙 _))
    (L : Type u) [Field L] [Algebra K L] [Module.Finite K L]
    [Algebra.IsSeparable K L]
    (ψ : SchemeHomOver (D.baseChange L).toBase (pullback.snd b (specMap K L)))
    (hψ : (fibreRestrictAlong (specMap K L) D.toBase c aj).1 ≫ ψ.1 =
      (fibreRestrictAlong (specMap K L) b c q).1) :
    ∃ φ : SchemeHomOver D.toBase b, aj.1 ≫ φ.1 = q.1 := by
  let s := specMap K L
  let p := pullback.fst D.toBase s
  let e : pullback D.toBase s ⟶ B := ψ.1 ≫ pullback.fst b s
  have heb : e ≫ b = p ≫ D.toBase := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ψ.2]
    exact pullback.condition.symm
  have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  have : Module.FinitePresentation K L := Module.finitePresentation_of_finite K L
  have : Algebra.Etale K L := { }
  have : Etale s := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  have hsurj : Surjective s :=
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap K L))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr
        (inferInstanceAs (Module.FaithfullyFlat K L)))).2
  have : IsFinite s := (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap K L))).mpr
    (RingHom.finite_algebraMap.mpr (inferInstanceAs (Module.Finite K L)))
  let w : pullback p p ⟶ Spec (CommRingCat.of K) :=
    pullback.fst p p ≫ p ≫ D.toBase
  have : Smooth w := inferInstance
  have : IsReduced (pullback p p) := isReduced_of_smooth_of_field w
  let Ω := AlgebraicClosure K
  let t := specMap K Ω
  let cΩ := SmoothProperCurve.baseChange K c Ω
  let bΩ := pullback.snd b t
  let qΩ : SchemeHomOver cΩ bΩ := fibreRestrictAlong t b c q
  let GΩ : RelativeGroupLaw Ω bΩ := G.baseChange t
  let ajΩ : SchemeHomOver cΩ (D.baseChange Ω).toBase :=
    fibreRestrictAlong t D.toBase c aj
  obtain ⟨hDΩ, hPΩ⟩ := exists_representsRelSubPic_baseChange K c ε D hD Ω
  obtain ⟨_, aΩ, _, _, _, hclassΩ, huniqΩ⟩ :=
    exists_abelJacobi_detects_pointed_factorizations_of_field Ω cΩ
      (sectionBaseChange Ω ε) (D.baseChange Ω) hDΩ inferInstance inferInstance inferInstance
  have hnative := abelJacobi_point_class_baseChange K c ε D hD aj hclass Ω hDΩ hPΩ
  have haΩ : aΩ = ajΩ := abelJacobi_eq_of_geometric_point_class Ω cΩ
    (sectionBaseChange Ω ε) (D.baseChange Ω) hDΩ Ω aΩ ajΩ
    (hclassΩ Ω _) (hnative Ω _)
  have : GeometricallyConnected bΩ := GeometricallyIrreducible.geometricallyConnected bΩ
  let hBΩ : AbelianSchemePropertyBundle Ω bΩ :=
    ⟨inferInstance, inferInstance, bΩ.isConnected_preimage_singleton, ⟨GΩ⟩⟩
  have hqΩ : NeronModelInfra.schemeHomOverComp (sectionBaseChange Ω ε) qΩ = GΩ.one (𝟙 _) :=
    pointed_fibreRestrictAlong c b ε G q hq
  have hpair : pullback.fst p p ≫ e = pullback.snd p p ≫ e := by
    apply geometricHomExt (R := K) (L := Ω) (algebraMap K Ω).injective w b
      (pullback.fst p p ≫ e) (pullback.snd p p ≫ e)
      (by rw [Category.assoc, heb])
      (by rw [Category.assoc, heb, ← Category.assoc, ← pullback.condition]; rfl)
    intro z hz
    let x : Spec (CommRingCat.of Ω) ⟶ D.P := z ≫ pullback.fst p p ≫ p
    let v₁ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of L) :=
      z ≫ pullback.fst p p ≫ pullback.snd D.toBase s
    let v₂ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of L) :=
      z ≫ pullback.snd p p ≫ pullback.snd D.toBase s
    have hx : x ≫ D.toBase = t := by
      simpa only [x, w, Category.assoc] using hz
    have hv₁ : v₁ ≫ s = t := by
      rw [Category.assoc, Category.assoc, ← pullback.condition]
      exact hx
    have hv₂ : v₂ ≫ s = t := by
      rw [Category.assoc, Category.assoc, ← pullback.condition,
        ← Category.assoc (pullback.snd p p), ← pullback.condition]
      exact hx
    let f₁ := factorAt s t v₁ hv₁ D.toBase b ψ
    let f₂ := factorAt s t v₂ hv₂ D.toBase b ψ
    have hf₁ : aΩ.1 ≫ f₁.1 = qΩ.1 := by
      rw [haΩ]
      exact factorAt_comp s t v₁ hv₁ D.toBase b c aj q ψ hψ
    have hf₂ : aΩ.1 ≫ f₂.1 = qΩ.1 := by
      rw [haΩ]
      exact factorAt_comp s t v₂ hv₂ D.toBase b c aj q ψ hψ
    have hf : f₁ = f₂ := huniqΩ (pullback b t) bΩ GΩ hBΩ qΩ hqΩ f₁ f₂ hf₁ hf₂
    let zΩ : Spec (CommRingCat.of Ω) ⟶ (D.baseChange Ω).P :=
      pullback.lift x (𝟙 _) (hx.trans (Category.id_comp t).symm)
    have hzΩfst : zΩ ≫ pullback.fst D.toBase t = x :=
      pullback.lift_fst _ _ _
    have hzΩsnd : zΩ ≫ pullback.snd D.toBase t = 𝟙 _ :=
      pullback.lift_snd _ _ _
    have hz₁ : zΩ ≫ scalarLeg s t v₁ hv₁ D.toBase = z ≫ pullback.fst p p := by
      apply pullback.hom_ext
      · rw [Category.assoc, scalarLeg, pullback.lift_fst, hzΩfst]
        rfl
      · rw [Category.assoc, scalarLeg, pullback.lift_snd,
          ← Category.assoc, hzΩsnd, Category.id_comp]
        rfl
    have hz₂ : zΩ ≫ scalarLeg s t v₂ hv₂ D.toBase = z ≫ pullback.snd p p := by
      apply pullback.hom_ext
      · rw [Category.assoc, scalarLeg, pullback.lift_fst, hzΩfst]
        exact congrArg (z ≫ ·) pullback.condition
      · rw [Category.assoc, scalarLeg, pullback.lift_snd,
          ← Category.assoc, hzΩsnd, Category.id_comp]
        rfl
    have hh := congrArg (fun f : SchemeHomOver (D.baseChange Ω).toBase bΩ =>
      zΩ ≫ f.1 ≫ pullback.fst b t) hf
    change zΩ ≫ (factorAt s t v₁ hv₁ D.toBase b ψ).1 ≫ pullback.fst b t =
      zΩ ≫ (factorAt s t v₂ hv₂ D.toBase b ψ).1 ≫ pullback.fst b t at hh
    simp only [factorAt, pullback.lift_fst] at hh
    rw [← Category.assoc zΩ, hz₁, ← Category.assoc zΩ, hz₂] at hh
    simpa only [Category.assoc, e] using hh
  have hequal : ∀ {X : Scheme.{u}} (v₁ v₂ : X ⟶ pullback D.toBase s),
      v₁ ≫ p = v₂ ≫ p → v₁ ≫ e = v₂ ≫ e := by
    intro X v₁ v₂ hv
    have hh := congrArg (pullback.lift v₁ v₂ hv ≫ ·) hpair
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using hh
  let φ : D.P ⟶ B := EffectiveEpi.desc p e hequal
  have hφ : p ≫ φ = e := EffectiveEpi.fac p e hequal
  have hφb : φ ≫ b = D.toBase := by
    apply (cancel_epi p).mp
    rw [← Category.assoc, hφ, heb]
  refine ⟨⟨φ, hφb⟩, ?_⟩
  apply (cancel_epi (pullback.fst c s)).mp
  rw [← Category.assoc, ← fibreRestrictAlong_coe_comp_fst s D.toBase c aj,
    Category.assoc, hφ]
  change (fibreRestrictAlong s D.toBase c aj).1 ≫ ψ.1 ≫ pullback.fst b s =
    pullback.fst c s ≫ q.1
  rw [← Category.assoc, hψ, fibreRestrictAlong_coe_comp_fst]

end JacobianVarieties.Albanese
