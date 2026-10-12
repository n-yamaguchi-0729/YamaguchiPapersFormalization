/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.LineBundleSumBaseChange
import Nyll.JacobianVarieties.Picard.Exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivTwist2
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Modules.Invertible
import Nyll.SchemeTheory.Modules.Monoidal
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Sums on divisor Picard charts over arbitrary fields

At a field-valued test map, rigidification changes a line bundle only by a
trivial line from that test field. Tensor cancellation therefore identifies
the divisor line bundles from an isomorphism of their actual twists.

On a reduced family locally of finite type over any ground field, equality
of sums follows by applying this comparison to points over its algebraic
closure and using actual geometric point density.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Picard.Proofs.OpenChart.AlgebraicGeometry.RelPicard.ChartOne

namespace JacobianVarieties.Albanese

private theorem nonempty_rigidify_iso_over_testField
    {L : Type u} [Field L] {X : Scheme.{u}}
    (σ : Spec (CommRingCat.of L) ⟶ X) (q : X ⟶ Spec (CommRingCat.of L))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Nonempty (Scheme.Modules.rigidify σ q M ≅ M) := by
  obtain ⟨e⟩ := (hM.pullback σ).dual.1.nonempty_iso_tensorUnit_of_isLocalRing
  exact ⟨(Iso.refl M ⊗ᵢ ((Scheme.Modules.pullback q).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso q)) ≪≫ ρ_ M⟩

/-- Over any field-valued test map, isomorphic equal-degree divisor twists
give isomorphic actual divisor line bundles. -/
theorem nonempty_lineBundle_iso_of_twistModule_iso_of_fieldMap
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsSeparated c]
    [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) {r : ℕ}
    (L : Type u) [Field L] (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    (D₀ D₁ : RelEffCartierDiv c r s)
    (e : D₀.twistModule c ε ≅ D₁.twistModule c ε) :
    Nonempty (D₀.lineBundle ≅ D₁.lineBundle) := by
  let F : (pullback c s).Modules := ((sectionIdeal c ε s) ^ r).module
  have hF : Scheme.Modules.IsInvertible F :=
    ((isInvertible_sectionIdeal K c ε s).pow r).isInvertible_module
  have h₀ : Scheme.Modules.IsInvertible (D₀.lineBundle ⊗ F) :=
    D₀.isInvertible_I.isInvertible_invModule.tensor hF
  have h₁ : Scheme.Modules.IsInvertible (D₁.lineBundle ⊗ F) :=
    D₁.isInvertible_I.isInvertible_invModule.tensor hF
  obtain ⟨e₀⟩ := nonempty_rigidify_iso_over_testField
    (rigSection c s ε) (pullback.snd c s) (D₀.lineBundle ⊗ F) h₀
  obtain ⟨e₁⟩ := nonempty_rigidify_iso_over_testField
    (rigSection c s ε) (pullback.snd c s) (D₁.lineBundle ⊗ F) h₁
  let eL : D₀.lineBundle ⊗ F ≅ D₁.lineBundle ⊗ F := e₀.symm ≪≫ e ≪≫ e₁
  obtain ⟨eF⟩ := hF.dual.2
  exact ⟨(ρ_ _).symm ≪≫ (Iso.refl _ ⊗ᵢ eF.symm) ≪≫ (α_ _ _ _).symm ≪≫
    (eL ⊗ᵢ Iso.refl _) ≪≫ (α_ _ _ _) ≪≫ (Iso.refl _ ⊗ᵢ eF) ≪≫ ρ_ _⟩

open AlgebraicCurves.Geometry.Schemes.Proofs
open SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat

open RigKerGeomPoints renaming ext_of_forall_geometric_point → geometricHomExt in
/-- Over every ground field, isomorphic actual divisor twists induce equal
sum morphisms on any reduced family locally of finite type over that field. -/
theorem lift_comp_eq_of_twistModule_iso_of_field
    {K : Type u} [Field K] {C B Y T : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    {r : ℕ} {y : Y ⟶ Spec (CommRingCat.of K)}
    {U : RelEffCartierDiv c r y} (hU : U.IsUniversal)
    {b : B ⟶ Spec (CommRingCat.of K)} [Smooth b] [IsProper b]
    [GeometricallyIntegral b] (G : RelativeGroupLaw K b) (sum : SchemeHomOver y b)
    (t : T ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType t] [IsReduced T]
    (D₀ D₁ : RelEffCartierDiv c r t)
    (e : D₀.twistModule c ε ≅ D₁.twistModule c ε) :
    hU.lift D₀ ≫ sum.1 = hU.lift D₁ ≫ sum.1 := by
  let s : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  apply geometricHomExt (R := K) (L := AlgebraicClosure K)
    (algebraMap K (AlgebraicClosure K)).injective t b
    (hU.lift D₀ ≫ sum.1) (hU.lift D₁ ≫ sum.1)
    (by rw [Category.assoc, sum.2, hU.lift_comp])
    (by rw [Category.assoc, sum.2, hU.lift_comp])
  intro x hx
  let ψ : SchemeHomOver s t := ⟨x, hx⟩
  obtain ⟨e₀⟩ := RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback c ε ψ D₀
  obtain ⟨e₁⟩ := RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback c ε ψ D₁
  let e' : (D₀.pullbackAlong x hx).twistModule c ε ≅
      (D₁.pullbackAlong x hx).twistModule c ε :=
    e₀ ≪≫ (Scheme.Modules.pullback (baseChangeSnd c ψ)).mapIso e ≪≫ e₁.symm
  obtain ⟨eL⟩ := nonempty_lineBundle_iso_of_twistModule_iso_of_fieldMap
    c ε (AlgebraicClosure K) s (D₀.pullbackAlong x hx) (D₁.pullbackAlong x hx) e'
  have h := lift_comp_eq_of_lineBundle_iso_of_fieldMap c hU G sum
    (AlgebraicClosure K) s (D₀.pullbackAlong x hx) (D₁.pullbackAlong x hx) eL
  have hlift (D : RelEffCartierDiv c r t) :
      hU.lift (D.pullbackAlong x hx) = x ≫ hU.lift D := by
    symm
    apply hU.eq_lift (by rw [Category.assoc, hU.lift_comp, hx])
    have hD : U.pullbackAlong (x ≫ hU.lift D)
        (by rw [Category.assoc, hU.lift_comp, hx]) = D.pullbackAlong x hx := by
      rw [← U.pullbackAlong_comp (hU.lift D) (hU.lift_comp D) x hx,
        hU.pullbackAlong_lift]
    exact congrArg RelEffCartierDiv.I hD
  rw [hlift D₀, hlift D₁, Category.assoc, Category.assoc] at h
  exact h

end JacobianVarieties.Albanese
