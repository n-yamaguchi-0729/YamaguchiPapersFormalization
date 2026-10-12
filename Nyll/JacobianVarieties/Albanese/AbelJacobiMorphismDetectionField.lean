/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Albanese.AbelJacobiHomDetectionField
import Nyll.JacobianVarieties.Picard.Designation
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.SchemeTheory.Modules.Monoidal

/-!
# Uniqueness of pointed Abel–Jacobi factorizations over any field

The actual Picard representation supplies an Abel–Jacobi map for which a pointed
map into an abelian variety has at most one factorization among all scheme
morphisms. Each candidate preserves the identity because its restriction to the
curve is pointed. Rigidity then proves multiplication preservation on every test
scheme, so Abel–Jacobi homomorphism detection applies over an algebraic closure.

The group law and Abel–Jacobi map are the same witnesses supplied by the existing
arbitrary-field construction. No characteristic or genus restriction is imposed.
This theorem proves uniqueness; existence of a factorization is a separate claim.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.RelPicard

/-- The constructed Abel–Jacobi map admits at most one scheme-morphism
factorization of any pointed map to an abelian variety, over any field. -/
theorem exists_abelJacobi_detects_pointed_factorizations_of_field
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
      ∀ (B : Scheme.{u}) (b : B ⟶ Spec (CommRingCat.of K))
        (G : RelativeGroupLaw K b), AbelianSchemePropertyBundle K b →
        ∀ (q : SchemeHomOver c b),
          NeronModelInfra.schemeHomOverComp ε q =
            G.one (𝟙 (Spec (CommRingCat.of K))) →
          ∀ (φ ψ : SchemeHomOver D.toBase b),
            aj.1 ≫ φ.1 = q.1 → aj.1 ≫ ψ.1 = q.1 → φ = ψ := by
  obtain ⟨L, aj, hA, hone, haj, hclass, hdetect⟩ :=
    exists_abelJacobi_detects_hom_of_field K c ε D hD hsm hpr hgc
  have : Smooth D.toBase := hsm
  have : IsProper D.toBase := hpr
  have : GeometricallyConnected D.toBase := hgc
  have : ConnectedSpace D.P :=
    GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
  refine ⟨L, aj, hA, hone, haj, hclass, ?_⟩
  intro B b G hB q hq φ ψ hφ hψ
  have : IsProper b := hB.proper
  have preserves_mul (θ : SchemeHomOver D.toBase b) (hθ : aj.1 ≫ θ.1 = q.1) :
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp (L.mul t x y) θ =
          G.mul t (NeronModelInfra.schemeHomOverComp x θ)
            (NeronModelInfra.schemeHomOverComp y θ) := by
    have hzero :
        NeronModelInfra.schemeHomOverComp (L.one (𝟙 (Spec (CommRingCat.of K)))) θ =
          G.one (𝟙 (Spec (CommRingCat.of K))) := by
      apply Subtype.ext
      change (L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ θ.1 =
        (G.one (𝟙 (Spec (CommRingCat.of K)))).1
      rw [hone, ← haj, Category.assoc, hθ]
      exact congrArg Subtype.val hq
    intro T t x y
    exact L.comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
      K G hB θ hzero t x y
  let t : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  exact hdetect (AlgebraicClosure K) B b (inferInstanceAs (IsSeparated b)) G φ ψ
    (preserves_mul φ hφ t) (preserves_mul ψ hψ t) (hφ.trans hψ.symm)

end AlgebraicGeometry.RelPicard
