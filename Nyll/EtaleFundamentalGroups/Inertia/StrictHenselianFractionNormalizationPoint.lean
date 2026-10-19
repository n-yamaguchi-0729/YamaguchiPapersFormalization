/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.FractionFieldSpecNormalization
import Nyll.SchemeTheory.RingTheory.Henselian.StrictHenselianFiniteDomainPointLift
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# A fixed geometric point on a strict-Henselian fraction-cover normalization

The actual function field of a connected finite etale cover is finite
separable over the fraction field. Its integral closure is therefore a finite
domain over the strict-Henselian DVR. A point over the prescribed closed
geometric point is constructed in the same algebraically closed field, then
transported through the actual function-field normalization isomorphism.
Every deck transformation fixes this point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The normalization of a connected finite etale fraction-field cover over
a strict-Henselian DVR has a closed geometric point fixed by every deck
transformation, over the originally specified algebraically closed field. -/
theorem exists_fractionCover_normalizationPoint_fixed_of_strictHenselian
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (Y : FiniteEtale (Spec (.of K))) [IsConnected Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (ψ : R →+* Ω) [IsLocalHom ψ] :
    ∃ z : Spec (.of Ω) ⟶ ((show Y.left ⟶ Spec (.of K) from Y.hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K))).normalization,
      z ≫ ((show Y.left ⟶ Spec (.of K) from Y.hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K))).fromNormalization =
          Spec.map (CommRingCat.ofHom ψ) ∧
      ∀ σ : Aut Y, z ≫ normalizationEndomorphism
        ((show Y.left ⟶ Spec (.of K) from Y.hom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R K))) σ.hom.left
        (by
          rw [← Category.assoc]
          exact congrArg
            (fun k => k ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) σ.hom.w) = z := by
  let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
  let : IsNormalIntegral Y.left := isNormalIntegral_left_of_isConnected_finiteEtale Y
  let : IsAffine Y.left := isAffine_of_isAffineHom (show Y.left ⟶ Spec (.of K) from Y.hom)
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let f : Y.left ⟶ Spec (.of R) := (show Y.left ⟶ Spec (.of K) from Y.hom) ≫ g
  let F := (Spec (.of K)).functionField
  let L := Y.left.functionField
  let : Algebra F L := finiteEtaleFunctionFieldAlgebra Y
  let : Algebra R F := affineMorphismFunctionFieldAlgebra R g
  let : Algebra R L := affineMorphismFunctionFieldAlgebra R f
  let : IsScalarTower R F L := finiteEtaleMorphism_functionField_isScalarTower R g Y
  let : IsFractionRing R F := affineMorphismFunctionFieldAlgebra_isFractionRing R K
  let : FiniteDimensional F L := finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let : Algebra.IsSeparable F L := isSeparable_functionField_of_finiteEtale_isConnected Y
  let : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R F L (integralClosure R L)
  obtain ⟨φ, _hφlocal, hφbase, hφfixed⟩ :=
    SchemeTheory.exists_local_hom_finiteDomain_fixed_of_strictHenselian
      R (integralClosure R L) ψ
  let e := affineMorphismFunctionFieldNormalizationIso R f
  let z := Spec.map (CommRingCat.ofHom φ) ≫ e.inv
  refine ⟨z, ?_, ?_⟩
  · change z ≫ f.fromNormalization = Spec.map (CommRingCat.ofHom ψ)
    rw [← affineMorphismFunctionFieldNormalizationIso_hom_base R f]
    dsimp only [z]
    rw [Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
    exact congrArg (fun k => Spec.map (CommRingCat.ofHom k)) hφbase
  · intro σ
    let s : Y.left ≅ Y.left :=
      (FiniteEtale.forget (Spec (.of K)) ⋙ Over.forget (Spec (.of K))).mapIso σ
    have hs : s.hom ≫ f = f := by
      have hw : σ.hom.left ≫ (show Y.left ⟶ Spec (.of K) from Y.hom) =
          (show Y.left ⟶ Spec (.of K) from Y.hom) := σ.hom.w
      exact (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ g) hw)
    apply (affineMorphismFunctionFieldNormalizationIso_fixes_iff R f s hs z).mp
    have hfixed := hφfixed (affineMorphismFunctionFieldAlgEquiv R f s hs).mapIntegralClosure
    have hz : z ≫ e.hom = Spec.map (CommRingCat.ofHom φ) := by
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun k => Spec.map (CommRingCat.ofHom φ) ≫ k)
          (Iso.inv_hom_id e)).trans (Category.comp_id _))
    rw [hz, ← Spec.map_comp]
    exact congrArg (fun k => Spec.map (CommRingCat.ofHom k)) hfixed

end EtaleFundamentalGroups.Inertia
