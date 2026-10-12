/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.OpenDivisorCohomologyInjection
import Nyll.JacobianVarieties.Kummer.OpenGenericRootMembership
import Nyll.EtaleFundamentalGroups.Kummer.GenericCharacterRootCover
import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSeparableComparison
import Nyll.GaloisCohomology.Kummer.Concrete.SeparableKummerH1
import Nyll.GaloisCohomology.Kummer.Concrete.FiniteDualSeparation
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RootsOfUnityFieldEmbedding
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Actual derived Kummer H¹ of an open smooth curve

Every character supplies an actual finite étale generic root cover. The local
étale calculation proves divisibility of orders at all interior points.
The original normalized Kummer cover recovers that character, so the already
constructed injection of actual functions modulo powers is surjective.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory KummerTheory TopologicalSpace
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups.Cohomology
open scoped FintypeCatDiscrete IntermediateField
open ClassFieldTower.Martinet.Shafarevich

namespace AlgebraicCurve.CurveModel.OpenKummer

section Coefficients
variable {K : Type} [Field K] {X : Scheme} [IsIntegral X]
  (c : X ⟶ Spec (.of K)) (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))

private def genericRootCoefficient :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    rootsOfUnity (n : ℕ) K →ₜ*
      DiscreteNthRootsSubgroup (SeparableClosure X.functionField) (n : ℕ) := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let ι := (algebraMap X.functionField (SeparableClosure X.functionField)).comp
    (baseToFunctionField c)
  exact
    { toMonoidHom :=
        (nthRootsSubgroupEquivRootsOfUnity (SeparableClosure X.functionField)
          (n : ℕ)).symm.toMonoidHom.comp (restrictRootsOfUnity ι (n : ℕ))
      continuous_toFun := continuous_of_discreteTopology }

private theorem genericRootCoefficient_coe (ζ : rootsOfUnity (n : ℕ) K) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    ((genericRootCoefficient c n ζ : (SeparableClosure X.functionField)ˣ) :
      SeparableClosure X.functionField) =
        algebraMap X.functionField (SeparableClosure X.functionField)
          (baseToFunctionField c ((ζ : Kˣ) : K)) := rfl

variable [IsAlgClosed K]

include c hn

private theorem genericRootCoefficient_bijective :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    Function.Bijective (genericRootCoefficient c n) := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let ι := (algebraMap X.functionField (SeparableClosure X.functionField)).comp
    (baseToFunctionField c)
  exact (nthRootsSubgroupEquivRootsOfUnity (SeparableClosure X.functionField)
    (n : ℕ)).symm.bijective.comp
      (RamificationTheory.HilbertRamification.restrictRootsOfUnity_bijective_of_primitiveRoot
        ι (n : ℕ) (HasEnoughRootsOfUnity.exists_primitiveRoot K (n : ℕ)))

private theorem functionField_primitiveRoots_nonempty :
    (primitiveRoots (n : ℕ) X.functionField).Nonempty := by
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (n : ℕ)
  refine ⟨baseToFunctionField c ζ, ?_⟩
  exact (mem_primitiveRoots n.pos).mpr
    (hζ.map_of_injective (baseToFunctionField c).injective)


end Coefficients

section GenericComparison
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
  {X : Scheme} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hinterior : ∀ (y : X) (x : closedPoints M.C),
    x.val = j y → M.placeOfPoint x ∉ S)
  (hn : IsUnit ((n : ℕ) : K))

private theorem character_generic_absolute
    (u : Pic0.openKummerUnits K F S n)
    (β : (SeparableClosure X.functionField)ˣ)
    (hβ : (β : SeparableClosure X.functionField) ^ (n : ℕ) =
      algebraMap X.functionField (SeparableClosure X.functionField)
        (j.functionFieldMap hj (M.ffEquiv (u.val : F))))
    (σ : Gal(SeparableClosure X.functionField/X.functionField)) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    (genericRootCoefficient (j ≫ M.toBase) n
      (kummerMonodromyCharacter M S n u j hj hinterior hn
        (X.genericExtensionMorphism (AlgebraicClosure X.functionField))
        (FiniteEtale.genericAbsoluteGaloisHom X σ)) :
          (SeparableClosure X.functionField)ˣ) = rootQuotient β σ := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  let Ωg := SeparableClosure X.functionField
  have : IsSepClosure X.functionField Ωg :=
    separableClosure.isSepClosure X.functionField (AlgebraicClosure X.functionField)
  let xi := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ωg))
  let genericMap := X.fromSpecStalk (genericPoint X)
  let g := FiniteEtale.fundamentalGroupHom genericMap xi
    (toAut (FiniteEtale.fiber xi) Gal(Ωg/X.functionField) σ)
  have hbase := character_basePoint_apply M S n j hj hinterior hn u (xi ≫ genericMap)
    (X.genericExtensionMorphism (AlgebraicClosure X.functionField))
    (FiniteEtale.genericSeparableFiberIso X) g
  have hg := FiniteEtale.genericAbsoluteGaloisHom_eq_separable X σ
  have hχ : kummerMonodromyCharacter M S n u j hj hinterior hn
      (X.genericExtensionMorphism (AlgebraicClosure X.functionField))
      (FiniteEtale.genericAbsoluteGaloisHom X σ) =
        kummerMonodromyCharacter M S n u j hj hinterior hn (xi ≫ genericMap) g := by
    rw [hg]
    exact hbase
  apply Units.ext
  simp only [rootQuotient, AlgEquiv.smul_units_def, Units.val_div_eq_div_val, Units.coe_map]
  rw [genericRootCoefficient_coe, hχ]
  apply (eq_div_iff β.ne_zero).mpr
  exact kummerMonodromyCharacter_generic_mul_root M S n u j hj hinterior (β : Ωg) hβ hn σ

end GenericComparison

section Surjectivity
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (n : ℕ+)
  {X : Scheme} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)

/-- Surjectivity for the actual open curve and its actual omitted places. -/
theorem kummerMonodromyCharacter_surjective :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    Function.Surjective (fun u : Pic0.openKummerUnits K F (M.openBoundaryPlaces j) n =>
      kummerMonodromyCharacter M (M.openBoundaryPlaces j) n u j hj
        (M.place_not_mem_openBoundaryPlaces j) hn xi) := by
  intro tμ χ
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : Smooth (j ≫ M.toBase) := inferInstance
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral X := IsNormalIntegral.of_stalks X
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk (j ≫ M.toBase) x).2)
  have hnf : IsUnit ((n : ℕ) : X.functionField) := by
    simpa only [map_natCast] using hn.map (baseToFunctionField (j ≫ M.toBase))
  have : NeZero ((n : ℕ) : X.functionField) := ⟨hnf.ne_zero⟩
  let S := M.openBoundaryPlaces j
  let hi := M.place_not_mem_openBoundaryPlaces j
  let E := M.ffEquiv.trans j.functionFieldRingEquivOfIsOpenImmersion
  let xig := X.genericExtensionMorphism (AlgebraicClosure X.functionField)
  let t := Classical.choice (FiniteEtale.nonempty_fiber_iso xig xi)
  let b := FiniteEtale.fundamentalGroupIsoOfFiberIso xig xi t
  let χg := (genericRootCoefficient (j ≫ M.toBase) n).comp
    (χ.comp (ContinuousMonoidHom.toContinuousMonoidHom b))
  obtain ⟨a, β, hβ, hχ, Y, f, hfinite, hetale, e, he⟩ :=
    EtaleFundamentalGroups.Kummer.exists_finiteEtale_genericKummerRoot X n
      (functionField_primitiveRoots_nonempty (j ≫ M.toBase) n hn) χg
  have : IsFinite f := hfinite
  have : Etale f := hetale
  let L : IntermediateField X.functionField (SeparableClosure X.functionField) :=
    X.functionField⟮(β : SeparableClosure X.functionField)⟯
  let βL : L := ⟨(β : SeparableClosure X.functionField),
    IntermediateField.mem_adjoin_simple_self X.functionField
      (β : SeparableClosure X.functionField)⟩
  have hβval : (β : SeparableClosure X.functionField) ^ (n : ℕ) =
      algebraMap X.functionField (SeparableClosure X.functionField) (a : X.functionField) :=
    congrArg (fun z : (SeparableClosure X.functionField)ˣ =>
      (z : SeparableClosure X.functionField)) hβ
  have hβL : βL ^ (n : ℕ) = algebraMap X.functionField L (a : X.functionField) := by
    apply Subtype.ext
    exact hβval
  let u : Pic0.openKummerUnits K F S n :=
    ⟨Units.map E.symm.toMonoidHom a,
      M.mem_openKummerUnits_of_finiteEtale_generic_root j L f e he a βL n hβL⟩
  have hu : j.functionFieldMap hj (M.ffEquiv (u.val : F)) = (a : X.functionField) :=
    E.apply_symm_apply (a : X.functionField)
  have hroot : (β : SeparableClosure X.functionField) ^ (n : ℕ) =
      algebraMap X.functionField (SeparableClosure X.functionField)
        (j.functionFieldMap hj (M.ffEquiv (u.val : F))) := by
    rw [hu]
    exact hβval
  refine ⟨u, ?_⟩
  apply ContinuousMonoidHom.ext
  intro g
  obtain ⟨g0, hg0⟩ := b.surjective g
  obtain ⟨σ, hσ⟩ := FiniteEtale.genericAbsoluteGaloisHom_surjective X g0
  rw [← hg0, ← hσ]
  apply (genericRootCoefficient_bijective (j ≫ M.toBase) n hn).injective
  apply Subtype.ext
  have hbase := character_basePoint_apply M S n j hj hi hn u xig xi t
    (FiniteEtale.genericAbsoluteGaloisHom X σ)
  change (genericRootCoefficient (j ≫ M.toBase) n
    (kummerMonodromyCharacter M S n u j hj hi hn xi
      (b (FiniteEtale.genericAbsoluteGaloisHom X σ))) :
        (SeparableClosure X.functionField)ˣ) = _
  rw [hbase]
  exact (character_generic_absolute M S n j hj hi hn u β hroot σ).trans (hχ σ).symm

/-- Every actual derived H¹ class is represented by a function unramified
at the actual interior places. -/
theorem quotientCohomology_surjective :
    Function.Surjective (quotientCohomology M (M.openBoundaryPlaces j) n j hj
      (M.place_not_mem_openBoundaryPlaces j) hn xi) := by
  intro a
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  obtain ⟨u, hu⟩ := kummerMonodromyCharacter_surjective M n j hj hn xi
    (finiteH1CharacterEquiv A xi a).toMul
  refine ⟨Additive.ofMul (QuotientGroup.mk u), ?_⟩
  rw [quotientCohomology_mk]
  change (finiteH1CharacterEquiv A xi).symm
    (Additive.ofMul (kummerMonodromyCharacter M (M.openBoundaryPlaces j) n u j hj
      (M.place_not_mem_openBoundaryPlaces j) hn xi)) = a
  exact (congrArg
    (fun ψ : Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative A =>
      (finiteH1CharacterEquiv A xi).symm (Additive.ofMul ψ)) hu).trans
      ((finiteH1CharacterEquiv A xi).symm_apply_apply a)

/-- The actual divisorial quotient is actual finite-coefficient derived
étale H¹ of the open curve, via its original Kummer covers. -/
def quotientCohomologyEquiv :
    Additive (Pic0.openKummerUnits K F (M.openBoundaryPlaces j) n ⧸
      Pic0.openKummerPowers K F (M.openBoundaryPlaces j) n) ≃+
      Sheaf.H.{0} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1 :=
  AddEquiv.ofBijective
    (quotientCohomology M (M.openBoundaryPlaces j) n j hj
      (M.place_not_mem_openBoundaryPlaces j) hn xi)
    ⟨quotientCohomology_injective M (M.openBoundaryPlaces j) n j hj
      (M.place_not_mem_openBoundaryPlaces j) hn xi,
      quotientCohomology_surjective M n j hj hn xi⟩

end Surjectivity
end AlgebraicCurve.CurveModel.OpenKummer
