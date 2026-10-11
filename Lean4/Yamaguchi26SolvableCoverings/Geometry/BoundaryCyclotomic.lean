/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26SolvableCoverings.Geometry.BoundaryInertia
import EtaleFundamentalGroups.Inertia.CartierStalkNormalizationPoint
import EtaleFundamentalGroups.Inertia.GaloisNormalizationPointLift
import EtaleFundamentalGroups.Inertia.FiniteEtaleNormalizationPoint
import EtaleFundamentalGroups.Inertia.FractionFieldSpecNormalization
import EtaleFundamentalGroups.FiniteEtale.Boundary.ComponentGenericResidue
import EtaleFundamentalGroups.LocalGeometry.HeightOne.CartierComponentStalkDVR
import SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.DVRCyclotomicInversion
import EtaleFundamentalGroups.GeometricFiber.RegularBoundarySurjective
import SchemeTheory.FunctionFields.PlainIntegerBase
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Ideal.Over

/-!
# Cyclotomic inversion for the actual boundary normalization stabilizer

A prescribed normalization point is transported to the discrete valuation
stalk at the component's generic point. The connected component through that
point supplies a genuine finite Galois extension of the local fraction field.
Local cyclotomic inversion then descends through the actual component quotient
to the original deck transformation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups EtaleFundamentalGroups.Inertia

namespace Yamaguchi26SolvableCoverings

private theorem integralClosurePoint_liesOver
    {R L Ω : Type} [CommRing R] [Field L] [Field Ω] [Algebra R L]
    (φ : integralClosure R L →+* Ω) (y : Spec (.of Ω) ⟶ Spec (.of R))
    (hy : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (integralClosure R L))) = y) :
    (RingHom.ker φ).LiesOver (y (IsLocalRing.closedPoint Ω)).asIdeal := by
  constructor
  rw [← hy]
  change Ideal.comap (algebraMap R (integralClosure R L))
    (Ideal.comap φ (IsLocalRing.maximalIdeal Ω)) =
      Ideal.comap (algebraMap R (integralClosure R L)) (RingHom.ker φ)
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

variable {X : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]

/-- Each element fixing a geometric normalization point above a horizontal
component with geometrically integral generic fibre is conjugate to its inverse
in the opposite deck group of the actual finite Galois cover. -/
theorem finiteCoverInertia_isConj_inv
    (D : X.EffectiveCartierDivisor) (hhor : IsHorizontal D)
    (hreg : D.IsAmbientRegularAlongSupport)
    (hgeom : HasGeometricallyIntegralGenericComponents D.1) :
    let : ConnectedSpace D.1.supportComplement := boundaryComplement_connectedSpace D hreg
    ∀ (W : FiniteEtale D.1.supportComplement) (_hW : IsGalois W)
      (E : Component D)
      (z : Spec (.of (AlgebraicClosure (X.residueField (componentPoint D E)))) ⟶
        (W.hom ≫ D.1.supportComplement.ι).normalization),
      z ≫ (W.hom ≫ D.1.supportComplement.ι).fromNormalization =
        componentGeometricPoint D E →
      ∀ σ : finiteCoverInertia D W E z,
        IsConj (MulOpposite.op (σ : Aut W)) (MulOpposite.op (σ : Aut W))⁻¹ := by
  intro hConnected
  let : ConnectedSpace D.1.supportComplement := hConnected
  intro W hW E z hz σ
  let x := componentPoint D E
  have hx_eq : D.1.componentGenericPoint E.val E.property = x :=
    D.1.componentGenericPoint_eq E.val E.property
  let R : Type := X.presheaf.stalk x
  have hLocal : ∃ hDomain : IsDomain R,
      let : IsDomain R := hDomain
      IsDiscreteValuationRing R := by
    apply Eq.mp (congrArg (fun q : X => ∃ hDomain : IsDomain (X.presheaf.stalk q),
      let : IsDomain (X.presheaf.stalk q) := hDomain
      IsDiscreteValuationRing (X.presheaf.stalk q)) hx_eq)
    exact ⟨isDomain_stalk_componentGenericPoint D hreg E.val E.property,
      isDiscreteValuationRing_stalk_componentGenericPoint D hreg E.val E.property⟩
  obtain ⟨hDomain, hDVR⟩ := hLocal
  let : IsDomain R := hDomain
  let : IsDiscreteValuationRing R := hDVR
  have hx : x ∈ D.1.support := hx_eq ▸ D.1.componentGenericPoint_mem_support E.val E.property
  let Ω := AlgebraicClosure (X.residueField x)
  let y : Spec (.of Ω) ⟶ Spec (X.presheaf.stalk x) :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) Ω)) ≫ Spec.map (X.residue x)
  have hy : y ≫ X.fromSpecStalk x = componentGeometricPoint D E :=
    Category.assoc _ _ _
  have hyideal : (y (IsLocalRing.closedPoint Ω)).asIdeal = IsLocalRing.maximalIdeal R := by
    change (Spec.map (X.residue x)
      (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) Ω))
        (IsLocalRing.closedPoint Ω))).asIdeal = _
    exact congrArg PrimeSpectrum.asIdeal (Scheme.SpecMap_residue_apply x _)
  obtain ⟨qA, hqA, hfixA⟩ := exists_fractionStalk_normalizationPoint D.1 D.2 x hx W z y
    (hz.trans hy.symm)
  let F := FractionRing R
  let c := D.2.fractionStalkToSupportComplement x
  let a : Spec (.of F) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R F))
  let xi : Spec (.of (AlgebraicClosure F)) ⟶ Spec (.of F) :=
    Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)))
  obtain ⟨Z, i, qZ, zZ, w, hi, hZ, hiz, hqZ, hlift⟩ :=
    exists_galoisComponent_normalizationPoint_fixed_lift c xi W hW a qA
  let : Mono i := hi
  let : IsGalois Z := hZ
  let : IsIntegral Z.left := isIntegral_left_of_isConnected_finiteEtale Z
  let K := (Spec (.of F)).functionField
  let L := Z.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Z
  let : Algebra R K := affineMorphismFunctionFieldAlgebra R a
  let : Algebra R L := affineMorphismFunctionFieldAlgebra R
    ((show Z.left ⟶ Spec (.of F) from Z.hom) ≫ a)
  let : IsScalarTower R K L := finiteEtaleMorphism_functionField_isScalarTower R a Z
  let : IsFractionRing R K := affineMorphismFunctionFieldAlgebra_isFractionRing R F
  let : FiniteDimensional K L := finiteDimensional_functionField_of_finiteEtale_isConnected Z
  let : _root_.IsGalois K L := isGalois_functionField_of_isGalois_finiteEtale Z hZ
  obtain ⟨φ, hφbase, hφfix⟩ :=
    exists_finiteEtaleMorphism_normalizationPoint_inertia_iff R a Z qZ
  let Q := RingHom.ker φ
  have : Q.IsPrime := RingHom.ker_isPrime φ
  have : Q.LiesOver (IsLocalRing.maximalIdeal R) := by
    have h : Q.LiesOver (y (IsLocalRing.closedPoint Ω)).asIdeal :=
      integralClosurePoint_liesOver (R := R) (L := L) (Ω := Ω)
        φ y (hφbase.trans (hqZ.trans hqA))
    exact Eq.mp (congrArg (fun P : Ideal R => Q.LiesOver P) hyideal) h
  let k : Type := (Spec (.of ℤ)).residueField (genericPoint (Spec (.of ℤ)))
  have hres : ∃ hAlg : Algebra k (X.residueField x),
      let : Algebra k (X.residueField x) := hAlg
      GeometricallyIntegral (Spec.map (CommRingCat.ofHom
        (algebraMap k (X.residueField x)))) := by
    apply Eq.mp (congrArg (fun q : X => ∃ hAlg : Algebra k (X.residueField q),
      let : Algebra k (X.residueField q) := hAlg
      GeometricallyIntegral (Spec.map (CommRingCat.ofHom
        (algebraMap k (X.residueField q))))) hx_eq)
    exact D.1.componentGenericPoint_exists_geometricallyIntegralResidueAlgebra
      (toIntegers X) E.val E.property (hhor E.val E.property) (hgeom E.val E.property)
  obtain ⟨hAlg, hfield⟩ := hres
  let : Algebra k (IsLocalRing.ResidueField R) := hAlg
  have hσfixed : z ≫ normalizationEndomorphism (W.hom ≫ D.1.supportComplement.ι)
      σ.val.hom.left (by
        rw [← Category.assoc]
        exact congrArg (fun t => t ≫ D.1.supportComplement.ι) σ.val.hom.w) = z := σ.property
  obtain ⟨τ, hτimage, hτfixed⟩ := hlift σ.val ((hfixA σ.val).mpr hσfixed)
  have hτmem : finiteEtaleAutFunctionFieldAlgEquiv Z τ ∈ Q.inertia Gal(L/K) :=
    (hφfix τ).mpr hτfixed
  have hτmemLocal :
      let : MulSemiringAction Gal(L/K) (integralClosure R L) :=
        IsIntegralClosure.MulSemiringAction R K L (integralClosure R L)
      finiteEtaleAutFunctionFieldAlgEquiv Z τ ∈ Q.toAddSubgroup.inertia Gal(L/K) := by
    have hcanonical := Ideal.mem_inertia.mp hτmem
    have hsmul (b : integralClosure R L) :
        (galRestrict R K L (integralClosure R L)) (finiteEtaleAutFunctionFieldAlgEquiv Z τ) b =
          (finiteEtaleAutFunctionFieldAlgEquiv Z τ) • b := by
      apply Subtype.ext
      exact algebraMap_galRestrict_apply R (finiteEtaleAutFunctionFieldAlgEquiv Z τ) b
    intro hAction
    apply Ideal.mem_inertia.mpr
    intro b
    change (galRestrict R K L (integralClosure R L))
      (finiteEtaleAutFunctionFieldAlgEquiv Z τ) b - b ∈ Q
    rw [hsmul b]
    exact hcanonical b
  have hconj :=
    (open _root_.TameAbhyankar.SGA1 in
      idealInertia_isConj_inv_of_geometricallyIntegral_dvrNormalizationResidue_of_ratEquiv
        k specZGenericResidueFieldEquivQ (A := R) (K := K) (L := L) Q hfield
          ⟨finiteEtaleAutFunctionFieldAlgEquiv Z τ, hτmemLocal⟩)
  let e : (Aut Z)ᵐᵒᵖ ≃* Gal(L/K) := finiteEtaleAutOpFunctionFieldMulEquiv Z hZ
  let μ : Gal(L/K) →* (Aut W)ᵐᵒᵖ :=
    (FiniteEtale.galoisPullbackComponentQuotientMonoidHom c xi W hW w Z i zZ hiz hZ hi).comp
      e.symm.toMonoidHom
  have hμ : μ (finiteEtaleAutFunctionFieldAlgEquiv Z τ) = MulOpposite.op σ.val := by
    change (FiniteEtale.galoisPullbackComponentQuotientMonoidHom c xi W hW w Z i zZ hiz hZ hi)
      (e.symm (e (MulOpposite.op τ))) = _
    rw [e.symm_apply_apply]
    exact hτimage
  have hconj' : IsConj (finiteEtaleAutFunctionFieldAlgEquiv Z τ)
      (finiteEtaleAutFunctionFieldAlgEquiv Z τ)⁻¹ := hconj
  have h := μ.map_isConj hconj'
  simpa only [map_inv, hμ] using h

end Yamaguchi26SolvableCoverings
