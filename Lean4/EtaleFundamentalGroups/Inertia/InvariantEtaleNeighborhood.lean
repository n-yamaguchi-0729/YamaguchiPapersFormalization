/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GenericTensor.FilteredColimit.CoconeLeg
import EtaleFundamentalGroups.Inertia.HenselianIntegralFiberDecomposition
import EtaleFundamentalGroups.Inertia.HenselianIntegralFiberAction
import EtaleFundamentalGroups.Inertia.EquivariantIdempotentDescent
import EtaleFundamentalGroups.Inertia.InvariantBaseChange
import EtaleFundamentalGroups.Inertia.HenselianInvariantProjection
import EtaleFundamentalGroups.Inertia.InvariantFlatBaseChange
import EtaleFundamentalGroups.Inertia.InvariantEtaleFactorNeighborhood
import SchemeTheory.RingTheory.Descent.EtaleOpenImage
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkIdempotentDescent
import EtaleFundamentalGroups.StrictHenselian.OriginalPrimeLift
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# Principal étale neighborhoods in inertia-fixed algebras

The actual geometric stalk supplies a finite family of isolating idempotents.
Descending this family and its action to an étale neighborhood constructs a
principal étale neighborhood in the original inertia-fixed algebra, avoiding
the contracted prime.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
open EtaleFundamentalGroups.StrictHenselian EtaleFundamentalGroups.Inertia

namespace EtaleFundamentalGroups.Inertia

universe u w

private theorem flatCoefficient_selectedFactor
    {B : CommRingCat.{u}} {R : Type u} [CommRing R] [Algebra B R]
    {G : Type w} [Group G] [Finite G] [MulSemiringAction G R]
    [SMulCommClass G B R] [Algebra.IsInvariant B R G]
    (C : Under B) [Module.Flat B C]
    {ι : Type u} [Fintype ι] (σ : G →* Equiv.Perm ι)
    (e : ι → (C ⊗[B] R)) (he : CompleteOrthogonalIdempotents e)
    (hinj : Function.Injective (algebraMap B R)) :
    let : MulSemiringAction G (C ⊗[B] R) := baseChangeAction B C R G
    let : SMulCommClass G C (C ⊗[B] R) := baseChangeAction_smulCommClass B C R G
    (∀ (g : G) (i : ι), g • e i = e (σ g i)) →
    ∀ i : ι, (∀ j : ι, ∃ g : G, σ g i = j) →
      let eH : FixedPoints.subalgebra C (C ⊗[B] R) (MulAction.stabilizer G (e i)) :=
        ⟨e i, fun g => g.property⟩
      Function.Bijective (algebraMap C (Localization.Away eH)) ∧
        Algebra.Etale C (Localization.Away eH) := by
  intro actualAction actualComm hσ i htrans eH
  have : Algebra.IsInvariant C (C ⊗[B] R) G := baseChangeAction_isInvariant B C R G
  have hbij : Function.Bijective (algebraMap C (Localization.Away eH)) :=
    algebraMap_away_bijective_of_transitive_completeOrthogonalIdempotents C (C ⊗[B] R) G
      σ e he hσ i htrans (Algebra.TensorProduct.includeLeft_injective (R := B) (S := C) hinj)
  exact ⟨hbij, Algebra.Etale.of_equiv
    (AlgEquiv.ofBijective (Algebra.ofId C (Localization.Away eH)) hbij)⟩

private theorem selectedFactor_exists_etale_away
    {B : CommRingCat.{u}} {R : Type u} [CommRing R] [Algebra B R]
    {G : Type w} [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G B R]
    (C : Under B) [Algebra.Etale B C] :
    let : MulSemiringAction G (C ⊗[B] R) := baseChangeAction B C R G
    let : SMulCommClass G C (C ⊗[B] R) := baseChangeAction_smulCommClass B C R G
    ∀ (Q : PrimeSpectrum (C ⊗[B] R)) (e : FixedPoints.subalgebra C (C ⊗[B] R) G),
      (e : C ⊗[B] R) ∉ Q.asIdeal → Algebra.Etale C (Localization.Away e) →
      ∃ f : FixedPoints.subalgebra B R G,
        f ∉ (PrimeSpectrum.comap
          ((Algebra.TensorProduct.includeRight (R := B) (A := C) (B := R)).toRingHom.comp
            (FixedPoints.subalgebra B R G).val.toRingHom) Q).asIdeal ∧
          Algebra.Etale B (Localization.Away f) := by
  intro actualAction actualComm Q e he hfactor
  let S := FixedPoints.subalgebra B R G
  let K := Localization.Away e
  let : Algebra S K := (invariantFlatBaseChangeFactorMap B C R G e).toAlgebra
  have : IsScalarTower B S K := IsScalarTower.of_algebraMap_eq (fun b =>
    (IsScalarTower.algebraMap_apply B C K b).trans
      (RingHom.congr_fun (invariantFlatBaseChangeFactorMap_comp_algebraMap B C R G e) b).symm)
  have : Algebra.Etale S K := invariantFlatBaseChangeFactorMap_etale B C R G e
  have : Algebra.Etale C K := hfactor
  have : Algebra.Etale B K := Algebra.Etale.comp B C K
  obtain ⟨P, hP⟩ := invariantFactorNeighborhood_exists_point B C R G Q e he
  exact SchemeTheory.exists_etale_away_of_mem_image_etale_source B S K
    (PrimeSpectrum.comap
      ((Algebra.TensorProduct.includeRight (R := B) (A := C) (B := R)).toRingHom.comp
        (FixedPoints.subalgebra B R G).val.toRingHom) Q) ⟨P, hP⟩

section CoefficientFamilies

variable {B : CommRingCat.{u}} {R : Type u} [CommRing R] [Algebra B R]
  {G : Type w} [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G B R]

attribute [local instance] coefficientTensorAction baseChangeAction_smulCommClass

private theorem etaleCoefficient_family
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : B →+* Ω)
    {ι : Type u} [Fintype ι] (σ : G →* Equiv.Perm ι)
    (e : ι → ((geometricStalkSmallAlgebraCocone φ).pt ⊗[B] R))
    (he : CompleteOrthogonalIdempotents e)
    (hσ : ∀ (g : G) (i : ι), g • e i = e (σ g i)) :
    ∃ C : Under B, Algebra.Etale B C ∧
      ∃ (γ : C ⟶ (geometricStalkSmallAlgebraCocone φ).pt) (eC : ι → (C ⊗[B] R)),
        CompleteOrthogonalIdempotents eC ∧
          (∀ (g : G) (i : ι), g • eC i = eC (σ g i)) ∧
          ∀ i, Algebra.TensorProduct.map (CommRingCat.toAlgHom γ) (AlgHom.id B R) (eC i) = e i := by
  obtain ⟨V, v, hV, eV, heV, hσV, hmap⟩ :=
    geometricStalk_exists_affine_equivariant_completeOrthogonalIdempotents φ σ e he hσ
  have : IsAffine V.left := hV
  refine ⟨geometricNeighborhoodAlgebra B V, ?_, geometricNeighborhoodGerm φ V v,
    eV, heV, hσV, hmap⟩
  change (V.hom.appTop.hom.comp (Scheme.ΓSpecIso B).inv.hom).Etale
  apply RingHom.Etale.stableUnderComposition
  · exact RingHom.Etale.of_bijective
      ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso B).inv).mp inferInstance)
  · exact HasRingHomProperty.appTop (P := @Etale)
      (show V.left ⟶ Spec B from V.hom) inferInstance

private theorem algebraic_inertiaNeighborhood
    [Algebra.IsInvariant B R G]
    (A C : Under B) [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
    [Module.Flat B A] [Algebra.Etale B C] (γ : C ⟶ A)
    (hfinite : ((IsLocalRing.maximalIdeal A).primesOver (A ⊗[B] R)).Finite)
    [Fintype ((IsLocalRing.maximalIdeal A).primesOver (A ⊗[B] R))]
    (e : ((IsLocalRing.maximalIdeal A).primesOver (A ⊗[B] R)) → (A ⊗[B] R))
    (he : CompleteOrthogonalIdempotents e)
    (hsupp : ∀ (q : (IsLocalRing.maximalIdeal A).primesOver (A ⊗[B] R)) (Q : Ideal (A ⊗[B] R)),
      Q.IsPrime → Q.LiesOver (IsLocalRing.maximalIdeal A) → (e q ∉ Q ↔ Q = q.val))
    (eC : ((IsLocalRing.maximalIdeal A).primesOver (A ⊗[B] R)) → (C ⊗[B] R))
    (heC : CompleteOrthogonalIdempotents eC)
    (hσC : ∀ (g : G) (q : (IsLocalRing.maximalIdeal A).primesOver (A ⊗[B] R)),
      g • eC q = eC (primeFiberPermutation A (A ⊗[B] R) G (IsLocalRing.maximalIdeal A) g q))
    (hmap : ∀ q, Algebra.TensorProduct.map (CommRingCat.toAlgHom γ) (AlgHom.id B R) (eC q) = e q)
    (q : (IsLocalRing.maximalIdeal A).primesOver (A ⊗[B] R))
    (hinj : Function.Injective (algebraMap B R)) :
    ∃ f : FixedPoints.subalgebra B R (q.val.inertia G),
      f ∉ (PrimeSpectrum.comap
        ((Algebra.TensorProduct.includeRight (R := B) (A := A) (B := R)).toRingHom.comp
          (FixedPoints.subalgebra B R (q.val.inertia G)).val.toRingHom)
        ⟨q.val, inferInstance⟩).asIdeal ∧ Algebra.Etale B (Localization.Away f) := by
  have : Algebra.IsInvariant A (A ⊗[B] R) G := baseChangeAction_isInvariant B A R G
  have : Algebra.IsIntegral A (A ⊗[B] R) := Algebra.IsInvariant.isIntegral A (A ⊗[B] R) G
  have hstab : MulAction.stabilizer G (eC q) = q.val.inertia G :=
    isolatingIdempotent_stabilizer_eq_inertia_of_map A (A ⊗[B] R) G hfinite
      (Algebra.TensorProduct.map (CommRingCat.toAlgHom γ) (AlgHom.id B R)).toRingHom
      (fun (g : G) (x : C ⊗[B] R) => baseChangeAction_map B C R G (CommRingCat.toAlgHom γ) g x)
      q eC (fun g => hσC g q) (e q) (he.idem q) (hsupp q) (hmap q)
  rw [← hstab]
  let eH : FixedPoints.subalgebra C (C ⊗[B] R) (MulAction.stabilizer G (eC q)) :=
    ⟨eC q, fun g => g.property⟩
  have hfactor : Function.Bijective (algebraMap C (Localization.Away eH)) ∧
      Algebra.Etale C (Localization.Away eH) := by
    apply flatCoefficient_selectedFactor C
      (primeFiberPermutation A (A ⊗[B] R) G (IsLocalRing.maximalIdeal A)) eC heC hinj hσC q
    intro q'
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A (A ⊗[B] R) G q.val q'.val
      ((q.val.over_def (IsLocalRing.maximalIdeal A)).symm.trans
        (q'.val.over_def (IsLocalRing.maximalIdeal A)))
    exact ⟨g, Subtype.ext hg.symm⟩
  have heQ : (eH : C ⊗[B] R) ∉ (PrimeSpectrum.comap
      (Algebra.TensorProduct.map (CommRingCat.toAlgHom γ) (AlgHom.id B R)).toRingHom
      ⟨q.val, inferInstance⟩).asIdeal := by
    intro heMem
    apply (hsupp q q.val inferInstance inferInstance).mpr rfl
    change Algebra.TensorProduct.map (CommRingCat.toAlgHom γ)
      (AlgHom.id B R) (eC q) ∈ q.val at heMem
    rw [hmap q] at heMem
    exact heMem
  obtain ⟨f, hf, hEtale⟩ := selectedFactor_exists_etale_away
    (G := MulAction.stabilizer G (eC q)) C
    (PrimeSpectrum.comap (Algebra.TensorProduct.map (CommRingCat.toAlgHom γ)
      (AlgHom.id B R)).toRingHom ⟨q.val, inferInstance⟩) eH heQ hfactor.2
  refine ⟨f, ?_, hEtale⟩
  intro hmem
  apply hf
  change Algebra.TensorProduct.map (CommRingCat.toAlgHom γ)
    (AlgHom.id B R) ((1 : C) ⊗ₜ[B] (f : R)) ∈ q.val
  have hgerm := AlgHom.congr_fun (Algebra.TensorProduct.map_comp_includeRight
    (CommRingCat.toAlgHom γ) (AlgHom.id B R)) (f : R)
  change Algebra.TensorProduct.map (CommRingCat.toAlgHom γ)
    (AlgHom.id B R) ((1 : C) ⊗ₜ[B] (f : R)) = (1 : A) ⊗ₜ[B] (f : R) at hgerm
  rw [hgerm]
  exact hmem

end CoefficientFamilies

/-- The actual stalk prime supplies a genuine principal étale neighborhood
in the original inertia-fixed algebra, with its original coordinate
contraction. All intermediate families, coefficients and image points are
constructed from the given finite action and geometric point. -/
theorem invariantGeometricFiber_exists_etale_inertiaNeighborhood
    (R : Type u) (G : Type w) [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : FixedPoints.subring R G →+* Ω) :
    let B : CommRingCat.{u} := CommRingCat.of (FixedPoints.subring R G)
    let ψ : B →+* Ω := φ
    let A : Under B := (geometricStalkSmallAlgebraCocone ψ).pt
    let : Algebra B A := EtaleFundamentalGroups.underCommRingCatAlgebra A
    let : HenselianLocalRing A :=
      geometricStalk_henselianLocalRing (Spec.map (CommRingCat.ofHom ψ))
    let : IsSepClosed (IsLocalRing.ResidueField A) :=
      geometricStalk_residueField_isSepClosed (Spec.map (CommRingCat.ofHom ψ))
    let T := A ⊗[B] R
    let : MulSemiringAction G T := baseChangeAction B A R G
    let : SMulCommClass G A T := baseChangeAction_smulCommClass B A R G
    ∀ q : (IsLocalRing.maximalIdeal A).primesOver T,
      ∃ f : FixedPoints.subalgebra B R (q.val.inertia G),
        f ∉ (PrimeSpectrum.comap
          ((Algebra.TensorProduct.includeRight (R := B) (A := A) (B := R)).toRingHom.comp
            (FixedPoints.subalgebra B R (q.val.inertia G)).val.toRingHom)
          ⟨q.val, inferInstance⟩).asIdeal ∧ Algebra.Etale B (Localization.Away f) := by
  classical
  intro B ψ A actualAlgebra actualHenselian actualResidue T actualAction actualComm q
  have : Algebra.IsInvariant B R G := by
    constructor
    intro r hr
    exact ⟨⟨r, hr⟩, rfl⟩
  have : Module.Flat B A := geometricStalkStructureMap_flat ψ
  have : Algebra.IsInvariant A T G := baseChangeAction_isInvariant B A R G
  have : Algebra.IsIntegral A T := Algebra.IsInvariant.isIntegral A T G
  have hfinite : ((IsLocalRing.maximalIdeal A).primesOver T).Finite :=
    baseChangeAction_finite_primesOver B A R G (IsLocalRing.maximalIdeal A)
  let : Fintype ((IsLocalRing.maximalIdeal A).primesOver T) := hfinite.fintype
  obtain ⟨e, he, hsupp⟩ := exists_completeOrthogonalIdempotents_of_finite_integral_fiber A T hfinite
  have hσ := isolatingIdempotents_equivariant A T G hfinite e he.idem hsupp
  obtain ⟨C, hC, γ, eC, heC, hσC, hmap⟩ := etaleCoefficient_family ψ
    (primeFiberPermutation A T G (IsLocalRing.maximalIdeal A)) e he hσ
  let : Algebra B C := EtaleFundamentalGroups.underCommRingCatAlgebra C
  have : Algebra.Etale B C := hC
  exact algebraic_inertiaNeighborhood A C γ hfinite e he hsupp eC heC hσC hmap q
    (show Function.Injective (algebraMap B R) from Subtype.val_injective)

/-- Stacks Project, Tag 0BST: for an arbitrary finite group acting on an
arbitrary commutative ring, the inclusion of full invariants into the
inertia invariants is genuinely étale on a principal neighborhood of the
contracted original prime. No domain, normality, noetherian, finite-type,
or maximal-prime assumption is imposed. -/
theorem inertia_invariants_exists_etale_away
    (R : Type u) (G : Type w) [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]
    (q : Ideal R) [q.IsPrime] :
    ∃ f : FixedPoints.subalgebra (FixedPoints.subring R G) R (q.inertia G),
      (f : R) ∉ q ∧ Algebra.Etale (FixedPoints.subring R G) (Localization.Away f) := by
  let B : CommRingCat.{u} := CommRingCat.of (FixedPoints.subring R G)
  let Ω := AlgebraicClosure q.ResidueField
  let φ : B →+* Ω := originalPrimeGeometricPoint B q
  let A : Under B := (geometricStalkSmallAlgebraCocone φ).pt
  let : Algebra B A := EtaleFundamentalGroups.underCommRingCatAlgebra A
  have : HenselianLocalRing A := geometricStalk_henselianLocalRing (Spec.map (CommRingCat.ofHom φ))
  have : IsSepClosed (IsLocalRing.ResidueField A) :=
    geometricStalk_residueField_isSepClosed (Spec.map (CommRingCat.ofHom φ))
  let T := A ⊗[B] R
  let : MulSemiringAction G T := baseChangeAction B A R G
  have : SMulCommClass G A T := baseChangeAction_smulCommClass B A R G
  obtain ⟨Q, hQmax, hQq⟩ := geometricStalk_exists_tensorProduct_prime_over_original B R q
  have : Q.asIdeal.LiesOver (IsLocalRing.maximalIdeal A) := ⟨hQmax.symm⟩
  let qT : (IsLocalRing.maximalIdeal A).primesOver T :=
    Ideal.primesOver.mk (IsLocalRing.maximalIdeal A) Q.asIdeal
  have hI : q.inertia G = Q.asIdeal.inertia G :=
    (congrArg (fun J : Ideal R => J.inertia G) hQq.symm).trans
      (inertia_comap_includeRight B A R G Q.asIdeal)
  have h := invariantGeometricFiber_exists_etale_inertiaNeighborhood R G φ qT
  change ∃ f : FixedPoints.subalgebra B R (Q.asIdeal.inertia G),
    f ∉ (PrimeSpectrum.comap
      ((Algebra.TensorProduct.includeRight (R := B) (A := A) (B := R)).toRingHom.comp
        (FixedPoints.subalgebra B R (Q.asIdeal.inertia G)).val.toRingHom) Q).asIdeal ∧
      Algebra.Etale B (Localization.Away f) at h
  rw [← hI] at h
  obtain ⟨f, hf, hEtale⟩ := h
  refine ⟨f, ?_, hEtale⟩
  intro hmem
  apply hf
  change (1 : A) ⊗ₜ[B] (f : R) ∈ Q.asIdeal
  change (f : R) ∈ q at hmem
  exact Eq.mpr (congrArg (fun J : Ideal R => (f : R) ∈ J) hQq) hmem

end EtaleFundamentalGroups.Inertia
