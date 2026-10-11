/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedLefschetzAlgebra
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedNormalizationLocal
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumCompleteLocalConnectedness
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Comparing a connected normalization fibre with an affine puncture

The punctured closed fibre of the function-field normalization is defined
scheme-theoretically by two pullbacks.  This file compares those pullbacks
with the punctured spectrum of the corresponding quotient of the literal
integral-closure algebra.
-/

noncomputable section

open CategoryTheory Limits IsLocalRing TopologicalSpace
open CategoryTheory.PreGaloisCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

/-- An integral homomorphism between local rings is a local homomorphism. -/
theorem isLocalHom_of_isIntegral_between_localRings
    {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B]
    (f : A →+* B) (hf : f.IsIntegral) : IsLocalHom f := by
  have hcomap :
      ((maximalIdeal B).comap f).IsMaximal := by
    let : (maximalIdeal B).IsMaximal := maximalIdeal.isMaximal B
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal f hf
      (maximalIdeal B)
  have heq : (maximalIdeal B).comap f = maximalIdeal A :=
    (maximal_ideal_unique A).unique hcomap (maximalIdeal.isMaximal A)
  exact ((local_hom_TFAE f).out 5 1).mp heq

/-- For an integral map of local rings, the inverse image of the punctured
spectrum is the punctured spectrum. -/
theorem preimage_puncturedSpectrumOpen_of_isIntegral
    {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B]
    (f : A →+* B) (hf : f.IsIntegral) :
    Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ puncturedSpectrumOpen A =
      puncturedSpectrumOpen B := by
  let : IsLocalHom f :=
    isLocalHom_of_isIntegral_between_localRings f hf
  let q : Spec (.of B) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom f)
  have hqClosed : q (closedPoint (CommRingCat.of B)) =
      closedPoint (CommRingCat.of A) := Spec_closedPoint
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro p
  change q p ∈ puncturedSpectrumOpen A ↔
    p ∈ puncturedSpectrumOpen B
  change q p ≠ closedPoint (CommRingCat.of A) ↔
    p ≠ closedPoint (CommRingCat.of B)
  constructor
  · intro hp hclosed
    exact hp (hclosed.symm ▸ hqClosed)
  · intro hp hclosed
    apply hp
    have hcomap : p.asIdeal.comap f = maximalIdeal A := by
      exact PrimeSpectrum.ext_iff.mp hclosed
    let : p.asIdeal.IsPrime := p.isPrime
    have hpMax : p.asIdeal.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap f hf p.asIdeal <| by
        rw [hcomap]
        exact maximalIdeal.isMaximal A
    exact PrimeSpectrum.ext_iff.mpr <|
      (maximal_ideal_unique B).unique hpMax (maximalIdeal.isMaximal B)

/-- Pulling an affine integral local morphism back to the puncture of its
target gives the punctured spectrum of its source. -/
noncomputable def pullbackPuncturedSpectrumIsoOfIntegral
    {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B]
    (f : A →+* B) (hf : f.IsIntegral) :
    Limits.pullback (Spec.map (CommRingCat.ofHom f))
        (puncturedSpectrumInclusion A) ≅
      puncturedSpectrum B := by
  letI : IsOpenImmersion (puncturedSpectrumInclusion A) := by
    dsimp only [puncturedSpectrumInclusion]
    infer_instance
  letI : IsOpenImmersion
      (Limits.pullback.fst (Spec.map (CommRingCat.ofHom f))
        (puncturedSpectrumInclusion A)) := inferInstance
  letI : IsOpenImmersion (puncturedSpectrumInclusion B) := by
    dsimp only [puncturedSpectrumInclusion]
    infer_instance
  apply IsOpenImmersion.isoOfRangeEq
    (Limits.pullback.fst (Spec.map (CommRingCat.ofHom f))
      (puncturedSpectrumInclusion A))
    (puncturedSpectrumInclusion B)
  rw [IsOpenImmersion.range_pullbackFst]
  dsimp only [puncturedSpectrumInclusion]
  rw [Scheme.Opens.opensRange_ι, Scheme.Opens.range_ι]
  exact congrArg (fun U : (Spec (.of B)).Opens ↦ U.1)
    (preimage_puncturedSpectrumOpen_of_isIntegral f hf)

/-- A ring equivalence between local rings induces an isomorphism of their
punctured spectra. -/
noncomputable def puncturedSpectrumIsoOfRingEquiv
    {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (e : A ≃+* B) :
    puncturedSpectrum A ≅ puncturedSpectrum B := by
  let f : Spec (.of B) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom e.toRingHom)
  let p : puncturedSpectrum A ⟶ Spec (.of A) :=
    puncturedSpectrumInclusion A
  letI : IsIso (CommRingCat.ofHom e.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective
      (CommRingCat.ofHom e.toRingHom)).mpr e.bijective
  letI : IsIso f := by
    dsimp only [f]
    infer_instance
  letI : IsIso (Limits.pullback.snd f p) := inferInstance
  exact (asIso (Limits.pullback.snd f p)).symm ≪≫
    pullbackPuncturedSpectrumIsoOfIntegral e.toRingHom
      (e.toRingHom.isIntegral_of_surjective e.surjective)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
  [IsNoetherianRing R] [IsIntegrallyClosed R]

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
private theorem puncturedSpectrumFunctionFieldRingEquiv_apply_germ_source_forFiber
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (r : Γ(Spec (.of R), ⊤)) :
    let X := Spec (.of R)
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : Nonempty (⊤ : X.Opens) :=
      ⟨⟨genericPoint X, by trivial⟩⟩
    letI : Algebra R X.functionField :=
      AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
    letI : Nonempty (⊤ : U.Opens) :=
      ⟨⟨genericPoint U, by trivial⟩⟩
    puncturedSpectrumFunctionFieldRingEquivOfPositiveDimension R hpos
        (X.germToFunctionField ⊤ r) =
      U.germToFunctionField ⊤ (j.appTop r) := by
  dsimp only
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  let : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  let : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : Nonempty (⊤ : X.Opens) :=
    ⟨⟨genericPoint X, by trivial⟩⟩
  let : Algebra R X.functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
  let : Nonempty (⊤ : U.Opens) :=
    ⟨⟨genericPoint U, by trivial⟩⟩
  let hgen : j (genericPoint U) = genericPoint X :=
    genericPoint_eq_of_isOpenImmersion j
  change j.stalkMap (genericPoint U)
      ((X.presheaf.stalkCongr (.of_eq hgen.symm)).hom
        (X.germToFunctionField ⊤ r)) =
    U.germToFunctionField ⊤ (j.appTop r)
  simp only [TopCat.Presheaf.stalkCongr_hom]
  have htransport :
      X.presheaf.stalkSpecializes
          (Inseparable.of_eq hgen.symm).ge
          (X.presheaf.germ ⊤ (genericPoint X) (by trivial) r) =
        X.presheaf.germ ⊤ (j (genericPoint U)) (by trivial) r := by
    exact DFunLike.congr_fun
      (CommRingCat.hom_ext_iff.mp
        (X.presheaf.germ_stalkSpecializes
          (show genericPoint X ∈ (⊤ : X.Opens) by trivial)
          (Inseparable.of_eq hgen.symm).ge)) r
  rw [htransport]
  exact j.germ_stalkMap_apply (⊤ : X.Opens) (genericPoint U)
    (by trivial) r

omit [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
private theorem specFunctionField_algebraMap_ΓSpecIso_hom_source_forFiber
    (r : Γ(Spec (.of R), ⊤)) :
    let X := Spec (.of R)
    letI : Nonempty (⊤ : X.Opens) :=
      ⟨⟨genericPoint X, by trivial⟩⟩
    letI : Algebra R X.functionField :=
      AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
    algebraMap R X.functionField ((Scheme.ΓSpecIso (.of R)).hom r) =
      X.germToFunctionField ⊤ r := by
  dsimp only
  let X := Spec (.of R)
  let : Nonempty (⊤ : X.Opens) :=
    ⟨⟨genericPoint X, by trivial⟩⟩
  let : Algebra R X.functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
  change X.presheaf.germ ⊤ (genericPoint X) (by trivial)
      ((Scheme.ΓSpecIso (.of R)).inv
        ((Scheme.ΓSpecIso (.of R)).hom r)) =
    X.germToFunctionField ⊤ r
  change X.presheaf.germ ⊤ (genericPoint X) (by trivial)
      ((Scheme.ΓSpecIso (.of R)).inv
        ((Scheme.ΓSpecIso (.of R)).hom r)) =
    X.presheaf.germ ⊤ (genericPoint X) (by trivial) r
  exact congrArg (fun s ↦
    X.presheaf.germ ⊤ (genericPoint X) (by trivial) s)
      (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of R)) r)

private noncomputable def connectedPuncturedCoverGenericNormalizationSectionsComparisonData
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    let g : Spec (.of W.left.functionField) ⟶ Spec (.of R) :=
      connectedCoverGenericComposite W ≫ j
    { e : Γ(g.normalization, ⊤) ≃+*
        integralClosure R W.left.functionField //
      e.toRingHom.comp g.fromNormalization.appTop.hom =
        (algebraMap R (integralClosure R W.left.functionField)).comp
          (Scheme.ΓSpecIso (.of R)).hom.hom } := by
  dsimp only
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  letI : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  letI : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U := isIntegral_of_isOpenImmersion j
  letI : Nonempty (⊤ : X.Opens) :=
    ⟨⟨genericPoint X, by trivial⟩⟩
  letI : Nonempty (⊤ : U.Opens) :=
    ⟨⟨genericPoint U, by trivial⟩⟩
  letI : Algebra R X.functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
  letI : Algebra R U.functionField :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  letI : IsFractionRing R U.functionField :=
    puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
  letI : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  letI : Algebra U.functionField W.left.functionField :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  letI : Algebra R W.left.functionField :=
    ((algebraMap U.functionField W.left.functionField).comp
      (algebraMap R U.functionField)).toAlgebra
  letI : IsScalarTower R U.functionField W.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let L : Type u := W.left.functionField
  let f : Spec (.of L) ⟶ U := connectedCoverGenericComposite W
  let g : Spec (.of L) ⟶ X := f ≫ j
  let A : Type u := Γ(X, ⊤)
  let S : Type u := Γ(Spec (.of L), g ⁻¹ᵁ (⊤ : X.Opens))
  letI : Algebra A S := g.appTop.hom.toAlgebra
  let eBase : A ≃+* R :=
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  let eAmbientCat : CommRingCat.of S ≅ CommRingCat.of L := by
    change Γ(Spec (.of L), f ⁻¹ᵁ (⊤ : U.Opens)) ≅ .of L
    exact connectedCoverGenericCompositeSectionsIso W
  let eAmbient : S ≃+* L := eAmbientCat.commRingCatIsoToRingEquiv
  have hCompat :
      eAmbient.toRingHom.comp (algebraMap A S) =
        (algebraMap R L).comp eBase.toRingHom := by
    ext a
    change eAmbient (g.appTop a) = algebraMap R L (eBase a)
    change (connectedCoverGenericCompositeSectionsIso W).hom
        (f.appTop (j.appTop a)) = algebraMap R L (eBase a)
    rw [connectedCoverGenericCompositeSectionsIso_hom_appTop]
    change algebraMap U.functionField L
        (U.germToFunctionField ⊤ (j.appTop a)) =
      algebraMap U.functionField L (algebraMap R U.functionField (eBase a))
    congr 1
    rw [← puncturedSpectrumFunctionFieldRingEquiv_apply_germ_source_forFiber
      R hpos a]
    change (puncturedSpectrumFunctionFieldRingEquivOfPositiveDimension R hpos)
        (X.germToFunctionField ⊤ a) =
      (puncturedSpectrumFunctionFieldRingEquivOfPositiveDimension R hpos)
        (algebraMap R X.functionField (eBase a))
    congr 1
    exact
      (specFunctionField_algebraMap_ΓSpecIso_hom_source_forFiber R a).symm
  let C0 : Type u := integralClosure A S
  let C : Type u := integralClosure R L
  letI : Algebra A C :=
    EtaleFundamentalGroups.integralClosureBaseRingAlgebra eBase
  let eC : C0 ≃ₐ[A] C :=
    EtaleFundamentalGroups.integralClosureAlgEquivOfBaseAndAmbientEquiv
      eBase eAmbient hCompat
  let eN : CommRingCat.of Γ(g.normalization, ⊤) ≅ .of C0 := by
    exact g.normalizationObjIso (isAffineOpen_top X)
  let e : Γ(g.normalization, ⊤) ≃+* C :=
    eN.commRingCatIsoToRingEquiv.trans eC.toRingEquiv
  refine ⟨e, ?_⟩
  have hz := g.fromNormalization_app (isAffineOpen_top X)
  have hz' : g.fromNormalization.appTop =
      CommRingCat.ofHom (algebraMap A C0) ≫ eN.inv := by
    exact hz
  have hzMorph : g.fromNormalization.appTop ≫ eN.hom =
      CommRingCat.ofHom (algebraMap A C0) := by
    calc
      g.fromNormalization.appTop ≫ eN.hom =
          (CommRingCat.ofHom (algebraMap A C0) ≫ eN.inv) ≫
            eN.hom := congrArg (fun k ↦ k ≫ eN.hom) hz'
      _ = CommRingCat.ofHom (algebraMap A C0) := by simp
  apply RingHom.ext
  intro a
  have hmain : e (g.fromNormalization.appTop a) =
      algebraMap R C (eBase a) := by
    change eC (eN.hom (g.fromNormalization.appTop a)) =
      algebraMap R C (eBase a)
    have heN := DFunLike.congr_fun
      (CommRingCat.hom_ext_iff.mp hzMorph) a
    simp only [CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.hom_ofHom] at heN
    rw [heN]
    exact eC.commutes a
  dsimp only [e, g, j, C, eBase, L, f, X, A] at hmain ⊢
  convert hmain using 1 <;> rfl

/-- The global sections of the generic-field normalization are the literal
integral closure of `R` in the connected cover's function field. -/
noncomputable def connectedPuncturedCoverGenericNormalizationSectionsRingEquiv
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    Γ((connectedCoverGenericComposite W ≫ j).normalization, ⊤) ≃+*
      integralClosure R W.left.functionField :=
  (connectedPuncturedCoverGenericNormalizationSectionsComparisonData
    R hpos W).1

/-- The sections equivalence identifies the normalization morphism with the
literal algebra map from `R` to its integral closure. -/
theorem connectedPuncturedCoverGenericNormalizationSectionsRingEquiv_appTop
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    let g : Spec (.of W.left.functionField) ⟶ Spec (.of R) :=
      connectedCoverGenericComposite W ≫ j
    (connectedPuncturedCoverGenericNormalizationSectionsRingEquiv
        R hpos W).toRingHom.comp g.fromNormalization.appTop.hom =
      (algebraMap R (integralClosure R W.left.functionField)).comp
        (Scheme.ΓSpecIso (.of R)).hom.hom :=
  (connectedPuncturedCoverGenericNormalizationSectionsComparisonData
    R hpos W).2

private noncomputable def connectedPuncturedCoverGenericNormalizationIsoSpecIntegralClosureData
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    let C := integralClosure R W.left.functionField
    let g : Spec (.of W.left.functionField) ⟶ Spec (.of R) :=
      connectedCoverGenericComposite W ≫ j
    { e : g.normalization ≅ Spec (.of C) //
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)) =
        g.fromNormalization } := by
  dsimp only
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  letI : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  letI : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U := isIntegral_of_isOpenImmersion j
  letI : Algebra R U.functionField :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  letI : IsFractionRing R U.functionField :=
    puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
  letI : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  letI : Algebra U.functionField W.left.functionField :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  letI : Algebra R W.left.functionField :=
    ((algebraMap U.functionField W.left.functionField).comp
      (algebraMap R U.functionField)).toAlgebra
  letI : IsScalarTower R U.functionField W.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let L : Type u := W.left.functionField
  let C : Type u := integralClosure R L
  let g : Spec (.of L) ⟶ X := connectedCoverGenericComposite W ≫ j
  let Z : Scheme.{u} := g.normalization
  let z : Z ⟶ X := g.fromNormalization
  letI : IsFinite z :=
    connectedPuncturedCoverGenericNormalization_isFinite R hpos W
  letI : IsAffine Z := isAffine_of_isAffineHom z
  let eRing : Γ(Z, ⊤) ≃+* C :=
    connectedPuncturedCoverGenericNormalizationSectionsRingEquiv R hpos W
  let eRingIso : CommRingCat.of Γ(Z, ⊤) ≅ CommRingCat.of C :=
    { hom := CommRingCat.ofHom eRing.toRingHom
      inv := CommRingCat.ofHom eRing.symm.toRingHom
      hom_inv_id := by
        apply CommRingCat.hom_ext
        ext a
        exact eRing.symm_apply_apply a
      inv_hom_id := by
        apply CommRingCat.hom_ext
        ext a
        exact congrArg Subtype.val (eRing.apply_symm_apply a) }
  letI : IsIso eRingIso.hom := eRingIso.isIso_hom
  let e : Z ≅ Spec (.of C) :=
    Z.isoSpec ≪≫
      Scheme.Spec.mapIso eRingIso.symm.op
  refine ⟨e, ?_⟩
  have hRing :=
    connectedPuncturedCoverGenericNormalizationSectionsRingEquiv_appTop
      R hpos W
  have hRingCat :
      z.appTop ≫ eRingIso.hom =
        (Scheme.ΓSpecIso (.of R)).hom ≫
          CommRingCat.ofHom (algebraMap R C) := by
    apply CommRingCat.hom_ext
    dsimp only [eRingIso]
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using hRing
  have hRingInv :
      (Scheme.ΓSpecIso (.of R)).inv ≫ z.appTop =
        CommRingCat.ofHom (algebraMap R C) ≫
          eRingIso.inv := by
    apply (cancel_mono eRingIso.hom).1
    simp only [Category.assoc]
    rw [hRingCat]
    simp
  have hSpec :
      Spec.map eRingIso.inv ≫
          Spec.map (CommRingCat.ofHom (algebraMap R C)) =
        Spec.map z.appTop ≫
          Spec.map (Scheme.ΓSpecIso (.of R)).inv := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map hRingInv.symm
  change (Z.isoSpec.hom ≫
      Spec.map eRingIso.inv) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R C)) = z
  rw [Category.assoc, hSpec]
  rw [Scheme.isoSpec_hom_naturality_assoc]
  dsimp only [X]
  rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp]
  simp

/-- The generic-field normalization over the affine local base is the
spectrum of the literal integral-closure algebra. -/
noncomputable def connectedPuncturedCoverGenericNormalizationIsoSpecIntegralClosure
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    (connectedCoverGenericComposite W ≫ j).normalization ≅
      Spec (.of (integralClosure R W.left.functionField)) :=
  (connectedPuncturedCoverGenericNormalizationIsoSpecIntegralClosureData
    R hpos W).1

@[reassoc (attr := simp)]
theorem connectedPuncturedCoverGenericNormalizationIsoSpecIntegralClosure_hom_fromSpec
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    (connectedPuncturedCoverGenericNormalizationIsoSpecIntegralClosure
        R hpos W).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap R (integralClosure R W.left.functionField))) =
      (connectedCoverGenericComposite W ≫ j).fromNormalization :=
  (connectedPuncturedCoverGenericNormalizationIsoSpecIntegralClosureData
    R hpos W).2

/-- Pulling back two isomorphic schemes over a fixed base preserves the
pullback.  This local copy is used to keep the comparison data explicit. -/
private noncomputable def pullbackIsoOfIsoOverForNormalizationFiber
    {A B X Y : Scheme.{u}} (e : A ≅ B)
    (f : A ⟶ X) (h : B ⟶ X) (g : Y ⟶ X)
    (w : e.hom ≫ h = f) :
    Limits.pullback f g ≅ Limits.pullback h g :=
  asIso <| Limits.pullback.map f g h g e.hom (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using w.symm) (by simp)

private noncomputable def affineQuotientPullbackIsoData
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (Z : Scheme.{u}) (z : Z ⟶ Spec (.of A))
    (eZ : Z ≅ Spec (.of B))
    (heZ : eZ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = z) :
    let Q := B ⧸ I.map (algebraMap A B)
    let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    { e : Limits.pullback z q ≅ Spec (.of Q) //
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I) Q)) =
        Limits.pullback.snd z q } := by
  let Q := B ⧸ I.map (algebraMap A B)
  let T := A ⧸ I
  let c := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let eFiber : Limits.pullback z q ≅ Limits.pullback c q :=
    pullbackIsoOfIsoOverForNormalizationFiber eZ z c q heZ
  have heFiber :
      eFiber.hom ≫ Limits.pullback.snd c q =
        Limits.pullback.snd z q := by
    dsimp only [eFiber, pullbackIsoOfIsoOverForNormalizationFiber]
    simp only [asIso_hom, pullback.map, pullback.lift_snd,
      Category.comp_id]
  let eRing : Q ≃ₐ[T] T ⊗[A] B :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  let eAffine : Limits.pullback c q ≅ Spec (.of Q) :=
    pullbackSymmetry c q ≪≫
      pullbackSpecIso A T B ≪≫
        Scheme.Spec.mapIso eRing.toRingEquiv.toCommRingCatIso.op
  have hRingBase :
      CommRingCat.ofHom (algebraMap T Q) ≫
          CommRingCat.ofHom eRing.toRingEquiv.toRingHom =
        CommRingCat.ofHom (algebraMap T (T ⊗[A] B)) := by
    apply CommRingCat.hom_ext
    ext t
    exact eRing.commutes t
  have hSpecBase :
      Spec.map (CommRingCat.ofHom eRing.toRingEquiv.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap T Q)) =
        Spec.map (CommRingCat.ofHom (algebraMap T (T ⊗[A] B))) := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map hRingBase
  have heAffine :
      eAffine.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap T Q)) =
        Limits.pullback.snd c q := by
    change ((pullbackSymmetry c q).hom ≫
        (pullbackSpecIso A T B).hom ≫
          Spec.map (CommRingCat.ofHom eRing.toRingEquiv.toRingHom)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap T Q)) = _
    simp only [Category.assoc]
    rw [hSpecBase, pullbackSpecIso_hom_fst',
      pullbackSymmetry_hom_comp_fst]
  let e : Limits.pullback z q ≅ Spec (.of Q) := eFiber ≪≫ eAffine
  refine ⟨e, ?_⟩
  change e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap T Q)) =
    Limits.pullback.snd z q
  change (eFiber.hom ≫ eAffine.hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap T Q)) =
    Limits.pullback.snd z q
  rw [Category.assoc, heAffine, heFiber]

private noncomputable def
    connectedPuncturedCoverNormalizationClosedFiberIsoSpecQuotientData
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (I : Ideal R) :
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    let C := integralClosure R W.left.functionField
    let Q := C ⧸ I.map (algebraMap R C)
    { e :
        (connectedPuncturedCoverNormalizationClosedFiber R hpos W I).left ≅
          Spec (.of Q) //
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ I) Q)) =
        (connectedPuncturedCoverNormalizationClosedFiber R hpos W I).hom } := by
  dsimp only
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  letI : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  letI : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U := isIntegral_of_isOpenImmersion j
  letI : Algebra R U.functionField :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  letI : IsFractionRing R U.functionField :=
    puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
  letI : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  letI : Algebra U.functionField W.left.functionField :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  letI : Algebra R W.left.functionField :=
    ((algebraMap U.functionField W.left.functionField).comp
      (algebraMap R U.functionField)).toAlgebra
  letI : IsScalarTower R U.functionField W.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let L : Type u := W.left.functionField
  let C : Type u := integralClosure R L
  let g : Spec (.of L) ⟶ X := connectedCoverGenericComposite W ≫ j
  let Z : Scheme.{u} := g.normalization
  let z : Z ⟶ X := g.fromNormalization
  let c : Spec (.of C) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap R C))
  let eZ : Z ≅ Spec (.of C) :=
    connectedPuncturedCoverGenericNormalizationIsoSpecIntegralClosure
      R hpos W
  have heZ : eZ.hom ≫ c = z :=
    connectedPuncturedCoverGenericNormalizationIsoSpecIntegralClosure_hom_fromSpec
      R hpos W
  exact affineQuotientPullbackIsoData R C I Z z eZ heZ

/-- The normalization closed fibre over `R ⧸ I` is the spectrum of the
literal quotient of the integral-closure algebra by the extended ideal. -/
noncomputable def connectedPuncturedCoverNormalizationClosedFiberIsoSpecQuotient
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (I : Ideal R) :
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    (connectedPuncturedCoverNormalizationClosedFiber R hpos W I).left ≅
      Spec (.of ((integralClosure R W.left.functionField) ⧸
        I.map (algebraMap R (integralClosure R W.left.functionField)))) :=
  (connectedPuncturedCoverNormalizationClosedFiberIsoSpecQuotientData
    R hpos W I).1

@[reassoc (attr := simp)]
theorem connectedPuncturedCoverNormalizationClosedFiberIsoSpecQuotient_hom_over
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (I : Ideal R) :
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    (connectedPuncturedCoverNormalizationClosedFiberIsoSpecQuotient
        R hpos W I).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (R ⧸ I)
          ((integralClosure R W.left.functionField) ⧸
            I.map (algebraMap R (integralClosure R W.left.functionField))))) =
      (connectedPuncturedCoverNormalizationClosedFiber R hpos W I).hom :=
  (connectedPuncturedCoverNormalizationClosedFiberIsoSpecQuotientData
    R hpos W I).2

/-- For a complete base, the punctured normalization fibre is the punctured
spectrum of the literal quotient of the connected integral closure. -/
noncomputable def
    connectedPuncturedCoverNormalizationPuncturedFiberIsoPuncturedSpectrumQuotient
    [IsAdicComplete (maximalIdeal R) R]
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    let C := integralClosure R W.left.functionField
    let J := I.map (algebraMap R C)
    let Q := C ⧸ J
    letI : IsLocalRing C :=
      connectedPuncturedCover_integralClosure_isLocalRing (R := R) hpos W
    letI : IsLocalHom (algebraMap R C) :=
      Scheme.isLocalHom_of_isIntegral_between_localRings
        (algebraMap R C) (algebraMap_isIntegral_iff.mpr inferInstance)
    let hJ : J ≤ maximalIdeal C :=
      (Ideal.map_mono hI).trans (map_maximalIdeal_le (algebraMap R C))
    letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top hJ
    letI : IsLocalRing Q :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
        Ideal.Quotient.mk_surjective
    connectedPuncturedCoverNormalizationPuncturedFiber
        R hpos W I hI ≅
      Scheme.puncturedSpectrum Q := by
  dsimp only
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  letI : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  letI : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U := isIntegral_of_isOpenImmersion j
  letI : Algebra R U.functionField :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  letI : IsFractionRing R U.functionField :=
    puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
  letI : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  letI : Algebra U.functionField W.left.functionField :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  letI : Algebra R W.left.functionField :=
    ((algebraMap U.functionField W.left.functionField).comp
      (algebraMap R U.functionField)).toAlgebra
  letI : IsScalarTower R U.functionField W.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let L : Type u := W.left.functionField
  let C : Type u := integralClosure R L
  let J : Ideal C := I.map (algebraMap R C)
  let Q : Type u := C ⧸ J
  let T : Type u := R ⧸ I
  letI : IsLocalRing C :=
    connectedPuncturedCover_integralClosure_isLocalRing (R := R) hpos W
  letI : IsLocalHom (algebraMap R C) :=
    Scheme.isLocalHom_of_isIntegral_between_localRings
      (algebraMap R C) (algebraMap_isIntegral_iff.mpr inferInstance)
  have hJ : J ≤ maximalIdeal C := by
    exact (Ideal.map_mono hI).trans (map_maximalIdeal_le (algebraMap R C))
  have hJne : J ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top hJ
  letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hJne
  letI : IsLocalRing Q :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective
  letI : Nontrivial T :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
  letI : IsLocalRing T :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  letI : Module.Finite R C :=
    connectedPuncturedCover_integralClosure_finite_of_positiveDimension
      R hpos W
  let eRing : Q ≃ₐ[T] T ⊗[R] C :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I
  letI : Module.Finite T Q :=
    Module.Finite.equiv eRing.symm.toLinearEquiv
  have hf : (algebraMap T Q).IsIntegral :=
    algebraMap_isIntegral_iff.mpr inferInstance
  let F := connectedPuncturedCoverNormalizationClosedFiber R hpos W I
  let f : Spec (.of Q) ⟶ Spec (.of T) :=
    Spec.map (CommRingCat.ofHom (algebraMap T Q))
  let p : Scheme.puncturedSpectrum T ⟶ Spec (.of T) :=
    Scheme.puncturedSpectrumInclusion T
  let eClosed : F.left ≅ Spec (.of Q) :=
    connectedPuncturedCoverNormalizationClosedFiberIsoSpecQuotient
      R hpos W I
  have heClosed : eClosed.hom ≫ f = F.hom :=
    connectedPuncturedCoverNormalizationClosedFiberIsoSpecQuotient_hom_over
      R hpos W I
  change Limits.pullback F.hom p ≅ Scheme.puncturedSpectrum Q
  exact
    pullbackIsoOfIsoOverForNormalizationFiber
        eClosed F.hom f p heClosed ≪≫
      Scheme.pullbackPuncturedSpectrumIsoOfIntegral (algebraMap T Q) hf

/-- Principal-ideal form of the punctured-fibre comparison, with the ideal
in the normalization written literally as the span of the image element. -/
noncomputable def
    connectedPuncturedCoverNormalizationPuncturedFiberIsoSpanSingleton
    [IsAdicComplete (maximalIdeal R) R]
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (x : R) (hx : x ∈ maximalIdeal R) :
    let U := Scheme.puncturedSpectrum R
    let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    let C := integralClosure R W.left.functionField
    let xC : C := algebraMap R C x
    let J := Ideal.span {xC}
    let Q := C ⧸ J
    letI : IsLocalRing C :=
      connectedPuncturedCover_integralClosure_isLocalRing (R := R) hpos W
    letI : IsLocalHom (algebraMap R C) :=
      Scheme.isLocalHom_of_isIntegral_between_localRings
        (algebraMap R C) (algebraMap_isIntegral_iff.mpr inferInstance)
    let hxC : xC ∈ maximalIdeal C :=
      map_nonunit (algebraMap R C) x hx
    letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hxC
    letI : IsLocalRing Q :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
        Ideal.Quotient.mk_surjective
    connectedPuncturedCoverNormalizationPuncturedFiber R hpos W
        (Ideal.span {x})
        ((maximalIdeal R).span_singleton_le_iff_mem.mpr hx) ≅
      Scheme.puncturedSpectrum Q := by
  dsimp only
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
  letI : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  letI : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U := isIntegral_of_isOpenImmersion j
  letI : Algebra R U.functionField :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  letI : IsFractionRing R U.functionField :=
    puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
  letI : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  letI : Algebra U.functionField W.left.functionField :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  letI : Algebra R W.left.functionField :=
    ((algebraMap U.functionField W.left.functionField).comp
      (algebraMap R U.functionField)).toAlgebra
  letI : IsScalarTower R U.functionField W.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let C : Type u := integralClosure R W.left.functionField
  let xC : C := algebraMap R C x
  let Jmap : Ideal C := (Ideal.span {x}).map (algebraMap R C)
  let Jspan : Ideal C := Ideal.span {xC}
  let A : Type u := C ⧸ Jmap
  let B : Type u := C ⧸ Jspan
  letI : IsLocalRing C :=
    connectedPuncturedCover_integralClosure_isLocalRing (R := R) hpos W
  letI : IsLocalHom (algebraMap R C) :=
    Scheme.isLocalHom_of_isIntegral_between_localRings
      (algebraMap R C) (algebraMap_isIntegral_iff.mpr inferInstance)
  have hxC : xC ∈ maximalIdeal C :=
    map_nonunit (algebraMap R C) x hx
  have hJmap : Jmap ≤ maximalIdeal C :=
    (Ideal.map_mono
      ((maximalIdeal R).span_singleton_le_iff_mem.mpr hx)).trans
        (map_maximalIdeal_le (algebraMap R C))
  have hJspan : Jspan ≤ maximalIdeal C :=
    (maximalIdeal C).span_singleton_le_iff_mem.mpr hxC
  letI : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr <|
    ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top hJmap
  letI : IsLocalRing A :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Jmap)
      Ideal.Quotient.mk_surjective
  letI : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr <|
    ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top hJspan
  letI : IsLocalRing B :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Jspan)
      Ideal.Quotient.mk_surjective
  have hmap :
      Jmap = Jspan := by
    dsimp only [Jmap, Jspan, xC]
    rw [Ideal.map_span, Set.image_singleton]
  let e :
      connectedPuncturedCoverNormalizationPuncturedFiber R hpos W
          (Ideal.span {x})
          ((maximalIdeal R).span_singleton_le_iff_mem.mpr hx) ≅
        Scheme.puncturedSpectrum A :=
    connectedPuncturedCoverNormalizationPuncturedFiberIsoPuncturedSpectrumQuotient
      R hpos W (Ideal.span {x})
        ((maximalIdeal R).span_singleton_le_iff_mem.mpr hx)
  exact e ≪≫
    Scheme.puncturedSpectrumIsoOfRingEquiv (Ideal.quotEquivOfEq hmap)

/-- Grothendieck connectedness for an ideal given by a finite list of
generators, transported through the literal normalization-fibre comparison.

The images of the generators need not be a regular sequence in the finite
normalization. -/
theorem connectedSpace_connectedPuncturedCoverNormalizationPuncturedFiber_ofList
    [IsAdicComplete (maximalIdeal R) R]
    (xs : List R)
    (hI : Ideal.ofList xs ≤ maximalIdeal R)
    (hdim :
      ((((xs.length + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim R))
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    let hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
      have hbase : (1 : WithBot ℕ∞) ≤
          (((xs.length + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        exact_mod_cast (by omega : 1 ≤ xs.length + 2)
      exact hbase.trans hdim
    ConnectedSpace
      (connectedPuncturedCoverNormalizationPuncturedFiber R hpos W
        (Ideal.ofList xs) hI) := by
  dsimp only
  have hbase : (1 : WithBot ℕ∞) ≤
      (((xs.length + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    exact_mod_cast (by omega : 1 ≤ xs.length + 2)
  have hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R :=
    hbase.trans hdim
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  let : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  let : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : Algebra R U.functionField :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  let : IsFractionRing R U.functionField :=
    puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let : Algebra U.functionField W.left.functionField :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : Algebra R W.left.functionField :=
    ((algebraMap U.functionField W.left.functionField).comp
      (algebraMap R U.functionField)).toAlgebra
  let : IsScalarTower R U.functionField W.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let L : Type u := W.left.functionField
  let C : Type u := integralClosure R L
  let f : R →+* C := algebraMap R C
  let xsC : List C := xs.map f
  let J : Ideal C := (Ideal.ofList xs).map f
  let Q : Type u := C ⧸ J
  let : Module.Finite R C :=
    connectedPuncturedCover_integralClosure_finite_of_positiveDimension
      R hpos W
  let : IsNoetherianRing C := IsNoetherianRing.of_finite R C
  let : IsLocalRing C :=
    connectedPuncturedCover_integralClosure_isLocalRing (R := R) hpos W
  let : IsAdicComplete (maximalIdeal C) C :=
    connectedPuncturedCover_integralClosure_isAdicComplete_maximalIdeal
      (R := R) hpos W
  let : IsLocalHom f :=
    Scheme.isLocalHom_of_isIntegral_between_localRings
      f (algebraMap_isIntegral_iff.mpr inferInstance)
  have hJ : J ≤ maximalIdeal C :=
    (Ideal.map_mono hI).trans (map_maximalIdeal_le f)
  have hJgen : J = Ideal.ofList xsC := by
    dsimp only [J, xsC, f]
    rw [Ideal.map_ofList]
  have hdimC :
      ((((xsC.length + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤
        ringKrullDim C) := by
    rw [connectedPuncturedCover_integralClosure_ringKrullDim_eq
      (R := R) hpos W]
    simpa only [xsC, List.length_map] using hdim
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr <|
    ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top hJ
  let : IsLocalRing Q :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective
  let : ConnectedSpace (Scheme.puncturedSpectrum Q) :=
    connectedSpace_puncturedSpectrum_quotient_ofList_of_completeLocalDomain
      J hJ xsC hJgen hdimC
  let e :=
    connectedPuncturedCoverNormalizationPuncturedFiberIsoPuncturedSpectrumQuotient
      R hpos W (Ideal.ofList xs) hI
  exact e.hom.homeomorph.connectedSpace_iff.mpr inferInstance

/-- Stage-4 connectedness endpoint: Grothendieck connectedness for a
complete local domain, transported through the literal normalization-fibre
comparison. -/
theorem connectedSpace_connectedPuncturedCoverNormalizationPuncturedFiber_span_singleton
    [IsAdicComplete (maximalIdeal R) R]
    (hdim : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (x : R) (hx : x ∈ maximalIdeal R) (hx0 : x ≠ 0) :
    let hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
      exact (by norm_num : (1 : WithBot ℕ∞) ≤ (3 : ℕ∞)).trans hdim
    ConnectedSpace
      (connectedPuncturedCoverNormalizationPuncturedFiber R hpos W
        (Ideal.span {x})
        ((maximalIdeal R).span_singleton_le_iff_mem.mpr hx)) := by
  dsimp only
  have hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R :=
    (by norm_num : (1 : WithBot ℕ∞) ≤ (3 : ℕ∞)).trans hdim
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  let : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  let : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : Algebra R U.functionField :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  let : IsFractionRing R U.functionField :=
    puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let : Algebra U.functionField W.left.functionField :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : Algebra R W.left.functionField :=
    ((algebraMap U.functionField W.left.functionField).comp
      (algebraMap R U.functionField)).toAlgebra
  let : IsScalarTower R U.functionField W.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let L : Type u := W.left.functionField
  let C : Type u := integralClosure R L
  let xC : C := algebraMap R C x
  let Q : Type u := C ⧸ Ideal.span {xC}
  let : Module.Finite R C :=
    connectedPuncturedCover_integralClosure_finite_of_positiveDimension
      R hpos W
  let : IsNoetherianRing C := IsNoetherianRing.of_finite R C
  let : IsLocalRing C :=
    connectedPuncturedCover_integralClosure_isLocalRing (R := R) hpos W
  let : IsAdicComplete (maximalIdeal C) C :=
    connectedPuncturedCover_integralClosure_isAdicComplete_maximalIdeal
      (R := R) hpos W
  let : IsLocalHom (algebraMap R C) :=
    Scheme.isLocalHom_of_isIntegral_between_localRings
      (algebraMap R C) (algebraMap_isIntegral_iff.mpr inferInstance)
  have hdimC : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C := by
    rw [connectedPuncturedCover_integralClosure_ringKrullDim_eq
      (R := R) hpos W]
    exact hdim
  have hxC : xC ∈ maximalIdeal C := by
    exact map_nonunit (algebraMap R C) x hx
  have hxC0 : xC ≠ 0 := by
    intro hzero
    apply hx0
    apply algebraMap_injective_of_field_isFractionRing
      (R := R) (S := C) U.functionField L
    simpa only [map_zero] using hzero
  have hJne : Ideal.span {xC} ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
      (maximalIdeal C).span_singleton_le_iff_mem.mpr hxC
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hJne
  let : IsLocalRing Q :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {xC}))
      Ideal.Quotient.mk_surjective
  let : ConnectedSpace (Scheme.puncturedSpectrum Q) :=
    connectedSpace_puncturedSpectrum_quotient_span_singleton_of_completeLocalDomain
      hdimC xC hxC hxC0
  let e :=
    connectedPuncturedCoverNormalizationPuncturedFiberIsoSpanSingleton
      R hpos W x hx
  exact e.hom.homeomorph.connectedSpace_iff.mpr inferInstance

end AlgebraicGeometry.FiniteEtale

end
