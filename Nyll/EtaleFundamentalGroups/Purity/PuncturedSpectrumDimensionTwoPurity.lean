/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedNormalization
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedRestriction
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumFunctionField
import Nyll.EtaleFundamentalGroups.FiniteEtale.ConnectedReduction

/-!
# Purity for two-dimensional regular local punctures

This file algebraizes connected finite-etale covers of the punctured spectrum
by normalizing the full spectrum in their function fields.  The normalization
is finite etale by the two-dimensional integral-closure theorem, and its
restriction is identified with the original connected cover.  Finite
coproduct decomposition then handles arbitrary covers.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]

private theorem puncturedSpectrum_nonempty_dimension_two'
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞)) :
    Nonempty (Scheme.puncturedSpectrum R) := by
  apply Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R
  rw [hdim]
  norm_num

/-- The function-field equivalence induced by the punctured open immersion
intertwines germs of global sections. -/
private theorem puncturedSpectrumFunctionFieldRingEquiv_apply_germ
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

omit [IsRegularLocalRing R] in
/-- The literal fraction-field algebra on an affine spectrum is the germ of
global sections, after the standard global-sections equivalence. -/
private theorem specFunctionField_algebraMap_ΓSpecIso_hom
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

/-- The normalization of the full local spectrum in the function field of a
connected punctured cover, packaged as a finite-etale cover. -/
noncomputable def connectedPuncturedCoverGenericNormalizationExtension
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    FiniteEtale (Spec (.of R)) := by
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  have hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
    rw [hdim]
    norm_num
  letI : IsIntegrallyClosed R :=
    EtaleFundamentalGroups.SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hdim
  letI : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  letI : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U := isIntegral_of_isOpenImmersion j
  letI : IsNormalIntegral U := inferInstance
  letI : IsLocallyNoetherian U := inferInstance
  letI : Nonempty (⊤ : X.Opens) :=
    ⟨⟨genericPoint X, by trivial⟩⟩
  letI : Nonempty (⊤ : U.Opens) :=
    ⟨⟨genericPoint U, by trivial⟩⟩
  letI : Algebra R X.functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
  let K : Type u := U.functionField
  letI : Algebra R K :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  letI : IsFractionRing R K :=
    puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
  letI : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let L : Type u := W.left.functionField
  letI : Algebra K L :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  letI : Algebra R L :=
    ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional K L :=
    EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
  letI : Algebra.IsSeparable K L :=
    EtaleFundamentalGroups.isSeparable_functionField_of_finiteEtale_isConnected W
  let f : Spec (.of L) ⟶ U := connectedCoverGenericComposite W
  let g : Spec (.of L) ⟶ X := f ≫ j
  letI : QuasiCompact g := inferInstance
  letI : QuasiSeparated g := inferInstance
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
    change algebraMap K L (U.germToFunctionField ⊤ (j.appTop a)) =
      algebraMap K L (algebraMap R K (eBase a))
    congr 1
    rw [← puncturedSpectrumFunctionFieldRingEquiv_apply_germ R hpos a]
    change (puncturedSpectrumFunctionFieldRingEquivOfPositiveDimension R hpos)
        (X.germToFunctionField ⊤ a) =
      (puncturedSpectrumFunctionFieldRingEquivOfPositiveDimension R hpos)
        (algebraMap R X.functionField (eBase a))
    congr 1
    exact (specFunctionField_algebraMap_ΓSpecIso_hom R a).symm
  let C : Type u := integralClosure A S
  have hEtaleC : Algebra.Etale A C :=
    EtaleFundamentalGroups.integralClosure_etale_of_baseAndAmbientEquiv
      eBase eAmbient hCompat
        (connectedPuncturedCover_integralClosure_etale R hdim W)
  letI : Algebra.Etale A C := hEtaleC
  let CR : Type u := integralClosure R L
  letI : Module.Finite R CR := IsIntegralClosure.finite R K L CR
  letI : Algebra A CR :=
    EtaleFundamentalGroups.integralClosureBaseRingAlgebra eBase
  let eC : C ≃ₐ[A] CR :=
    EtaleFundamentalGroups.integralClosureAlgEquivOfBaseAndAmbientEquiv
      eBase eAmbient hCompat
  letI : Algebra A R := eBase.toRingHom.toAlgebra
  letI : IsScalarTower A R CR := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite A R := eBase.finite
  letI : Module.Finite A CR := Module.Finite.trans R CR
  letI : Module.Finite A C := Module.Finite.equiv eC.symm.toLinearEquiv
  have hFiniteEtaleC : (algebraMap A C).FiniteEtale := by
    rw [RingHom.finiteEtale_algebraMap_iff, Algebra.finiteEtale_iff]
    exact ⟨inferInstance, inferInstance⟩
  have hApp : g.fromNormalization.appTop.hom.FiniteEtale := by
    change (g.fromNormalization.app (⊤ : X.Opens)).hom.FiniteEtale
    rw [g.fromNormalization_app (isAffineOpen_top X)]
    exact RingHom.FiniteEtale.respectsIso.left
      (algebraMap A C)
      (g.normalizationObjIso (isAffineOpen_top X)).symm.commRingCatIsoToRingEquiv
      hFiniteEtaleC
  have hFiniteEtale : IsFiniteEtale g.fromNormalization := by
    rw [HasAffineProperty.iff_of_isAffine (P := @IsFiniteEtale)]
    exact ⟨isAffine_of_isAffineHom g.fromNormalization, hApp⟩
  exact @FiniteEtale.mk X _ g.fromNormalization hFiniteEtale

/-- A connected punctured cover is canonically the restriction of its
function-field normalization over the full spectrum. -/
noncomputable def
    connectedPuncturedCoverGenericNormalizationExtensionRestrictionIso
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    W ≅ (pullback (Scheme.puncturedSpectrumInclusion R)).obj
      (connectedPuncturedCoverGenericNormalizationExtension R hdim W) := by
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  have hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
    rw [hdim]
    norm_num
  letI : IsIntegrallyClosed R :=
    EtaleFundamentalGroups.SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hdim
  letI : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  letI : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U := isIntegral_of_isOpenImmersion j
  letI : IsNormalIntegral U := inferInstance
  letI : IsLocallyNoetherian U := inferInstance
  letI : QuasiCompact j := inferInstance
  letI : QuasiSeparated j := inferInstance
  exact MorphismProperty.Over.isoMk
    (connectedCoverGenericNormalizationPullbackIso W j)
    (connectedCoverGenericNormalizationPullbackIso_hom_snd W j)

/-- Every finite-etale cover of the punctured spectrum of a
two-dimensional regular local domain extends over the full spectrum. -/
theorem hasPuncturedPurity_of_isRegularLocalRing_dimension_two
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞)) :
    HasPuncturedPurity R := by
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  have hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
    rw [hdim]
    norm_num
  let : IsIntegrallyClosed R :=
    EtaleFundamentalGroups.SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hdim
  let : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  let : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : ConnectedSpace U := inferInstance
  change (pullback j).EssSurj
  apply pullback_essSurj_of_connected j
  intro W hW
  let : IsConnected W := hW
  exact ⟨connectedPuncturedCoverGenericNormalizationExtension R hdim W,
    ⟨(connectedPuncturedCoverGenericNormalizationExtensionRestrictionIso
      R hdim W).symm⟩⟩


end AlgebraicGeometry.FiniteEtale
