/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedNormalizationFinite
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedRestriction
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumQuotient
import Nyll.EtaleFundamentalGroups.FiniteEtale.Henselian.CompleteOrthogonalIdempotents
import Nyll.EtaleFundamentalGroups.Purity.Local.IdealAdicComplete
import Nyll.EtaleFundamentalGroups.Purity.Local.CompleteQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite

/-!
# Finite normalization sources for punctured hypersurface restriction

For a connected finite-etale cover of a positive-dimensional punctured
normal local spectrum, its function-field normalization over the full
spectrum is finite.  Pulling that actual finite normalization back to a
local quotient gives the closed-fibre source whose puncture controls the
connected-cover form of local Lefschetz.

This file constructs that source and the canonical comparison with the
restriction of the original cover.  No connectedness or effectivity
conclusion is assumed.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace IsLocalRing
open CategoryTheory.PreGaloisCategory
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteEtale

universe u

local instance finiteHasAffinePropertyLefschetz : HasAffineProperty
    (@IsFinite : MorphismProperty Scheme.{u}) (affineAnd RingHom.Finite) := by
  rw [HasAffineProperty.affineAnd_iff
    (@IsFinite : MorphismProperty Scheme.{u})
    RingHom.finite_respectsIso RingHom.finite_localizationPreserves.away
    RingHom.finite_ofLocalizationSpan]
  intro X Y f
  exact isFinite_iff f

variable (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
  [IsNoetherianRing R] [IsIntegrallyClosed R]

omit [IsDomain R] [IsIntegrallyClosed R] in
/-- Let a finite domain algebra lie over a complete Noetherian local ring.
For every ideal of the base contained in its maximal ideal, the spectrum of
the corresponding quotient of the finite algebra is connected.

The proof is the genuine completeness input: an idempotent of the quotient
lifts by Hensel's lemma, and the lift is trivial because the finite algebra
is a domain. -/
theorem connectedSpace_spec_quotient_map_of_finiteDomain_of_maximalAdicComplete
    {C : Type u} [CommRing C] [IsDomain C] [Algebra R C]
    [Module.Finite R C] [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    ConnectedSpace
      (Spec (.of (C ⧸ I.map (algebraMap R C)))) := by
  let J : Ideal C := I.map (algebraMap R C)
  let Q := C ⧸ J
  let q : C →+* Q := Ideal.Quotient.mk J
  let : IsAdicComplete I R :=
    EtaleFundamentalGroups.Purity.isAdicComplete_of_le_maximalIdeal
      (M := R) I hI
  let : HenselianRing C J :=
    (open _root_.ValuationTheory.DiscreteValuationField in
      henselianRing_map_algebraMap_of_moduleFinite_of_isAdicComplete)
  have hJne : J ≠ ⊤ := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal C
    apply ne_top_of_le_ne_top hM.ne_top
    exact (HenselianRing.jac (R := C) (I := J)).trans
      (sInf_le ⟨bot_le, hM⟩)
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hJne
  have hker : RingHom.ker q = J := Ideal.mk_ker
  let : HenselianRing C (RingHom.ker q) := by
    rw [hker]
    infer_instance
  rw [connectedSpace_iff_clopen]
  refine ⟨inferInstance, ?_⟩
  intro s hs
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  obtain ⟨e', he', he'map⟩ :=
    ValuationTheory.DiscreteValuationField.exists_idempotent_lift_of_surjective_henselianRing_ker
      q Ideal.Quotient.mk_surjective e he
  have he_cases : e = 0 ∨ e = 1 := by
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp he' with he' | he'
    · left
      rw [← he'map, he', map_zero]
    · right
      rw [← he'map, he', map_one]
  rcases he_cases with rfl | rfl
  · left
    rw [PrimeSpectrum.basicOpen_zero]
    rfl
  · right
    rw [PrimeSpectrum.basicOpen_one]
    rfl

omit [IsDomain R] [IsIntegrallyClosed R] in
/-- Geometric form of
`connectedSpace_spec_quotient_map_of_finiteDomain_of_maximalAdicComplete`:
the closed fibre of a finite affine domain over a complete Noetherian local
base is connected. -/
theorem connectedSpace_pullback_spec_quotient_of_finiteDomain_of_maximalAdicComplete
    {C : Type u} [CommRing C] [IsDomain C] [Algebra R C]
    [Module.Finite R C] [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    ConnectedSpace
      ((Limits.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R C)))
        (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I))))) : Scheme.{u}) := by
  let Q := C ⧸ I.map (algebraMap R C)
  let eRing : Q ≃+* C ⊗[R] (R ⧸ I) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C I).toRingEquiv
  let eScheme :
      Limits.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R C)))
          (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I)))) ≅
        Spec (.of Q) :=
    pullbackSpecIso R C (R ⧸ I) ≪≫
      Scheme.Spec.mapIso eRing.toCommRingCatIso.op
  let : ConnectedSpace (Spec (.of Q)) :=
    connectedSpace_spec_quotient_map_of_finiteDomain_of_maximalAdicComplete
      R I hI
  exact eScheme.hom.homeomorph.connectedSpace_iff.mpr inferInstance

/-- Pulling back two isomorphic objects over the same base gives isomorphic
pullbacks. -/
private noncomputable def pullbackIsoOfIsoOver
    {A B X Y : Scheme.{u}} (e : A ≅ B)
    (f : A ⟶ X) (h : B ⟶ X) (g : Y ⟶ X)
    (w : e.hom ≫ h = f) :
    Limits.pullback f g ≅ Limits.pullback h g :=
  asIso <| Limits.pullback.map f g h g e.hom (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using w.symm)
    (by rw [Category.comp_id, Category.id_comp])

omit [IsDomain R] [IsIntegrallyClosed R] in
/-- The closed fibre of any finite morphism with integral source over a
complete Noetherian local affine scheme is connected.  Passing to global
sections reduces this to the finite-domain quotient theorem above. -/
theorem connectedSpace_normalizationClosedFiber_of_isFinite_of_isIntegral
    {Z : Scheme.{u}} (z : Z ⟶ Spec (.of R)) [IsFinite z] [IsIntegral Z]
    [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    ConnectedSpace
      ((Limits.pullback z
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) : Scheme.{u}) := by
  let : IsAffine Z := isAffine_of_isAffineHom z
  let C : Type u := Γ(Z, ⊤)
  let phi : R →+* C :=
    z.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let : Algebra R C := phi.toAlgebra
  have hzApp : z.appTop.hom.Finite := by
    have hz : IsFinite z := inferInstance
    rw [HasAffineProperty.iff_of_isAffine (P := (@IsFinite : MorphismProperty Scheme.{u}))
        (Q := affineAnd RingHom.Finite)] at hz
    exact hz.2
  have hphi : phi.Finite := by
    exact RingHom.Finite.comp hzApp
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.finite
  let : Module.Finite R C := by
    change phi.Finite
    exact hphi
  let e : Z ≅ Spec (.of C) := Z.isoSpec
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom phi) = z := by
    have hphiCat : CommRingCat.ofHom phi =
        (Scheme.ΓSpecIso (.of R)).inv ≫ z.appTop := by
      ext r
      rfl
    have hSpec :
        Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ z.appTop) =
          Spec.map z.appTop ≫
            Spec.map (Scheme.ΓSpecIso (.of R)).inv :=
      Spec.map_comp _ _
    rw [hphiCat, hSpec]
    change Z.isoSpec.hom ≫ Spec.map z.appTop ≫
        Spec.map (Scheme.ΓSpecIso (.of R)).inv = z
    rw [Scheme.isoSpec_hom_naturality_assoc]
    rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.comp_id]
  let eFiber :
      Limits.pullback z
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
        Limits.pullback (Spec.map (CommRingCat.ofHom phi))
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    pullbackIsoOfIsoOver e z (Spec.map (CommRingCat.ofHom phi))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) he
  let : ConnectedSpace
      ((Limits.pullback (Spec.map (CommRingCat.ofHom phi))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) : Scheme.{u}) := by
    change ConnectedSpace
      ((Limits.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R C)))
        (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I))))) : Scheme.{u})
    exact
      connectedSpace_pullback_spec_quotient_of_finiteDomain_of_maximalAdicComplete
        R I hI
  exact eFiber.hom.homeomorph.connectedSpace_iff.mpr inferInstance

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
private theorem puncturedSpectrumFunctionFieldRingEquiv_apply_germ_source
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
private theorem specFunctionField_algebraMap_ΓSpecIso_hom_source
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

/-- The relative function-field normalization attached to a connected
finite-etale cover of a positive-dimensional punctured normal local
spectrum is finite over the full spectrum. -/
theorem connectedPuncturedCoverGenericNormalization_isFinite
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
    IsFinite (connectedCoverGenericComposite W ≫ j).fromNormalization := by
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
  let : IsNormalIntegral U := inferInstance
  let : IsLocallyNoetherian U := inferInstance
  let : Nonempty (⊤ : X.Opens) :=
    ⟨⟨genericPoint X, by trivial⟩⟩
  let : Nonempty (⊤ : U.Opens) :=
    ⟨⟨genericPoint U, by trivial⟩⟩
  let : Algebra R X.functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
  let K : Type u := U.functionField
  let : Algebra R K :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  let : IsFractionRing R K :=
    puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let L : Type u := W.left.functionField
  let : Algebra K L :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : Algebra R L :=
    ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional K L :=
    EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : Algebra.IsSeparable K L :=
    EtaleFundamentalGroups.isSeparable_functionField_of_finiteEtale_isConnected W
  let f : Spec (.of L) ⟶ U := connectedCoverGenericComposite W
  let g : Spec (.of L) ⟶ X := f ≫ j
  let : QuasiCompact g := inferInstance
  let : QuasiSeparated g := inferInstance
  let A : Type u := Γ(X, ⊤)
  let S : Type u := Γ(Spec (.of L), g ⁻¹ᵁ (⊤ : X.Opens))
  let : Algebra A S := g.appTop.hom.toAlgebra
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
    rw [← puncturedSpectrumFunctionFieldRingEquiv_apply_germ_source R hpos a]
    change (puncturedSpectrumFunctionFieldRingEquivOfPositiveDimension R hpos)
        (X.germToFunctionField ⊤ a) =
      (puncturedSpectrumFunctionFieldRingEquivOfPositiveDimension R hpos)
        (algebraMap R X.functionField (eBase a))
    congr 1
    exact (specFunctionField_algebraMap_ΓSpecIso_hom_source R a).symm
  let C : Type u := integralClosure A S
  let CR : Type u := integralClosure R L
  let : Module.Finite R CR :=
    connectedPuncturedCover_integralClosure_finite_of_positiveDimension
      R hpos W
  let : Algebra A CR :=
    EtaleFundamentalGroups.integralClosureBaseRingAlgebra eBase
  let eC : C ≃ₐ[A] CR :=
    EtaleFundamentalGroups.integralClosureAlgEquivOfBaseAndAmbientEquiv
      eBase eAmbient hCompat
  let : Algebra A R := eBase.toRingHom.toAlgebra
  let : IsScalarTower A R CR := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite A R := eBase.finite
  let : Module.Finite A CR := Module.Finite.trans R CR
  let : Module.Finite A C := Module.Finite.equiv eC.symm.toLinearEquiv
  have hfiniteC : (algebraMap A C).Finite := by
    change Module.Finite A C
    infer_instance
  have hApp : g.fromNormalization.appTop.hom.Finite := by
    change (g.fromNormalization.app (⊤ : X.Opens)).hom.Finite
    rw [g.fromNormalization_app (isAffineOpen_top X)]
    exact RingHom.Finite.comp
      (g.normalizationObjIso (isAffineOpen_top X)).symm.commRingCatIsoToRingEquiv.finite
      hfiniteC
  rw [HasAffineProperty.iff_of_isAffine (P := (@IsFinite : MorphismProperty Scheme.{u}))
        (Q := affineAnd RingHom.Finite)]
  exact ⟨isAffine_of_isAffineHom g.fromNormalization, hApp⟩

/-- The finite closed-fibre normalization over a quotient of the local
base.  Its further restriction to the quotient puncture is the concrete
source in the connected-cover Lefschetz problem. -/
noncomputable def connectedPuncturedCoverNormalizationClosedFiber
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (I : Ideal R) : Over (Spec (.of (R ⧸ I))) := by
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
  letI : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  letI : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U := isIntegral_of_isOpenImmersion j
  let Z := (connectedCoverGenericComposite W ≫ j).fromNormalization
  let q : Spec (.of (R ⧸ I)) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  exact Over.mk (Limits.pullback.snd Z q)

/-- The normalization closed fibre is finite over the quotient spectrum. -/
theorem connectedPuncturedCoverNormalizationClosedFiber_hom_isFinite
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (I : Ideal R) :
    IsFinite
      (connectedPuncturedCoverNormalizationClosedFiber R hpos W I).hom := by
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  let : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  let : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let Z : Scheme.{u} :=
    (connectedCoverGenericComposite W ≫ j).normalization
  let z : Z ⟶ X :=
    (connectedCoverGenericComposite W ≫ j).fromNormalization
  let : IsFinite z :=
    connectedPuncturedCoverGenericNormalization_isFinite R hpos W
  unfold connectedPuncturedCoverNormalizationClosedFiber
  change IsFinite (Limits.pullback.snd z
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
  infer_instance

/-- The normalization closed fibre is affine. -/
theorem connectedPuncturedCoverNormalizationClosedFiber_isAffine
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (I : Ideal R) :
    IsAffine
      (connectedPuncturedCoverNormalizationClosedFiber R hpos W I).left := by
  let : IsFinite
      (connectedPuncturedCoverNormalizationClosedFiber R hpos W I).hom :=
    connectedPuncturedCoverNormalizationClosedFiber_hom_isFinite
      R hpos W I
  exact isAffine_of_isAffineHom
    (connectedPuncturedCoverNormalizationClosedFiber R hpos W I).hom

/-- For a complete base, the entire normalization closed fibre is connected.
The remaining local-Lefschetz issue is precisely whether deleting the finite
set over the closed point preserves this connectedness. -/
theorem connectedPuncturedCoverNormalizationClosedFiber_connectedSpace
    [IsAdicComplete (maximalIdeal R) R]
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    ConnectedSpace
      (connectedPuncturedCoverNormalizationClosedFiber R hpos W I).left := by
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  let : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  let : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let z :
      (connectedCoverGenericComposite W ≫ j).normalization ⟶ X :=
    (connectedCoverGenericComposite W ≫ j).fromNormalization
  let : IsFinite z :=
    connectedPuncturedCoverGenericNormalization_isFinite R hpos W
  unfold connectedPuncturedCoverNormalizationClosedFiber
  change ConnectedSpace
    ((Limits.pullback z
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) : Scheme.{u})
  exact
    connectedSpace_normalizationClosedFiber_of_isFinite_of_isIntegral
      R z I hI

/-- The puncture of the finite normalization closed fibre. -/
noncomputable def connectedPuncturedCoverNormalizationPuncturedFiber
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) : Scheme.{u} := by
  letI : Nontrivial (R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
  letI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  exact Limits.pullback
    (connectedPuncturedCoverNormalizationClosedFiber R hpos W I).hom
    (Scheme.puncturedSpectrumInclusion (R ⧸ I))

/-- The restriction of a connected punctured cover to a quotient puncture
is canonically the puncture of the closed fibre of its finite generic-field
normalization.  This identifies the actual source whose connectedness is
the local Lefschetz input. -/
noncomputable def connectedPuncturedCoverQuotientRestrictionIso
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    ((pullback (Scheme.puncturedSpectrumQuotientMorphism R I hI)).obj W).left ≅
      connectedPuncturedCoverNormalizationPuncturedFiber R hpos W I hI := by
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  letI : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  letI : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U := isIntegral_of_isOpenImmersion j
  letI : IsNormalIntegral U := inferInstance
  letI : IsLocallyNoetherian U := inferInstance
  letI : Nontrivial (R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
  letI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let U0 := Scheme.puncturedSpectrum (R ⧸ I)
  let jI : U0 ⟶ Spec (.of (R ⧸ I)) :=
    Scheme.puncturedSpectrumInclusion (R ⧸ I)
  let q : Spec (.of (R ⧸ I)) ⟶ X :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let g : U0 ⟶ U :=
    Scheme.puncturedSpectrumQuotientMorphism R I hI
  let z : Scheme.{u} :=
    (connectedCoverGenericComposite W ≫ j).normalization
  let Z : z ⟶ X :=
    (connectedCoverGenericComposite W ≫ j).fromNormalization
  let e : W.left ≅ Limits.pullback Z j :=
    connectedCoverGenericNormalizationPullbackIso W j
  have he : e.hom ≫ Limits.pullback.snd Z j = W.hom :=
    connectedCoverGenericNormalizationPullbackIso_hom_snd W j
  have hg : g ≫ j = jI ≫ q :=
    Scheme.puncturedSpectrumQuotientMorphism_comp_inclusion R I hI
  change Limits.pullback W.hom g ≅
    Limits.pullback (Limits.pullback.snd Z q) jI
  exact
    pullbackIsoOfIsoOver e W.hom (Limits.pullback.snd Z j) g he ≪≫
      pullbackLeftPullbackSndIso Z j g ≪≫
      Limits.pullback.congrHom rfl hg ≪≫
      (pullbackLeftPullbackSndIso Z q jI).symm

/-- The connectedness question for the quotient restriction is exactly the
connectedness of the punctured finite-normalization closed fibre. -/
theorem connectedPuncturedCoverQuotientRestriction_connectedSpace_iff
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    ConnectedSpace
        ((pullback
          (Scheme.puncturedSpectrumQuotientMorphism R I hI)).obj W).left ↔
      ConnectedSpace
        (connectedPuncturedCoverNormalizationPuncturedFiber
          R hpos W I hI) :=
  (connectedPuncturedCoverQuotientRestrictionIso
    R hpos W I hI).hom.homeomorph.connectedSpace_iff

/-- Over a connected quotient puncture, categorical connectedness of the
restricted finite-etale cover is equivalent to connectedness of the
punctured finite-normalization closed fibre. -/
theorem connectedPuncturedCoverQuotientRestriction_isConnected_iff
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (I : Ideal R) (hI : I ≤ maximalIdeal R)
    [IsLocalRing (R ⧸ I)]
    [ConnectedSpace (Scheme.puncturedSpectrum (R ⧸ I))] :
    IsConnected
        ((pullback
          (Scheme.puncturedSpectrumQuotientMorphism R I hI)).obj W) ↔
      ConnectedSpace
        (connectedPuncturedCoverNormalizationPuncturedFiber
          R hpos W I hI) := by
  constructor
  · intro h
    let : IsConnected
        ((pullback
          (Scheme.puncturedSpectrumQuotientMorphism R I hI)).obj W) := h
    let : ConnectedSpace
        ((pullback
          (Scheme.puncturedSpectrumQuotientMorphism R I hI)).obj W).left :=
      connectedSpace_left_of_isConnected _
    exact
      (connectedPuncturedCoverQuotientRestriction_connectedSpace_iff
        R hpos W I hI).mp inferInstance
  · intro h
    let : ConnectedSpace
        (connectedPuncturedCoverNormalizationPuncturedFiber
          R hpos W I hI) := h
    let : ConnectedSpace
        ((pullback
          (Scheme.puncturedSpectrumQuotientMorphism R I hI)).obj W).left :=
      (connectedPuncturedCoverQuotientRestriction_connectedSpace_iff
        R hpos W I hI).mpr inferInstance
    exact isConnected_of_connectedSpace_left _

end AlgebraicGeometry.FiniteEtale

end
