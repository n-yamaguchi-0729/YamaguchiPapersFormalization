/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedNormalizationFiberComparison
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumPurityNormalization

/-!
# Literal integral closures under punctured purity

Punctured purity makes the canonical relative function-field normalization
finite etale.  The normalization comparison with the spectrum of the literal
integral closure then transports this scheme-level conclusion back to the
underlying algebra.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Under punctured purity, the literal integral closure attached to a
connected punctured cover is etale over the local base. -/
theorem connectedPuncturedCover_integralClosure_etale_of_hasPuncturedPurity
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegral (Scheme.puncturedSpectrum R)]
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (hpurity : HasPuncturedPurity R)
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
    Algebra.Etale R (integralClosure R W.left.functionField) := by
  dsimp only
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ Spec (.of R) := Scheme.puncturedSpectrumInclusion R
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
  let C := integralClosure R W.left.functionField
  let g : Spec (.of W.left.functionField) ⟶ Spec (.of R) :=
    connectedCoverGenericComposite W ≫ j
  let z : g.normalization ⟶ Spec (.of R) := g.fromNormalization
  let e : g.normalization ≅ Spec (.of C) :=
    connectedPuncturedCoverGenericNormalizationIsoSpecIntegralClosure
      R hpos W
  have hz : IsFiniteEtale z :=
    connectedPuncturedCoverGenericNormalization_isFiniteEtale_of_hasPuncturedPurity
      R hpurity W
  have hcomp : IsFiniteEtale
      (e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R C))) := by
    rw [connectedPuncturedCoverGenericNormalizationIsoSpecIntegralClosure_hom_fromSpec]
    exact hz
  let : MorphismProperty.RespectsIso
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) := by
    apply MorphismProperty.RespectsIso.mk
    · intro _ _ _ _ f hf
      let : IsFinite f := hf.toIsFinite
      let : Etale f := hf.toEtale
      exact ⟨⟩
    · intro _ _ _ _ f hf
      let : IsFinite f := hf.toIsFinite
      let : Etale f := hf.toEtale
      exact ⟨⟩
  have hSpec : IsFiniteEtale
      (Spec.map (CommRingCat.ofHom (algebraMap R C))) :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @IsFiniteEtale) e.hom _).mp hcomp
  rw [IsFiniteEtale.SpecMap_iff] at hSpec
  exact hSpec.toEtale

end AlgebraicGeometry.FiniteEtale

end
