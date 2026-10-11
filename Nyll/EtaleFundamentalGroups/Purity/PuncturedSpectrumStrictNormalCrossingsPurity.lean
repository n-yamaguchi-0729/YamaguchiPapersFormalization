/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.Scheme
import Nyll.EtaleFundamentalGroups.Purity.Local.MaximalAdicCompletion
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumCompleteRegularLocalPurity
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumCompletionDescentFrontier
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumPurityNormalization
import Mathlib.RingTheory.Regular.Flat
import Nyll.SchemeTheory.Normalization.Normal

/-!
# Punctured purity from strict-normal-crossings stalk data

This file connects the explicit regular system carried by a strict-normal-
crossings point to complete-local punctured purity.  It also records exactly
what survives after maximal-adic completion, before any normality theorem for
the completed regular local ring is invoked.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace
open CategoryTheory.PreGaloisCategory
open RingTheory.Sequence

namespace EtaleFundamentalGroups

universe u

/-- A regular system remains a regular system after maximal-adic completion.

Regularity uses faithful flatness, while generation of the maximal ideal is
the canonical maximal-ideal calculation for the completion. -/
theorem regularSystem_map_maximalAdicCompletion
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ps : List R) (hreg : IsRegular R ps)
    (hgen : Ideal.ofList ps = maximalIdeal R) :
    let Rhat := AdicCompletion (maximalIdeal R) R
    IsRegular Rhat (ps.map (algebraMap R Rhat)) ∧
      Ideal.ofList (ps.map (algebraMap R Rhat)) = maximalIdeal Rhat := by
  dsimp only
  let Rhat := AdicCompletion (maximalIdeal R) R
  let : Module.FaithfullyFlat R Rhat :=
    maximalAdicCompletion_faithfullyFlat R
  refine ⟨hreg.of_faithfullyFlat, ?_⟩
  calc
    Ideal.ofList (ps.map (algebraMap R Rhat)) =
        (Ideal.ofList ps).map (algebraMap R Rhat) := by
      rw [Ideal.map_ofList]
    _ = (maximalIdeal R).map (algebraMap R Rhat) := by rw [hgen]
    _ = maximalIdeal Rhat := AdicCompletion.maximalIdeal_eq_map.symm

/-- The completed mapped system supplies a domain, regular-local geometry,
and the expected dimension.  Thus normality of the completed ring is the
only commutative-algebra input still needed by the arbitrary-dimensional
one-shot purity theorem. -/
theorem maximalAdicCompletion_regularSystem_geometry
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ps : List R) (hreg : IsRegular R ps)
    (hgen : Ideal.ofList ps = maximalIdeal R) :
    let Rhat := AdicCompletion (maximalIdeal R) R
    IsDomain Rhat ∧ IsRegularLocalRing Rhat ∧
      ringKrullDim Rhat = ((ps.length : ℕ∞) : WithBot ℕ∞) := by
  dsimp only
  let Rhat := AdicCompletion (maximalIdeal R) R
  obtain ⟨hregHat, hgenHat⟩ :=
    regularSystem_map_maximalAdicCompletion ps hreg hgen
  refine ⟨Kummer.isDomain_of_regularSystem _ hregHat hgenHat,
    Kummer.isRegularLocalRing_of_regularSystem _ hregHat hgenHat, ?_⟩
  simpa only [List.length_map] using
    (Kummer.regularSystem_length_eq_ringKrullDim
      (ps.map (algebraMap R Rhat)) hregHat hgenHat).symm

/-- If the explicit regular system has length two, its maximal-adic
completion has punctured purity.  This is the dimension where completed
normality is already supplied by the dimension-two regular-local theorem. -/
theorem hasPuncturedPurity_maximalAdicCompletion_of_regularSystem_length_two
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ps : List R) (hreg : IsRegular R ps)
    (hgen : Ideal.ofList ps = maximalIdeal R)
    (hlen : ps.length = 2) :
    AlgebraicGeometry.FiniteEtale.HasPuncturedPurity
      (AdicCompletion (maximalIdeal R) R) := by
  let Rhat := AdicCompletion (maximalIdeal R) R
  have hgeometry :=
    maximalAdicCompletion_regularSystem_geometry ps hreg hgen
  let : IsDomain Rhat := hgeometry.1
  let : IsRegularLocalRing Rhat := hgeometry.2.1
  apply
    AlgebraicGeometry.FiniteEtale.hasPuncturedPurity_of_isRegularLocalRing_dimension_two
      Rhat
  calc
    ringKrullDim Rhat = ((ps.length : ℕ∞) : WithBot ℕ∞) := by
      simpa only [Rhat] using hgeometry.2.2
    _ = ((2 : ℕ∞) : WithBot ℕ∞) := by simp [hlen]

/-- A two-parameter regular system discharges the purity input of the
maximal-adic completion extension theorem. -/
theorem exists_maximalAdicCompletion_extension_of_regularSystem_length_two
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ps : List R) (hreg : IsRegular R ps)
    (hgen : Ideal.ofList ps = maximalIdeal R)
    (hlen : ps.length = 2)
    (Y : AlgebraicGeometry.FiniteEtale
      (AlgebraicGeometry.Scheme.puncturedSpectrum R)) :
    ∃ X : AlgebraicGeometry.FiniteEtale
        (AlgebraicGeometry.Spec (.of
          (AdicCompletion (maximalIdeal R) R))),
      Nonempty
        ((AlgebraicGeometry.FiniteEtale.pullback
            (AlgebraicGeometry.Scheme.puncturedSpectrumInclusion
              (AdicCompletion (maximalIdeal R) R))).obj X ≅
          (AlgebraicGeometry.FiniteEtale.pullback
            (maximalAdicCompletionPuncturedSpectrumMorphism R)).obj Y) :=
  exists_maximalAdicCompletion_extension_of_hasPuncturedPurity R
    (hasPuncturedPurity_maximalAdicCompletion_of_regularSystem_length_two
      ps hreg hgen hlen) Y

end EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.IdealSheafData

open EtaleFundamentalGroups

universe u

variable {X : Scheme.{u}} {I : X.IdealSheafData} {x : X}

/-- A strict-normal-crossings point on a normal integral scheme has
punctured purity whenever its local ring is complete and has dimension at
least two.

The regular system and all local algebra except integral closedness come
from the strict-normal-crossings data; integral closedness comes from the
normal ambient scheme. -/
theorem IsStrictNormalCrossingsAt.hasPuncturedPurity_of_completeStalk
    [IsIntegral X] [IsNormalIntegral X]
    (hI : I.IsStrictNormalCrossingsAt x)
    [IsAdicComplete (maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x)]
    (hdim : ((2 : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim (X.presheaf.stalk x)) :
    FiniteEtale.HasPuncturedPurity (X.presheaf.stalk x) := by
  let A := X.presheaf.stalk x
  let hregular : IsRegularLocalRing A := hI.1
  let : IsLocalRing A := hregular.toIsLocalRing
  let : IsNoetherianRing A := hregular.toIsNoetherian
  let : IsIntegrallyClosed A :=
    IsNormalIntegral.stalk_isIntegrallyClosed x
  obtain ⟨d, _r, t, _hrpos, _hr, hparams, _hideal⟩ := hI.2
  have hparamDim :
      (((d : ℕ∞) : WithBot ℕ∞)) = ringKrullDim A := by
    simpa only [List.length_ofFn] using
      (Kummer.regularSystem_length_eq_ringKrullDim
        (List.ofFn t) hparams.1 hparams.2)
  have hdWithBot :
      ((2 : ℕ∞) : WithBot ℕ∞) ≤
        ((d : ℕ∞) : WithBot ℕ∞) :=
    hdim.trans_eq hparamDim.symm
  have hdENat : (2 : ℕ∞) ≤ (d : ℕ∞) :=
    WithBot.coe_le_coe.mp hdWithBot
  have hd : 2 ≤ d := by exact_mod_cast hdENat
  apply hasPuncturedPurity_of_complete_regularSystem_of_two_le_length
    (List.ofFn t) hparams.1 hparams.2
  simpa only [List.length_ofFn] using hd

/-- At a two-dimensional strict-normal-crossings point, purity of the
maximal-adic completion is automatic and every punctured cover acquires the
completed extension supplied by the completion comparison API. -/
theorem IsStrictNormalCrossingsAt.exists_maximalAdicCompletion_extension_of_dimension_two
    (hI : I.IsStrictNormalCrossingsAt x)
    (hdim : ringKrullDim (X.presheaf.stalk x) =
      ((2 : ℕ∞) : WithBot ℕ∞))
    (Y : FiniteEtale
      (Scheme.puncturedSpectrum (X.presheaf.stalk x))) :
    let A := X.presheaf.stalk x
    let hregular : IsRegularLocalRing A := hI.1
    letI : IsLocalRing A := hregular.toIsLocalRing
    letI : IsNoetherianRing A := hregular.toIsNoetherian
    ∃ Z : FiniteEtale
        (Spec (.of (AdicCompletion
          (maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x)))),
      Nonempty
        ((FiniteEtale.pullback
            (Scheme.puncturedSpectrumInclusion
              (AdicCompletion
                (maximalIdeal (X.presheaf.stalk x))
                (X.presheaf.stalk x)))).obj Z ≅
          (FiniteEtale.pullback
            (EtaleFundamentalGroups.maximalAdicCompletionPuncturedSpectrumMorphism
              (X.presheaf.stalk x))).obj Y) := by
  dsimp only
  let A := X.presheaf.stalk x
  let hregular : IsRegularLocalRing A := hI.1
  let : IsLocalRing A := hregular.toIsLocalRing
  let : IsNoetherianRing A := hregular.toIsNoetherian
  obtain ⟨d, _r, t, _hrpos, _hr, hparams, _hideal⟩ := hI.2
  have hparamDim :
      ((d : ℕ∞) : WithBot ℕ∞) = ringKrullDim A := by
    simpa only [List.length_ofFn] using
      (Kummer.regularSystem_length_eq_ringKrullDim
        (List.ofFn t) hparams.1 hparams.2)
  have hdWithBot :
      ((d : ℕ∞) : WithBot ℕ∞) =
        ((2 : ℕ∞) : WithBot ℕ∞) :=
    hparamDim.trans hdim
  have hdENat : (d : ℕ∞) = (2 : ℕ∞) :=
    WithBot.coe_eq_coe.mp hdWithBot
  have hd : d = 2 := by exact_mod_cast hdENat
  apply
    EtaleFundamentalGroups.exists_maximalAdicCompletion_extension_of_regularSystem_length_two
      (List.ofFn t) hparams.1 hparams.2
  simp [hd]

/-- At the same complete strict-normal-crossings stalk, the canonical
function-field normalization of every connected punctured cover is already
finite etale.  This is the normalization endpoint used by the boundary
extension pipeline. -/
theorem
IsStrictNormalCrossingsAt.connectedPuncturedCoverGenericNormalization_isFiniteEtale_of_completeStalk
    [IsIntegral X] [IsNormalIntegral X]
    (hI : I.IsStrictNormalCrossingsAt x)
    [IsAdicComplete (maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x)]
    (hdim : ((2 : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim (X.presheaf.stalk x))
    (W : FiniteEtale
      (Scheme.puncturedSpectrum (X.presheaf.stalk x))) [IsConnected W] :
    let A := X.presheaf.stalk x
    let hregular : IsRegularLocalRing A := hI.1
    letI : IsLocalRing A := hregular.toIsLocalRing
    letI : IsNoetherianRing A := hregular.toIsNoetherian
    let hdomain : IsDomain A := by
      obtain ⟨_d, _r, t, _hrpos, _hr, hparams, _hideal⟩ := hI.2
      exact Kummer.isDomain_of_regularSystem
        (List.ofFn t) hparams.1 hparams.2
    letI : IsDomain A := hdomain
    let hnormal : IsIntegrallyClosed A :=
      IsNormalIntegral.stalk_isIntegrallyClosed x
    letI : IsIntegrallyClosed A := hnormal
    let hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim A :=
      (by norm_num : (1 : WithBot ℕ∞) ≤ (2 : ℕ∞)).trans hdim
    let U := Scheme.puncturedSpectrum A
    let j : U ⟶ Spec (.of A) := Scheme.puncturedSpectrumInclusion A
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim A hpos
    letI : IsOpenImmersion j := by
      dsimp only [j, Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : IsNormalIntegral U := inferInstance
    letI : IsLocallyNoetherian U := inferInstance
    IsFiniteEtale
      (FiniteEtale.connectedCoverGenericComposite W ≫
        Scheme.puncturedSpectrumInclusion
          (X.presheaf.stalk x)).fromNormalization := by
  dsimp only
  let A := X.presheaf.stalk x
  let hregular : IsRegularLocalRing A := hI.1
  let : IsLocalRing A := hregular.toIsLocalRing
  let : IsNoetherianRing A := hregular.toIsNoetherian
  obtain ⟨_d, _r, t, _hrpos, _hr, hparams, _hideal⟩ := hI.2
  let : IsDomain A :=
    Kummer.isDomain_of_regularSystem
      (List.ofFn t) hparams.1 hparams.2
  let : IsIntegrallyClosed A :=
    IsNormalIntegral.stalk_isIntegrallyClosed x
  have hpurity : FiniteEtale.HasPuncturedPurity A :=
    hI.hasPuncturedPurity_of_completeStalk hdim
  have hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim A :=
    (by norm_num : (1 : WithBot ℕ∞) ≤ (2 : ℕ∞)).trans hdim
  let U := Scheme.puncturedSpectrum A
  let j : U ⟶ Spec (.of A) := Scheme.puncturedSpectrumInclusion A
  let : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim A hpos
  let : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : IsNormalIntegral U := inferInstance
  let : IsLocallyNoetherian U := inferInstance
  exact
    FiniteEtale.connectedPuncturedCoverGenericNormalization_isFiniteEtale_of_hasPuncturedPurity
      A hpurity W

end AlgebraicGeometry.Scheme.IdealSheafData

end
