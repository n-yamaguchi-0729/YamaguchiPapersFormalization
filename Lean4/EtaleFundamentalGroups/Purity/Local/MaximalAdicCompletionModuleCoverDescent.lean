/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.Local.MaximalAdicCompletionModuleGluingData
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Faithfully flat descent for the maximal-adic module cover

Let `Rhat` be the completion of a Noetherian local ring `R` at its maximal
ideal, and let `R_i` be the principal localizations associated to a finite
generating family of that ideal.  This file packages the single affine cover

`R -> Rhat x product_i R_i`.

The cover is faithfully flat because its completion factor already is.  We
then apply comonadic module descent to a genuine descent coalgebra on this
cover.  Its descended module is presented explicitly as the equalizer of the
coalgebra map and the adjunction unit.  The main constructions identify base
change of this equalizer with the cover module, with the completion chart, and
with every principal chart.

The final structure records when an abstract `ModuleFormalGluingDatum` is
identified, at the level of its degree-zero and degree-one diagrams, with such
a full cover descent coalgebra.  Its chart comparison isomorphisms are derived
from those diagram identifications; they are not fields of the structure.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The maximal-adic completion occurring in the module cover. -/
abbrev MaximalAdicModuleCoverCompletion :=
  AdicCompletion (maximalIdeal R) R

/-- The finite family indexing the chosen generators of the maximal ideal. -/
abbrev MaximalAdicModuleCoverGeneratorIndex :=
  AlgebraicGeometry.Scheme.puncturedSpectrumGeneratorIndex R

/-- A member of the chosen generating family of the maximal ideal. -/
abbrev maximalAdicModuleCoverGenerator
    (i : MaximalAdicModuleCoverGeneratorIndex R) : R :=
  AlgebraicGeometry.Scheme.puncturedSpectrumGenerator R i

/-- The principal localization associated to a chosen generator. -/
abbrev MaximalAdicModuleCoverLocalization
    (i : MaximalAdicModuleCoverGeneratorIndex R) :=
  Localization (Submonoid.powers (maximalAdicModuleCoverGenerator R i))

/-- The single affine algebra containing the completion chart and all
principal charts. -/
abbrev MaximalAdicModuleCover :=
  MaximalAdicModuleCoverCompletion R ×
    ((i : MaximalAdicModuleCoverGeneratorIndex R) →
      MaximalAdicModuleCoverLocalization R i)

/-- Projection of the module cover to its completion factor. -/
def maximalAdicModuleCoverToCompletion :
    MaximalAdicModuleCover R →+* MaximalAdicModuleCoverCompletion R :=
  RingHom.fst _ _

/-- Projection of the module cover to one principal-localization factor. -/
def maximalAdicModuleCoverToPrincipal
    (i : MaximalAdicModuleCoverGeneratorIndex R) :
    MaximalAdicModuleCover R →+* MaximalAdicModuleCoverLocalization R i :=
  (Pi.evalRingHom
      (fun i : MaximalAdicModuleCoverGeneratorIndex R ↦
        MaximalAdicModuleCoverLocalization R i) i).comp
    (RingHom.snd _ _)

@[simp]
theorem maximalAdicModuleCoverToCompletion_comp :
    (maximalAdicModuleCoverToCompletion R).comp
        (algebraMap R (MaximalAdicModuleCover R)) =
      algebraMap R (MaximalAdicModuleCoverCompletion R) := by
  ext r
  rfl

@[simp]
theorem maximalAdicModuleCoverToPrincipal_comp
    (i : MaximalAdicModuleCoverGeneratorIndex R) :
    (maximalAdicModuleCoverToPrincipal R i).comp
        (algebraMap R (MaximalAdicModuleCover R)) =
      algebraMap R (MaximalAdicModuleCoverLocalization R i) := by
  ext r
  rfl

section Noetherian

variable [IsNoetherianRing R]

/-- The completion/principal product is flat over the original local ring. -/
theorem maximalAdicModuleCover_flat :
    Module.Flat R (MaximalAdicModuleCover R) := by
  infer_instance

/-- The completion/principal product is faithfully flat over the original
local ring.  Faithfulness is detected by the completion factor. -/
theorem maximalAdicModuleCover_faithfullyFlat :
    Module.FaithfullyFlat R (MaximalAdicModuleCover R) := by
  rw [Module.FaithfullyFlat.iff_flat_and_lTensor_faithful]
  refine ⟨maximalAdicModuleCover_flat R, ?_⟩
  intro N _ _ hN
  let : Nontrivial N := hN
  let : Module.FaithfullyFlat R (MaximalAdicModuleCoverCompletion R) :=
    maximalAdicCompletion_faithfullyFlat R
  let : Nontrivial
      (TensorProduct R (MaximalAdicModuleCoverCompletion R) N) :=
    inferInstance
  exact (TensorProduct.prodLeft R R
    (MaximalAdicModuleCoverCompletion R)
    ((i : MaximalAdicModuleCoverGeneratorIndex R) →
      MaximalAdicModuleCoverLocalization R i) N).toEquiv.nontrivial

/-- The extension/restriction adjunction for the single maximal-adic module
cover. -/
abbrev MaximalAdicModuleCoverAdjunction :=
  ModuleCat.extendRestrictScalarsAdj
    (algebraMap R (MaximalAdicModuleCover R))

/-- A genuine faithfully-flat module descent datum on the single
completion/principal product cover. -/
abbrev MaximalAdicModuleCoverDescentDatum :=
  (MaximalAdicModuleCoverAdjunction R).toComonad.Coalgebra

namespace MaximalAdicModuleCoverDescentDatum

variable (D : MaximalAdicModuleCoverDescentDatum R)

local instance : Module R D.A :=
  Module.compHom D.A (algebraMap R (MaximalAdicModuleCover R))

/-- The coalgebra structure map, viewed after restriction to `R`. -/
def left :
    (ModuleCat.restrictScalars
        (algebraMap R (MaximalAdicModuleCover R))).obj D.A ⟶
      (ModuleCat.restrictScalars
        (algebraMap R (MaximalAdicModuleCover R))).obj
        ((ModuleCat.extendScalars
          (algebraMap R (MaximalAdicModuleCover R))).obj
            ((ModuleCat.restrictScalars
              (algebraMap R (MaximalAdicModuleCover R))).obj D.A)) :=
  (ModuleCat.restrictScalars
    (algebraMap R (MaximalAdicModuleCover R))).map D.a

/-- The adjunction unit, viewed as the second map of the descent equalizer. -/
def right :
    (ModuleCat.restrictScalars
        (algebraMap R (MaximalAdicModuleCover R))).obj D.A ⟶
      (ModuleCat.restrictScalars
        (algebraMap R (MaximalAdicModuleCover R))).obj
        ((ModuleCat.extendScalars
          (algebraMap R (MaximalAdicModuleCover R))).obj
            ((ModuleCat.restrictScalars
              (algebraMap R (MaximalAdicModuleCover R))).obj D.A)) :=
  (MaximalAdicModuleCoverAdjunction R).unit.app _

/-- The descended `R`-module, written as the usual degree-zero equalizer. -/
abbrev Sections :=
  LinearMap.eqLocus (D.left (R := R)).hom (D.right (R := R)).hom

/-- The explicit equalizer fork defining `Sections`. -/
def sectionsFork : Fork (D.left (R := R)) (D.right (R := R)) :=
  Fork.ofι (ModuleCat.ofHom D.Sections.subtype) <| by
    ext x
    exact x.2

/-- The explicit `Sections` fork has the universal property of an equalizer. -/
def sectionsForkIsLimit : IsLimit (D.sectionsFork (R := R)) :=
  Fork.IsLimit.mk _
    (fun s ↦ ModuleCat.ofHom <| LinearMap.codRestrict D.Sections s.ι.hom <| by
      intro x
      change (D.left (R := R)).hom (s.ι x) =
        (D.right (R := R)).hom (s.ι x)
      simpa only [ModuleCat.comp_apply] using
        DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp s.condition) x)
    (fun _ ↦ by ext; rfl)
    (fun _ m hm ↦ by
      apply ModuleCat.hom_ext
      ext x
      apply Subtype.ext
      exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hm) x)

/-- The explicit linear equalizer agrees with the categorical equalizer used
by Beck's comparison adjunction. -/
noncomputable def sectionsIsoComparisonEqualizer :
    ModuleCat.of R D.Sections ≅
      Comonad.ComonadicityInternal.comparisonRightAdjointObj
        (MaximalAdicModuleCoverAdjunction R) D :=
  (D.sectionsForkIsLimit (R := R)).conePointUniqueUpToIso
    (limit.isLimit
      (parallelPair (D.left (R := R)) (D.right (R := R))))

/-- Base change of the explicit descended sections to the full product cover
recovers the carrier of the descent datum. -/
noncomputable def coverBaseChangeIso :
    (ModuleCat.extendScalars
      (algebraMap R (MaximalAdicModuleCover R))).obj
        (ModuleCat.of R D.Sections) ≅ D.A := by
  letI : (Comonad.comparison
      (MaximalAdicModuleCoverAdjunction R)).IsEquivalence :=
    (comonadicExtendScalars
      (RingHom.faithfullyFlat_algebraMap_iff.mpr
        (maximalAdicModuleCover_faithfullyFlat R))).eqv
  let counit :=
    (Comonad.ComonadicityInternal.comparisonAdjunction
      (MaximalAdicModuleCoverAdjunction R)).counit.app D
  haveI : IsIso counit := by infer_instance
  exact (ModuleCat.extendScalars
      (algebraMap R (MaximalAdicModuleCover R))).mapIso
        (D.sectionsIsoComparisonEqualizer (R := R)) ≪≫
    (Comonad.forget
      (MaximalAdicModuleCoverAdjunction R).toComonad).mapIso (asIso counit)

/-- The completion chart cut out from the product-cover module. -/
abbrev completionChart :
    ModuleCat (MaximalAdicModuleCoverCompletion R) :=
  (ModuleCat.extendScalars
    (maximalAdicModuleCoverToCompletion R)).obj D.A

/-- A principal chart cut out from the product-cover module. -/
abbrev principalChart (i : MaximalAdicModuleCoverGeneratorIndex R) :
    ModuleCat (MaximalAdicModuleCoverLocalization R i) :=
  (ModuleCat.extendScalars
    (maximalAdicModuleCoverToPrincipal R i)).obj D.A

/-- Base change of descended sections to the completion recovers the
completion chart of the descent datum. -/
noncomputable def completionBaseChangeIso :
    (ModuleCat.extendScalars
      (algebraMap R (MaximalAdicModuleCoverCompletion R))).obj
        (ModuleCat.of R D.Sections) ≅ D.completionChart (R := R) := by
  rw [← maximalAdicModuleCoverToCompletion_comp R]
  exact (ModuleCat.extendScalarsComp
      (algebraMap R (MaximalAdicModuleCover R))
      (maximalAdicModuleCoverToCompletion R)).app
        (ModuleCat.of R D.Sections) ≪≫
    (ModuleCat.extendScalars
      (maximalAdicModuleCoverToCompletion R)).mapIso
        (D.coverBaseChangeIso (R := R))

/-- Base change of descended sections to a principal localization recovers
that principal chart of the descent datum. -/
noncomputable def principalBaseChangeIso
    (i : MaximalAdicModuleCoverGeneratorIndex R) :
    (ModuleCat.extendScalars
      (algebraMap R (MaximalAdicModuleCoverLocalization R i))).obj
        (ModuleCat.of R D.Sections) ≅ D.principalChart (R := R) i := by
  rw [← maximalAdicModuleCoverToPrincipal_comp R i]
  exact (ModuleCat.extendScalarsComp
      (algebraMap R (MaximalAdicModuleCover R))
      (maximalAdicModuleCoverToPrincipal R i)).app
        (ModuleCat.of R D.Sections) ≪≫
    (ModuleCat.extendScalars
      (maximalAdicModuleCoverToPrincipal R i)).mapIso
        (D.coverBaseChangeIso (R := R))

end MaximalAdicModuleCoverDescentDatum

private def eqLocusCongr
    {A B A' B' : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B']
    [Module R A] [Module R B] [Module R A'] [Module R B']
    (l r : A →ₗ[R] B) (l' r' : A' →ₗ[R] B')
    (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B')
    (hl : eB.toLinearMap.comp l = l'.comp eA.toLinearMap)
    (hr : eB.toLinearMap.comp r = r'.comp eA.toLinearMap) :
    LinearMap.eqLocus l r ≃ₗ[R] LinearMap.eqLocus l' r' where
  toFun x := ⟨eA x, by
    have hlx := (LinearMap.ext_iff.mp hl) x.1
    have hrx := (LinearMap.ext_iff.mp hr) x.1
    change eB (l x.1) = l' (eA x.1) at hlx
    change eB (r x.1) = r' (eA x.1) at hrx
    exact hlx.symm.trans ((congrArg eB x.2).trans hrx)⟩
  invFun x := ⟨eA.symm x, by
    apply eB.injective
    have hlx := (LinearMap.ext_iff.mp hl) (eA.symm x.1)
    have hrx := (LinearMap.ext_iff.mp hr) (eA.symm x.1)
    change eB (l (eA.symm x.1)) = l' (eA (eA.symm x.1)) at hlx
    change eB (r (eA.symm x.1)) = r' (eA (eA.symm x.1)) at hrx
    calc
      eB (l (eA.symm x.1)) = l' (eA (eA.symm x.1)) := hlx
      _ = l' x.1 := by rw [eA.apply_symm_apply]
      _ = r' x.1 := x.2
      _ = r' (eA (eA.symm x.1)) := by rw [eA.apply_symm_apply]
      _ = eB (r (eA.symm x.1)) := hrx.symm⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

/-- Evidence that an abstract formal-gluing equalizer is the degree-zero
diagram of a genuine descent coalgebra on the full completion/principal
product cover.

The fields identify source and overlap diagrams and record compatibility of
their two arrows.  In particular, this structure does not assume any
base-change statement about `D.Sections`; those isomorphisms are consequences
below. -/
structure ModuleFormalGluingDatum.FullCoverDescent
    (D : ModuleFormalGluingDatum R
      (MaximalAdicModuleCoverGeneratorIndex R)) where
  /-- The module descent coalgebra on the full product cover. -/
  descent : MaximalAdicModuleCoverDescentDatum R
  /-- Identification of the degree-zero sources of the two diagrams. -/
  sourceEquiv :
    D.Source ≃ₗ[R]
      (ModuleCat.restrictScalars
        (algebraMap R (MaximalAdicModuleCover R))).obj descent.A
  /-- Identification of the overlap targets of the two diagrams. -/
  targetEquiv :
    D.Target ≃ₗ[R]
      (ModuleCat.restrictScalars
        (algebraMap R (MaximalAdicModuleCover R))).obj
          ((ModuleCat.extendScalars
            (algebraMap R (MaximalAdicModuleCover R))).obj
              ((ModuleCat.restrictScalars
                (algebraMap R (MaximalAdicModuleCover R))).obj descent.A))
  /-- The source and target identifications commute with the first diagram map. -/
  left_compatibility :
    targetEquiv.toLinearMap.comp D.left =
      (descent.left (R := R)).hom.comp sourceEquiv.toLinearMap
  /-- The source and target identifications commute with the second diagram map. -/
  right_compatibility :
    targetEquiv.toLinearMap.comp D.right =
      (descent.right (R := R)).hom.comp sourceEquiv.toLinearMap
  /-- The descended completion chart agrees with the specified completion module. -/
  completion_identification :
    (ModuleCat.restrictScalars
      (algebraMap R (MaximalAdicModuleCoverCompletion R))).obj
        (descent.completionChart (R := R)) ≅ D.completion
  /-- Each descended principal chart agrees with the specified principal module. -/
  principal_identification :
    (i : MaximalAdicModuleCoverGeneratorIndex R) →
      (ModuleCat.restrictScalars
        (algebraMap R (MaximalAdicModuleCoverLocalization R i))).obj
          (descent.principalChart (R := R) i) ≅ D.principal i

namespace ModuleFormalGluingDatum.FullCoverDescent

variable {D : ModuleFormalGluingDatum R
  (MaximalAdicModuleCoverGeneratorIndex R)}

/-- Diagram compatibility identifies formal-gluing sections with the
explicit equalizer of the full cover descent coalgebra. -/
noncomputable def sectionsEquiv (V : D.FullCoverDescent (R := R)) :
    D.Sections ≃ₗ[R] V.descent.Sections :=
  eqLocusCongr (R := R) D.left D.right
    (V.descent.left (R := R)).hom (V.descent.right (R := R)).hom
    V.sourceEquiv V.targetEquiv
    V.left_compatibility V.right_compatibility

/-- Base change of the formal-gluing `Sections` to the full product cover
recovers the full cover module. -/
noncomputable def coverBaseChangeIso (V : D.FullCoverDescent (R := R)) :
    (ModuleCat.extendScalars
      (algebraMap R (MaximalAdicModuleCover R))).obj
        (ModuleCat.of R D.Sections) ≅ V.descent.A :=
  (ModuleCat.extendScalars
    (algebraMap R (MaximalAdicModuleCover R))).mapIso
      (LinearEquiv.toModuleIso V.sectionsEquiv) ≪≫
    V.descent.coverBaseChangeIso (R := R)

/-- Base change of the formal-gluing `Sections` recovers the typed completion
chart associated to the full descent datum. -/
noncomputable def completionBaseChangeIso
    (V : D.FullCoverDescent (R := R)) :
    (ModuleCat.extendScalars
      (algebraMap R (MaximalAdicModuleCoverCompletion R))).obj
        (ModuleCat.of R D.Sections) ≅
      V.descent.completionChart (R := R) := by
  rw [← maximalAdicModuleCoverToCompletion_comp R]
  exact (ModuleCat.extendScalarsComp
      (algebraMap R (MaximalAdicModuleCover R))
      (maximalAdicModuleCoverToCompletion R)).app
        (ModuleCat.of R D.Sections) ≪≫
    (ModuleCat.extendScalars
      (maximalAdicModuleCoverToCompletion R)).mapIso
        (V.coverBaseChangeIso (R := R))

/-- Base change of the formal-gluing `Sections` recovers each typed principal
chart associated to the full descent datum. -/
noncomputable def principalBaseChangeIso
    (V : D.FullCoverDescent (R := R))
    (i : MaximalAdicModuleCoverGeneratorIndex R) :
    (ModuleCat.extendScalars
      (algebraMap R (MaximalAdicModuleCoverLocalization R i))).obj
        (ModuleCat.of R D.Sections) ≅
      V.descent.principalChart (R := R) i := by
  rw [← maximalAdicModuleCoverToPrincipal_comp R i]
  exact (ModuleCat.extendScalarsComp
      (algebraMap R (MaximalAdicModuleCover R))
      (maximalAdicModuleCoverToPrincipal R i)).app
        (ModuleCat.of R D.Sections) ≪≫
    (ModuleCat.extendScalars
      (maximalAdicModuleCoverToPrincipal R i)).mapIso
        (V.coverBaseChangeIso (R := R))

end ModuleFormalGluingDatum.FullCoverDescent

end Noetherian

end EtaleFundamentalGroups

end
