/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualNormalizationResidueExactness
import EtaleFundamentalGroups.Inertia.NativeSeparableResidueGroup
import EtaleFundamentalGroups.Inertia.NormalizationAbsoluteResidueGroup
import EtaleFundamentalGroups.Inertia.NormalizationResidueNormal
import EtaleFundamentalGroups.Inertia.SeparableClosureAutomorphisms
import SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence

/-!
# Original decomposition and inertia over the separable residue field

Normality of the actual normalization residue extension gives the existing
restriction equivalence with its relative separable closure. Composing this
actual equivalence with the original residue action preserves its surjectivity
and its literal kernel, the original inertia included in decomposition.
No discrete valuation or algebraically closed residue hypothesis is used.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open CategoryTheory SchemeTheory

universe u v w

attribute [local instance] normalizationCommAlgGaloisAction

private def separableResidueIsoOfNormal (k : Type u) [Field k] (E : Bundled Field.{w})
    (a : Algebra k E.α) (h : let := a; Normal k E.α) :
    nativeFieldAutomorphisms k E a ≅ nativeSeparableResidueGroup k E a := by
  let := a
  have : Normal k E.α := h
  exact (separableClosureAutEquiv k E.α).toGrpIso

private theorem separableResidueIsoOfNormal_commutes
    (k : Type u) [Field k] (E : Bundled Field.{w}) (a : Algebra k E.α)
    (h : let := a; Normal k E.α)
    (σ : (nativeFieldAutomorphisms k E a).carrier)
    (z : (nativeSeparableResidueField k E a).α) :
    nativeSeparableResidueActionScalar k E a
        ((separableResidueIsoOfNormal k E a h).hom.hom'.toFun σ) z =
      nativeFieldResidueActionScalar k E a σ (nativeSeparableResidueScalar k E a z) := by
  let := a
  have : Normal k E.α := h
  exact separableClosure_restrictNormal_coefficient k E.α (show E.α ≃ₐ[k] E.α from σ) z

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- Restriction identifies the original literal residue automorphism group
with the Galois group of its actual separable part. The required normality
is proved from the original normalization data. -/
def normalizationSeparableResidueIso :
    normalizationResidueAutomorphisms A L Q ≅ normalizationResidueSeparableGroup A L Q :=
  eqToIso (normalizationResidueAutomorphisms_eq_fieldObject A L Q) ≪≫
    separableResidueIsoOfNormal (IsLocalRing.ResidueField A) (normalizationResidueFieldObject A L Q)
      (normalizationResidueFieldAlgebra A L Q) (normalizationResidueFieldAlgebra_isNormal A K L Q)

/-- The residue restriction equivalence preserves the literal coefficient
inclusion into the original normalization quotient. -/
theorem normalizationSeparableResidueIso_commutes
    (σ : (normalizationResidueAutomorphisms A L Q).carrier)
    (z : (nativeSeparableResidueField (IsLocalRing.ResidueField A)
      (normalizationResidueFieldObject A L Q) (normalizationResidueFieldAlgebra A L Q)).α) :
    nativeSeparableResidueActionScalar (IsLocalRing.ResidueField A)
        (normalizationResidueFieldObject A L Q) (normalizationResidueFieldAlgebra A L Q)
        ((normalizationSeparableResidueIso A K L Q).hom.hom'.toFun σ) z =
      normalizationResidueActionScalar A L Q σ
        (nativeSeparableResidueScalar (IsLocalRing.ResidueField A)
          (normalizationResidueFieldObject A L Q) (normalizationResidueFieldAlgebra A L Q) z) := by
  exact (separableResidueIsoOfNormal_commutes (IsLocalRing.ResidueField A)
    (normalizationResidueFieldObject A L Q) (normalizationResidueFieldAlgebra A L Q)
    (normalizationResidueFieldAlgebra_isNormal A K L Q)
    ((eqToIso (normalizationResidueAutomorphisms_eq_fieldObject A L Q)).hom.hom'.toFun σ) z).trans
      (normalizationResidueAutomorphisms_fieldObject_apply A L Q σ
        (nativeSeparableResidueScalar (IsLocalRing.ResidueField A)
          (normalizationResidueFieldObject A L Q) (normalizationResidueFieldAlgebra A L Q) z))

/-- The original decomposition action restricted to the actual separable
residue field. -/
def normalizationSeparableResidueMorphism :
    GrpCat.Hom (normalizationDecompositionGroup A K L Q)
      (normalizationResidueSeparableGroup A L Q) :=
  normalizationResidueMorphism A K L Q ≫ (normalizationSeparableResidueIso A K L Q).hom

/-- Every automorphism of the actual separable residue field is induced by
an element of the original decomposition subgroup. -/
theorem normalizationSeparableResidueMorphism_surjective :
    Function.Surjective (normalizationSeparableResidueMorphism A K L Q).hom'.toFun :=
  nativeGroupMorphism_comp_iso_surjective (normalizationResidueMorphism A K L Q)
    (normalizationSeparableResidueIso A K L Q) (normalizationResidueMorphism_surjective A K L Q)

/-- The actual separable-residue map has the same literal kernel in D as
the original full residue action. -/
theorem normalizationSeparableResidueMorphism_ker :
    (normalizationSeparableResidueMorphism A K L Q).hom'.ker =
      (actualNormalizationInertiaToDecomposition A K L Q).range :=
  (nativeGroupMorphism_comp_iso_ker (normalizationResidueMorphism A K L Q)
    (normalizationSeparableResidueIso A K L Q)).trans
      (actualNormalizationResidueMorphism_ker A K L Q)

/-- The exact original I-to-D-to-separable-residue sequence over an arbitrary
normal local domain, with the same original inclusion and residue action. -/
theorem normalizationSeparableResidue_exact :
    Function.Injective (actualNormalizationInertiaToDecomposition A K L Q).toFun ∧
      Function.Surjective (normalizationSeparableResidueMorphism A K L Q).hom'.toFun ∧
        (normalizationSeparableResidueMorphism A K L Q).hom'.ker =
          (actualNormalizationInertiaToDecomposition A K L Q).range :=
  ⟨actualNormalizationInertiaToDecomposition_injective A K L Q,
    normalizationSeparableResidueMorphism_surjective A K L Q,
    normalizationSeparableResidueMorphism_ker A K L Q⟩

end EtaleFundamentalGroups.Inertia
