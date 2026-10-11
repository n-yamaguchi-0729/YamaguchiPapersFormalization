/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NativeResidueRingAction
import Nyll.EtaleFundamentalGroups.Inertia.NativeAbsoluteResidueFields
import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationResidueCoefficient

/-!
# The actual original decomposition action on residue coefficients

The quotient automorphism is the SAME original normalization residue morphism.
Its localization presentation retains the already proved coefficient equation.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier)

/-- The original decomposition group acts by its literal quotient automorphism. -/
def actualNormalizationQuotientAction :
    (normalizationDecompositionGroup A K L Q).carrier →*
      (((normalizationCommAlgCat A L).carrier ⧸ Q) ≃+*
        ((normalizationCommAlgCat A L).carrier ⧸ Q)) :=
  (nativeAlgebraResidueRingEquivHom (normalizationCommAlgCat A L) Q).comp
    (normalizationResidueMorphism A K L Q).hom'

/-- Evaluate the SAME literal quotient action on a coefficient. Its ring
 automorphism group remains inside this original action owner. -/
def actualNormalizationQuotientActionScalar [Q.IsMaximal]
    (d : (normalizationDecompositionGroup A K L Q).carrier)
    (z : (normalizationResidueFieldObject A L Q).α) :
    (normalizationResidueFieldObject A L Q).α :=
  ((actualNormalizationQuotientAction A K L Q).toFun d).toRingHom.toFun z

/-- The stored scalar evaluation is exactly the existing quotient action,
with no alternative action or coefficient identification. -/
theorem actualNormalizationQuotientActionScalar_apply [Q.IsMaximal]
    (d : (normalizationDecompositionGroup A K L Q).carrier)
    (z : (normalizationResidueFieldObject A L Q).α) :
    actualNormalizationQuotientActionScalar A K L Q d z =
      ((actualNormalizationQuotientAction A K L Q).toFun d).toRingHom.toFun z := rfl

/-- The original quotient action evaluates the original residue morphism
on the same stored coefficient, before any separable-field comparison. -/
theorem actualNormalizationQuotientActionScalar_eq_residueAction [Q.IsMaximal]
    (d : (normalizationDecompositionGroup A K L Q).carrier)
    (z : (normalizationResidueFieldObject A L Q).α) :
    actualNormalizationQuotientActionScalar A K L Q d z =
      normalizationResidueActionScalar A L Q
        ((normalizationResidueMorphism A K L Q).hom'.toFun d) z := rfl

/-- The SAME action transported to the fixed localization residue field. -/
def actualNormalizationResidueFieldMap [Q.IsMaximal]
    (d : (normalizationDecompositionGroup A K L Q).carrier) :
    Q.ResidueField →+* Q.ResidueField :=
  nativeAlgebraResidueRingHom (normalizationCommAlgCat A L) Q
    ((normalizationResidueMorphism A K L Q).hom'.toFun d)

theorem actualNormalizationResidueFieldMap_coefficient [Q.IsMaximal]
    (d : (normalizationDecompositionGroup A K L Q).carrier)
    (b : (normalizationCommAlgCat A L).carrier) :
    (actualNormalizationResidueFieldMap A K L Q d).toFun
        ((algebraMap (normalizationCommAlgCat A L).carrier Q.ResidueField).toFun b) =
      (algebraMap (normalizationCommAlgCat A L).carrier Q.ResidueField).toFun
        ((normalizationGaloisRingHom A K L d.val).toFun b) :=
  nativeAlgebraResidueRingHom_coefficient (normalizationCommAlgCat A L) Q
    ((normalizationResidueMorphism A K L Q).hom'.toFun d)
    (normalizationGaloisRingHom A K L d.val)
    (originalNormalizationResidueMorphism_coefficientMap A K L Q d) b

end EtaleFundamentalGroups.Inertia

end
