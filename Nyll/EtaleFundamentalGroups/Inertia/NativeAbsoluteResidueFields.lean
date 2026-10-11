/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationResidueDVR
import Nyll.SchemeTheory.RingTheory.Ramification.NativeAlgebraResidueCoefficient
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Native quotient residue fields and coefficient actions

Constructs bundled maximal quotient fields and their residue coefficient actions for integral
algebras. Proves algebraicity of these actions and specializes them to normalization residue
fields.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open CategoryTheory SchemeTheory

universe u v w

/-- A bundled field retains its own stored field structure. -/
instance bundledResidueField (F : Bundled Field.{u}) : Field F.α := F.str

/-- A literal maximal quotient, with the canonical maximal-ideal field structure. -/
def maximalQuotientFieldObject (B : CommRingCat.{v}) (Q : Ideal B.carrier) [Q.IsMaximal] :
    Bundled Field.{v} := ⟨B.carrier ⧸ Q, Ideal.Quotient.field Q⟩

/-- The actual quotient coefficient action over the local residue field.
Integrality proves that the chosen maximal prime contracts to the closed point. -/
@[instance_reducible]
def integralResidueFieldAlgebra
    (A : Type u) [CommRing A] [IsLocalRing A] (B : CommAlgCat.{v} A)
    [Algebra.IsIntegral A B.carrier] (Q : Ideal B.carrier) [Q.IsMaximal] :
    Algebra (IsLocalRing.ResidueField A)
      (maximalQuotientFieldObject (CommRingCat.of B.carrier) Q).α := by
  have hmax : (Q.under A).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q
  have hover : Q.LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal hmax).symm⟩
  exact inferInstanceAs (Algebra (A ⧸ IsLocalRing.maximalIdeal A) (B.carrier ⧸ Q))

/-- Integrality descends through the literal quotient before either
residue field or its coefficient action is introduced. -/
private theorem quotient_isIntegral
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [Algebra.IsIntegral A B] (Q : Ideal B) : Algebra.IsIntegral A (B ⧸ Q) :=
  Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ A Q) Ideal.Quotient.mk_surjective

/-- The computed residue coefficient action is algebraic, by descending
the original integral extension to its actual quotients. -/
theorem integralResidueFieldAlgebra_isAlgebraic
    (A : Type u) [CommRing A] [IsLocalRing A] (B : CommAlgCat.{v} A)
    [Algebra.IsIntegral A B] (Q : Ideal B) [Q.IsMaximal] :
    letI := integralResidueFieldAlgebra A B Q
    Algebra.IsAlgebraic (IsLocalRing.ResidueField A)
      (maximalQuotientFieldObject (CommRingCat.of B) Q) := by
  have hmax : (Q.under A).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q
  have hover : Q.LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal hmax).symm⟩
  have hint : Algebra.IsIntegral A (B ⧸ Q) := quotient_isIntegral A B Q
  have hres : Algebra.IsIntegral (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ Q) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := A) x).tower_top⟩
  change Algebra.IsAlgebraic (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ Q)
  infer_instance

/-- The literal quotient of the actual normalization as a native field object. -/
def normalizationResidueFieldObject
    (A : Type u) (Ω : Type w) [CommRing A] [CommRing Ω] [Algebra A Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal] : Bundled Field.{w} :=
  maximalQuotientFieldObject (CommRingCat.of (normalizationCommAlgCat A Ω)) Q

/-- The actual native residue automorphism evaluated on the stored literal
field carrier. Its quotient interface stays inside this field owner. -/
def normalizationResidueActionScalar
    (A : Type u) (Ω : Type w) [CommRing A] [CommRing Ω] [Algebra A Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]
    (σ : (normalizationResidueAutomorphisms A Ω Q).carrier)
    (z : (normalizationResidueFieldObject A Ω Q).α) :
    (normalizationResidueFieldObject A Ω Q).α :=
  (nativeAlgebraResidueAutomorphismRingEquiv (normalizationCommAlgCat A Ω) Q σ
    ).toRingHom.toFun z

/-- The stored coefficient evaluation is the SAME underlying native quotient
ring automorphism at every literal field element. -/
theorem normalizationResidueActionScalar_apply
    (A : Type u) (Ω : Type w) [CommRing A] [CommRing Ω] [Algebra A Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]
    (σ : (normalizationResidueAutomorphisms A Ω Q).carrier)
    (z : (normalizationResidueFieldObject A Ω Q).α) :
    normalizationResidueActionScalar A Ω Q σ z =
      (nativeAlgebraResidueAutomorphismRingEquiv (normalizationCommAlgCat A Ω) Q σ
        ).toRingHom.toFun z := rfl

/-- The actual coefficient field action on the literal normalization residue. -/
@[instance_reducible]
def normalizationResidueFieldAlgebra
    (A : Type u) (Ω : Type w) [CommRing A] [IsLocalRing A]
    [CommRing Ω] [Algebra A Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal] :
    Algebra (IsLocalRing.ResidueField A) (normalizationResidueFieldObject A Ω Q) := by
  have : Algebra.IsIntegral A (normalizationCommAlgCat A Ω) :=
    inferInstanceAs (Algebra.IsIntegral A (integralClosure A Ω))
  exact integralResidueFieldAlgebra A (normalizationCommAlgCat A Ω) Q

/-- The two literal normalization residue fields form an algebraic extension. -/
theorem normalizationResidueFieldAlgebra_isAlgebraic
    (A : Type u) (Ω : Type w) [CommRing A] [IsLocalRing A]
    [CommRing Ω] [Algebra A Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal] :
    letI := normalizationResidueFieldAlgebra A Ω Q
    Algebra.IsAlgebraic (IsLocalRing.ResidueField A) (normalizationResidueFieldObject A Ω Q) := by
  have : Algebra.IsIntegral A (normalizationCommAlgCat A Ω) :=
    inferInstanceAs (Algebra.IsIntegral A (integralClosure A Ω))
  exact integralResidueFieldAlgebra_isAlgebraic A (normalizationCommAlgCat A Ω) Q

end EtaleFundamentalGroups.Inertia

end
