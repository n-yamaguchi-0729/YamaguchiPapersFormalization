/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Tower
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Original displayed fraction fields and the canonical same-universe field

The native map from FractionRing A to the displayed original fraction field
K is the actual fraction-field equivalence. Its surjectivity makes scalar
extension on the original ambient automorphisms an equivalence, leaving
every underlying automorphism unchanged. This permits using common-universe
scheme APIs without changing the independently supplied original K.
-/

noncomputable section

namespace EtaleFundamentalGroups.StrictHenselian

universe u v w

/-- The native fraction-field coefficient map is the original canonical
fraction-field equivalence, as witnessed on every coefficient of A. -/
theorem fractionFieldBaseMap_eq_algEquiv
    (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] :
    let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
    algebraMap (FractionRing A) K = (FractionRing.algEquiv A K).toRingHom := by
  intro actualAlgebra
  have : IsScalarTower A (FractionRing A) K := inferInstance
  apply IsFractionRing.ringHom_ext (A := A)
  intro a
  exact (IsScalarTower.algebraMap_apply A (FractionRing A) K a).symm.trans
    ((FractionRing.algEquiv A K).commutes a).symm

/-- The actual canonical-to-displayed fraction-field map is surjective. -/
theorem fractionFieldBaseMap_surjective
    (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] :
    let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
    Function.Surjective (algebraMap (FractionRing A) K) := by
  intro actualAlgebra
  rw [fractionFieldBaseMap_eq_algEquiv A K]
  exact (FractionRing.algEquiv A K).surjective

variable (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra A L] [FaithfulSMul A L]
    [Algebra K L] [IsScalarTower A K L]

/-- The original ambient automorphisms over the canonical fraction field
and over the displayed original K are the same actual automorphisms. -/
def originalFractionFieldGaloisEquiv :
    let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
    let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    Gal(L/FractionRing A) ≃* Gal(L/K) := by
  intro actualFractionAlgebra actualAmbientAlgebra
  have : IsScalarTower (FractionRing A) K L := inferInstance
  exact AlgEquiv.extendScalarsHomOfSurjective (fractionFieldBaseMap_surjective A K)

/-- The fraction-field scalar comparison retains the literal ambient RingHom. -/
theorem originalFractionFieldGaloisEquiv_toRingHom :
    let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
    let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    ∀ σ : Gal(L/FractionRing A),
      (originalFractionFieldGaloisEquiv A K L σ).toRingHom = σ.toRingHom := by
  intro actualFractionAlgebra actualAmbientAlgebra σ
  rfl

/-- The original separable closure is also a separable closure of the
canonical fraction field, through its native original A-coefficient action. -/
theorem originalFractionField_isSepClosure [IsGalois K L] [IsSepClosed L] :
    let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
    let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    IsSepClosure (FractionRing A) L := by
  intro actualFractionAlgebra actualAmbientAlgebra
  have : IsScalarTower (FractionRing A) K L := inferInstance
  let e : FractionRing A ≃+* K := (FractionRing.algEquiv A K).toRingEquiv
  have he : algebraMap (FractionRing A) K = e.toRingHom :=
    fractionFieldBaseMap_eq_algEquiv A K
  have hcomp : (algebraMap (FractionRing A) L).comp e.symm.toRingHom =
      (RingHom.id L).comp (algebraMap K L) := by
    rw [IsScalarTower.algebraMap_eq (FractionRing A) K L, he, RingHom.comp_assoc,
      RingEquiv.toRingHom_comp_symm_toRingHom, RingHom.comp_id, RingHom.id_comp]
  exact ⟨inferInstance,
    Algebra.IsSeparable.of_equiv_equiv e.symm (RingEquiv.refl L) hcomp⟩

end EtaleFundamentalGroups.StrictHenselian
