/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NativeAbsoluteResidueFields
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Invariant.Galois

/-!
# Normality of the actual normalization residue extension

Each element of the original normalization residue is represented by an
integral element lying in a finite Galois intermediate field. At that finite
stage the actual residue extension is normal by the finite invariant-action
theorem. Its splitting polynomial transports through the actual quotient
coefficient map. This proves normality for the possibly infinite original
Galois extension, including the zero-prime and base-field cases.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] Ideal.Quotient.field

private theorem finiteNormalizationQuotient_normal
    (A : Type u) (K : Type v) (E : Type w)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field E]
    [Algebra A K] [IsFractionRing A K] [Algebra K E] [Algebra A E]
    [IsScalarTower A K E] [FiniteDimensional K E] [IsGalois K E]
    (P : Ideal A) [P.IsMaximal]
    (q : Ideal (integralClosure A E)) [q.IsMaximal] [q.LiesOver P] :
    Normal (A ⧸ P) ((integralClosure A E) ⧸ q) := by
  have : IsFractionRing (integralClosure A E) E :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K E
  let : MulSemiringAction Gal(E/K) (integralClosure A E) :=
    IsIntegralClosure.MulSemiringAction A K E (integralClosure A E)
  have : Algebra.IsInvariant A (integralClosure A E) Gal(E/K) :=
    Algebra.isInvariant_of_isGalois A K E (integralClosure A E)
  exact Ideal.Quotient.normal Gal(E/K) P q

/-- The literal normalization residue field is normal over the original
local residue field for any original Galois extension. No algebraic-closure
or nonzero-prime premise is required. -/
theorem normalizationResidueFieldAlgebra_isNormal
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [hQmax : Q.IsMaximal] :
    let : Algebra (IsLocalRing.ResidueField A) (normalizationResidueFieldObject A L Q).α :=
      normalizationResidueFieldAlgebra A L Q
    Normal (IsLocalRing.ResidueField A) (normalizationResidueFieldObject A L Q).α := by
  intro actualResidueAlgebra
  let Q₀ : Ideal (integralClosure A L) := Q
  have : Q₀.IsMaximal := hQmax
  have hQ : Q₀.under A = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) Q₀)
  have : Q₀.LiesOver (IsLocalRing.maximalIdeal A) := ⟨hQ.symm⟩
  refine
    { toIsAlgebraic := normalizationResidueFieldAlgebra_isAlgebraic A L Q
      splits' := ?_ }
  intro x
  obtain ⟨b, hbValue⟩ := Ideal.Quotient.mk_surjective (I := Q₀) x
  let E := FiniteGaloisIntermediateField.adjoin K ({b.val} : Set L)
  have hb : b.val ∈ E.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin K ({b.val} : Set L) (by rfl)
  have : IsScalarTower A E L := IsScalarTower.of_algebraMap_eq' rfl
  let c₀ : E := ⟨b.val, hb⟩
  have hc₀ : IsIntegral A c₀ :=
    (isIntegral_algebraMap_iff (R := A) (A := E) (B := L)).mp b.property
  let c : integralClosure A E := ⟨c₀, hc₀⟩
  let ι : integralClosure A E →ₐ[A] integralClosure A L :=
    (IsScalarTower.toAlgHom A E L).mapIntegralClosure
  let q : Ideal (integralClosure A E) := Q₀.comap ι.toRingHom
  have : q.IsPrime := Ideal.IsPrime.comap ι.toRingHom
  have hq_under : q.under A = Q₀.under A := by
    apply Ideal.ext
    intro a
    change (ι (algebraMap A (integralClosure A E) a) ∈ Q₀) ↔
      algebraMap A (integralClosure A L) a ∈ Q₀
    rw [ι.commutes a]
  have hq : q.under A = IsLocalRing.maximalIdeal A := hq_under.trans hQ
  have : q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under q
    (hq.symm ▸ (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal))
  have : q.LiesOver (IsLocalRing.maximalIdeal A) := ⟨hq.symm⟩
  let : Algebra (IsLocalRing.ResidueField A) ((integralClosure A E) ⧸ q) :=
    Ideal.Quotient.algebraOfLiesOver q (IsLocalRing.maximalIdeal A)
  have : Normal (IsLocalRing.ResidueField A) ((integralClosure A E) ⧸ q) :=
    finiteNormalizationQuotient_normal A K E (IsLocalRing.maximalIdeal A) q
  let ρ : ((integralClosure A E) ⧸ q) →ₐ[A] ((integralClosure A L) ⧸ Q₀) :=
    Ideal.quotientMapₐ Q₀ ι (le_refl q)
  let ρκ : ((integralClosure A E) ⧸ q) →ₐ[IsLocalRing.ResidueField A]
      (normalizationResidueFieldObject A L Q).α :=
    { ρ.toRingHom with
      commutes' := fun a => by
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) a
        change ρ (algebraMap A ((integralClosure A E) ⧸ q) a) =
          algebraMap A ((integralClosure A L) ⧸ Q₀) a
        exact ρ.commutes a }
  let y : (integralClosure A E) ⧸ q := Ideal.Quotient.mk q c
  have hρ : ρκ y = x := by
    have hc : ι c = b := by
      apply Subtype.ext
      rfl
    exact (congrArg (Ideal.Quotient.mk Q₀) hc).trans hbValue
  have hρinjective : Function.Injective ρκ :=
    Ideal.quotientMap_injective (I := Q₀) (f := ι.toRingHom)
  have hpoly : minpoly (IsLocalRing.ResidueField A) x =
      minpoly (IsLocalRing.ResidueField A) y :=
    (congrArg (fun z : (normalizationResidueFieldObject A L Q).α =>
      minpoly (IsLocalRing.ResidueField A) z) hρ.symm).trans
        (minpoly.algHom_eq ρκ hρinjective y)
  rw [hpoly]
  have hcomp : ρκ.toRingHom.comp
      (algebraMap (IsLocalRing.ResidueField A) ((integralClosure A E) ⧸ q)) =
        algebraMap (IsLocalRing.ResidueField A) (normalizationResidueFieldObject A L Q).α :=
    RingHom.ext (fun a => ρκ.commutes a)
  have hsplit : (((minpoly (IsLocalRing.ResidueField A) y).map
      (algebraMap (IsLocalRing.ResidueField A) ((integralClosure A E) ⧸ q))).map
        ρκ.toRingHom).Splits :=
    ((inferInstance : Normal (IsLocalRing.ResidueField A)
      ((integralClosure A E) ⧸ q)).splits y).map ρκ.toRingHom
  have hmap : ((minpoly (IsLocalRing.ResidueField A) y).map
      (algebraMap (IsLocalRing.ResidueField A) ((integralClosure A E) ⧸ q))).map
        ρκ.toRingHom =
      (minpoly (IsLocalRing.ResidueField A) y).map
        (algebraMap (IsLocalRing.ResidueField A) (normalizationResidueFieldObject A L Q).α) := by
    rw [Polynomial.map_map]
    exact congrArg (fun f : IsLocalRing.ResidueField A →+*
      (normalizationResidueFieldObject A L Q).α =>
        (minpoly (IsLocalRing.ResidueField A) y).map f) hcomp
  exact hmap ▸ hsplit

end EtaleFundamentalGroups.Inertia
