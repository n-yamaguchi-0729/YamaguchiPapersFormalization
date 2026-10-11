/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.AffineUnramifiedSubfield
import Nyll.EtaleFundamentalGroups.StrictHenselian.OriginalFractionFieldGaloisTopology
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The maximal unramified field inside the original separable closure

The original fraction field may have an independent universe. Scalar
restriction to the canonical fraction field retains the literal finite
subfields and their integral closures. The actual automorphism comparison
then identifies the kernel with the fixing condition over the original K.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale
open scoped nonZeroDivisors

namespace EtaleFundamentalGroups.StrictHenselian

universe u v

private local instance fieldSpecQuasiCompact
    {F : Type u} [Field F] {S : Scheme.{u}} (f : Spec (.of F) ⟶ S) :
    QuasiCompact f where
  isCompact_preimage U _ _ := (Set.toFinite (f ⁻¹' U)).isCompact

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [FaithfulSMul A L] [IsGalois K L] [IsSepClosed L]

/-- The actual fraction-point map from the original Galois group. -/
def originalFractionAbsoluteGaloisHom :
    let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
    let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    let : IsSepClosure (FractionRing A) L := originalFractionField_isSepClosure A K L
    Gal(L/K) →ₜ* π₁ᵉᵗ(ξ (FractionRing A) L ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) := by
  intro actualFractionAlgebra actualAmbientAlgebra actualSepClosure
  let e := originalFractionFieldGaloisEquiv A K L
  let ei : Gal(L/K) →ₜ* Gal(L/FractionRing A) :=
    { toMonoidHom := e.symm.toMonoidHom
      continuous_toFun := Continuous.continuous_symm_of_equiv_compact_to_t2
        (f := e.toEquiv) (originalFractionFieldGaloisEquiv_continuous A K L) }
  exact (fieldSourceAbsoluteGaloisHom (FractionRing A) L
    (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))))).comp ei

/-- Surjectivity is supplied by the native localization generic point. -/
theorem originalFractionAbsoluteGaloisHom_surjective :
    let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
    let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    let : IsSepClosure (FractionRing A) L := originalFractionField_isSepClosure A K L
    Function.Surjective (originalFractionAbsoluteGaloisHom A K L) := by
  intro actualFractionAlgebra actualAmbientAlgebra actualSepClosure
  let j := Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))
  have : IsPreimmersion j := IsPreimmersion.of_isLocalization A⁰
  have : IsDominant j := by
    rw [isDominant_iff]
    change DenseRange (PrimeSpectrum.comap (algebraMap A (FractionRing A)))
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective A (FractionRing A))]
    exact bot_le
  exact (fieldSourceAbsoluteGaloisHom_surjective (FractionRing A) L j).comp
    (originalFractionFieldGaloisEquiv A K L).symm.surjective

/-- The finite normalization criterion for literal subfields of L over the
original fraction field K, retaining its independent universe. -/
theorem integralClosure_unramified_iff_originalKernel_le_fixingSubgroup
    (E : IntermediateField K L) [FiniteDimensional K E] :
    let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
    let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    let : IsSepClosure (FractionRing A) L := originalFractionField_isSepClosure A K L
    (Algebra.FormallyUnramified A (integralClosure A E) ∧
      Algebra.FiniteType A (integralClosure A E)) ↔
      (originalFractionAbsoluteGaloisHom A K L).toMonoidHom.ker ≤ E.fixingSubgroup := by
  intro actualFractionAlgebra actualAmbientAlgebra actualSepClosure
  have : IsScalarTower (FractionRing A) K L := inferInstance
  have : FiniteDimensional (FractionRing A) K :=
    Module.Finite.of_surjective (Algebra.linearMap (FractionRing A) K)
      (fractionFieldBaseMap_surjective A K)
  have : FiniteDimensional (FractionRing A) (E.restrictScalars (FractionRing A)) :=
    Module.Finite.trans (R := FractionRing A) K E
  let q := fieldSourceAbsoluteGaloisHom (FractionRing A) L
    (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))))
  let e := originalFractionFieldGaloisEquiv A K L
  have hfinite := integralClosure_unramified_iff_fieldSourceKernel_le_fixingSubgroup
    A (FractionRing A) L (E.restrictScalars (FractionRing A))
  refine hfinite.trans ?_
  constructor
  · intro h σ hσ
    apply (IntermediateField.mem_fixingSubgroup_iff E σ).mpr
    intro x hx
    have hs : e.symm σ ∈ q.toMonoidHom.ker := hσ
    have hfix := (IntermediateField.mem_fixingSubgroup_iff
      (E.restrictScalars (FractionRing A)) (e.symm σ)).mp (h hs) x hx
    have he : (e (e.symm σ)) x = (e.symm σ) x :=
      DFunLike.congr_fun (originalFractionFieldGaloisEquiv_toRingHom A K L (e.symm σ)) x
    rw [e.apply_symm_apply] at he
    exact he.trans hfix
  · intro h σ hσ
    apply (IntermediateField.mem_fixingSubgroup_iff
      (E.restrictScalars (FractionRing A)) σ).mpr
    intro x hx
    have hs : e σ ∈ (originalFractionAbsoluteGaloisHom A K L).toMonoidHom.ker := by
      change q (e.symm (e σ)) = 1
      rw [e.symm_apply_apply]
      exact hσ
    have hfix := (IntermediateField.mem_fixingSubgroup_iff E (e σ)).mp (h hs) x hx
    have he : (e σ) x = σ x :=
      DFunLike.congr_fun (originalFractionFieldGaloisEquiv_toRingHom A K L σ) x
    exact he.symm.trans hfix

/-- Membership in the original kernel fixed field is membership in an
actual finite unramified subextension of the original L/K. -/
theorem mem_originalKernelFixedField_iff_exists_unramified_finite_subfield
    (x : L) :
    let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
    let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    let : IsSepClosure (FractionRing A) L := originalFractionField_isSepClosure A K L
    x ∈ IntermediateField.fixedField
      (originalFractionAbsoluteGaloisHom A K L).toMonoidHom.ker ↔
      ∃ E : IntermediateField K L, FiniteDimensional K E ∧
        (Algebra.FormallyUnramified A (integralClosure A E) ∧
          Algebra.FiniteType A (integralClosure A E)) ∧ x ∈ E := by
  intro actualFractionAlgebra actualAmbientAlgebra actualSepClosure
  constructor
  · intro hx
    let E := IntermediateField.adjoin K ({x} : Set L)
    let : FiniteDimensional K E :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    have hE : E ≤ IntermediateField.fixedField
        (originalFractionAbsoluteGaloisHom A K L).toMonoidHom.ker :=
      IntermediateField.adjoin_simple_le_iff.mpr hx
    have hfix := (IntermediateField.le_iff_le _ E).mp hE
    exact ⟨E, inferInstance,
      (integralClosure_unramified_iff_originalKernel_le_fixingSubgroup A K L E).mpr hfix,
      IntermediateField.subset_adjoin K {x} (Set.mem_singleton x)⟩
  · rintro ⟨E, hfinite, hunram, hx⟩
    let : FiniteDimensional K E := hfinite
    have hfix :=
      (integralClosure_unramified_iff_originalKernel_le_fixingSubgroup A K L E).mp hunram
    exact ((IntermediateField.le_iff_le _ E).mpr hfix) hx

/-- The independently defined original maximal unramified field is the
fixed field of the actual fraction-point fundamental-group kernel. -/
theorem maximalUnramifiedSubfield_eq_originalKernelFixedField :
    let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
    let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    let : IsSepClosure (FractionRing A) L := originalFractionField_isSepClosure A K L
    maximalUnramifiedSubfield A K L = IntermediateField.fixedField
      (originalFractionAbsoluteGaloisHom A K L).toMonoidHom.ker := by
  intro actualFractionAlgebra actualAmbientAlgebra actualSepClosure
  apply le_antisymm
  · apply iSup_le
    intro E
    apply iSup_le
    intro hfinite
    apply iSup_le
    intro hunram x hx
    exact (mem_originalKernelFixedField_iff_exists_unramified_finite_subfield
      A K L x).mpr ⟨E, hfinite, hunram, hx⟩
  · intro x hx
    obtain ⟨E, hfinite, hunram, hxE⟩ :=
      (mem_originalKernelFixedField_iff_exists_unramified_finite_subfield
        A K L x).mp hx
    have hE : E ≤ maximalUnramifiedSubfield A K L :=
      le_iSup_of_le E (le_iSup_of_le hfinite (le_iSup_of_le hunram le_rfl))
    exact hE hxE

/-- The original maximal unramified subextension is Galois over K. -/
theorem maximalUnramifiedSubfield_isGalois :
    IsGalois K (maximalUnramifiedSubfield A K L) := by
  rw [maximalUnramifiedSubfield_eq_originalKernelFixedField A K L]
  infer_instance

end EtaleFundamentalGroups.StrictHenselian
