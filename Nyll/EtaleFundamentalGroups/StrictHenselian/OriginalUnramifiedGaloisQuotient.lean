/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.OriginalUnramifiedSubfield
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# The original maximal-unramified Galois quotient

The maximal unramified subfield was independently defined by its actual
finite unramified subextensions. Its proved equality with the actual
fraction-point kernel fixed field now supplies the topological quotient,
including the exact equation identifying the scheme map with restriction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.StrictHenselian

universe u v

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [FaithfulSMul A L] [IsGalois K L] [IsSepClosed L]

/-- The actual fundamental group of Spec A is the Galois group of the
specifically defined maximal unramified subfield of the original L/K.
The actual generic map becomes the literal restriction of automorphisms. -/
theorem exists_originalUnramifiedFundamentalGroupEquivGalois :
    let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
    let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    let : IsSepClosure (FractionRing A) L := originalFractionField_isSepClosure A K L
    let : IsGalois K (maximalUnramifiedSubfield A K L) :=
      maximalUnramifiedSubfield_isGalois A K L
    ∃ e : π₁ᵉᵗ(ξ (FractionRing A) L ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) ≃ₜ*
          Gal(maximalUnramifiedSubfield A K L/K),
      ∀ σ : Gal(L/K), e (originalFractionAbsoluteGaloisHom A K L σ) =
        AlgEquiv.restrictNormalHom (maximalUnramifiedSubfield A K L) σ := by
  intro actualFractionAlgebra actualAmbientAlgebra actualSepClosure actualUnramifiedGalois
  let q := originalFractionAbsoluteGaloisHom A K L
  let H : ClosedSubgroup Gal(L/K) :=
    { toSubgroup := q.toMonoidHom.ker
      isClosed' := isClosed_eq q.continuous continuous_const }
  have : H.toSubgroup.Normal := inferInstanceAs q.toMonoidHom.ker.Normal
  let M₀ := IntermediateField.fixedField q.toMonoidHom.ker
  let quotientEquiv := QuotientGroup.quotientKerEquivOfSurjective q.toMonoidHom
    (originalFractionAbsoluteGaloisHom_surjective A K L)
  let eMul := quotientEquiv.symm.trans (InfiniteGalois.normalAutEquivQuotient H)
  have heMul (σ : Gal(L/K)) : eMul (q σ) = AlgEquiv.restrictNormalHom M₀ σ := by
    change InfiniteGalois.normalAutEquivQuotient H
      (quotientEquiv.symm (quotientEquiv (QuotientGroup.mk σ))) = _
    rw [quotientEquiv.symm_apply_apply]
    rfl
  have hcontinuous : Continuous eMul := by
    have hq : Topology.IsQuotientMap q :=
      Topology.IsQuotientMap.of_surjective_continuous
        (originalFractionAbsoluteGaloisHom_surjective A K L) q.continuous
    rw [hq.continuous_iff]
    have hcomp : eMul ∘ q = AlgEquiv.restrictNormalHom M₀ := funext heMul
    rw [hcomp]
    exact InfiniteGalois.restrictNormalHom_continuous M₀
  let : T2Space Gal(M₀/K) := krullTopology_t2
  let e : π₁ᵉᵗ(ξ (FractionRing A) L ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) ≃ₜ* Gal(M₀/K) :=
    ContinuousMulEquiv.mk'
      (eMul.toEquiv.toHomeomorphOfContinuousClosed hcontinuous hcontinuous.isClosedMap)
      eMul.map_mul
  have hM : maximalUnramifiedSubfield A K L = M₀ :=
    maximalUnramifiedSubfield_eq_originalKernelFixedField A K L
  have hfixed : ∃ e : π₁ᵉᵗ(ξ (FractionRing A) L ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) ≃ₜ* Gal(M₀/K),
      ∀ σ : Gal(L/K), e (q σ) = AlgEquiv.restrictNormalHom M₀ σ :=
    ⟨e, heMul⟩
  let P : IntermediateField K L → Prop := fun N =>
    ∀ hN : IsGalois K N,
      let : IsGalois K N := hN
      ∃ e : π₁ᵉᵗ(ξ (FractionRing A) L ≫
          Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) ≃ₜ* Gal(N/K),
        ∀ σ : Gal(L/K), e (q σ) = AlgEquiv.restrictNormalHom N σ
  have hP₀ : P M₀ := by
    intro hN
    exact hfixed
  have hP : P (maximalUnramifiedSubfield A K L) := Eq.mpr (congrArg P hM) hP₀
  exact hP actualUnramifiedGalois

end EtaleFundamentalGroups.StrictHenselian
