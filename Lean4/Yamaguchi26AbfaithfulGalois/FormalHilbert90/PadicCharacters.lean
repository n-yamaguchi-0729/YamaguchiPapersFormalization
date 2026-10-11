/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.FormalHilbert90.CharacterLifting
import GaloisCohomology.ProfiniteIntegers.PadicPrimaryQuotient
import ProCGroups.Abelian.PrimePowerCharacters
import ProCGroups.ProC.MaximalQuotients.ResidualQuotient

/-! # Detecting primary abelianization by p-adic characters -/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.Abelian ProCGroups.ProC

universe u

namespace PadicCocycle

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {θ : Orientation ℓ G} {U : Subgroup G}

omit [IsTopologicalGroup G] in
theorem map_one (c : PadicCocycle θ U) : c.toFun 1 = 0 := by
  have h := c.cocycle 1 1
  simp only [one_mul, Subgroup.coe_one, _root_.map_one, Units.val_one] at h
  exact (add_left_cancel (h.symm.trans (add_zero (c.toFun 1)).symm) : c.toFun 1 = 0)

omit [IsTopologicalGroup G] in
theorem map_conj (c : PadicCocycle θ U) (u d : U) (hd : θ (d : G) = 1) :
    c.toFun (u * d * u⁻¹) = (θ (u : G) : PadicInt ℓ) * c.toFun d := by
  have hi := c.cocycle u u⁻¹
  rw [mul_inv_cancel, c.map_one] at hi
  rw [c.cocycle, c.cocycle]
  simp only [Subgroup.coe_mul, _root_.map_mul, hd, mul_one]
  linear_combination -hi

/-- Restriction to an orientation-trivial subgroup is a continuous character. -/
def restrictCharacter (D : Subgroup G) (hDθ : D ≤ θ.toMonoidHom.ker)
    (hDU : D ≤ U) (c : PadicCocycle θ U) : D →ₜ* Multiplicative (PadicInt ℓ) where
  toFun d := Multiplicative.ofAdd (c.toFun (Subgroup.inclusion hDU d))
  map_one' := c.map_one
  map_mul' d e := by
    change c.toFun (Subgroup.inclusion hDU (d * e)) =
      c.toFun (Subgroup.inclusion hDU d) + c.toFun (Subgroup.inclusion hDU e)
    rw [_root_.map_mul, c.cocycle]
    rw [show θ ((Subgroup.inclusion hDU d : U) : G) = 1 from hDθ d.2,
      Units.val_one, one_mul]
  continuous_toFun := c.continuous_toFun.comp
    (continuous_subtype_val.subtype_mk fun d => hDU d.2)

/-- The p-adic character on the primary abelianization of the orientation kernel. -/
noncomputable def primaryCharacter [CompactSpace G]
    (D : Subgroup G) (hDclosed : IsClosed (D : Set G))
    (hDθ : D ≤ θ.toMonoidHom.ker) (hDU : D ≤ U) (c : PadicCocycle θ U) :
    PrimaryAbelianization ℓ D →ₜ* Multiplicative (PadicInt ℓ) := by
  letI : CompactSpace D := hDclosed.isClosedEmbedding_subtypeVal.compactSpace
  exact liftPadicCharacter (TopologicalAbelianization.lift
    (c.restrictCharacter D hDθ hDU))

theorem primaryCharacter_mk [CompactSpace G]
    (D : Subgroup G) (hDclosed : IsClosed (D : Set G))
    (hDθ : D ≤ θ.toMonoidHom.ker) (hDU : D ≤ U) (c : PadicCocycle θ U) (d : D) :
    (c.primaryCharacter D hDclosed hDθ hDU
      (QuotientGroup.mk' _ (TopologicalAbelianization.mk D d))).toAdd =
        c.toFun (Subgroup.inclusion hDU d) := rfl

theorem primaryCharacter_conj [CompactSpace G]
    (D : Subgroup G) [D.Normal] (hDclosed : IsClosed (D : Set G))
    (hDθ : D ≤ θ.toMonoidHom.ker) (hDU : D ≤ U) (c : PadicCocycle θ U)
    (u : U) (a : PrimaryAbelianization ℓ D) :
    (c.primaryCharacter D hDclosed hDθ hDU
      (primaryConjugationMap ℓ D hDclosed (u : G) a)).toAdd =
        (θ (u : G) : PadicInt ℓ) *
          (c.primaryCharacter D hDclosed hDθ hDU a).toAdd := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ a
  obtain ⟨d, rfl⟩ := TopologicalAbelianization.surjective_mk D b
  change c.toFun (Subgroup.inclusion hDU ((MulAut.conjNormal (u : G)) d)) = _
  rw [primaryCharacter_mk]
  exact c.map_conj u (Subgroup.inclusion hDU d) (hDθ d.2)

end PadicCocycle

/-- Every nonidentity primary class is detected by a p-adic cocycle on an open
normal supergroup of the orientation kernel. -/
theorem exists_padicCocycle_detecting_primary
    {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (D : Subgroup G) [D.Normal] (hDclosed : IsClosed (D : Set G))
    (θ : Orientation ℓ G) (hDθ : D ≤ θ.toMonoidHom.ker)
    (hLift : RelativeFormalHilbert90 D θ)
    (a : PrimaryAbelianization ℓ D) (ha : a ≠ 1) :
    ∃ U : OpenNormalSubgroup G, ∃ hDU : D ≤ (U : Subgroup G),
      ∃ c : PadicCocycle θ (U : Subgroup G),
        (c.primaryCharacter D hDclosed hDθ hDU a).toAdd ≠ 0 := by
  let : CompactSpace D := hDclosed.isClosedEmbedding_subtypeVal.compactSpace
  let : TotallyDisconnectedSpace (TopologicalAbelianization D) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator D) (Subgroup.isClosed_closedCommutator D)
  have : IsClosed (proCResidualCore (ProCGroups.FiniteGroupClass.pGroup ℓ)
      (TopologicalAbelianization D) : Set (TopologicalAbelianization D)) :=
    proCResidualCore_isClosed _ _
  have hP : HasOpenNormalBasisInClass (ProCGroups.FiniteGroupClass.pGroup ℓ)
      (PrimaryAbelianization ℓ D) :=
    proCResidualCoreQuotient_hasOpenNormalBasisInClass
      (ProCGroups.FiniteGroupClass.pGroup_formation ℓ)
  obtain ⟨n, hn, χ, hχ⟩ := exists_primePower_character_proP hP ha
  let π : D →ₜ* PrimaryAbelianization ℓ D :=
    { toMonoidHom := (QuotientGroup.mk' _).comp (TopologicalAbelianization.mk D)
      continuous_toFun := QuotientGroup.continuous_mk.comp
        (TopologicalAbelianization.mkₜ D).continuous }
  obtain ⟨U, hDU, c, hc⟩ := exists_openNormal_padicCocycle_lifting_character
    D hDclosed θ hDθ hLift n hn (χ.comp π)
  refine ⟨U, hDU, c, ?_⟩
  intro hz
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective _ a
  obtain ⟨d, hd⟩ := TopologicalAbelianization.surjective_mk D b
  have hπ : π d = a := congrArg (QuotientGroup.mk' _) hd |>.trans hb
  apply hχ
  apply Multiplicative.toAdd.injective
  have hc0 : c.toFun (Subgroup.inclusion hDU d) = 0 := by
    rw [← c.primaryCharacter_mk D hDclosed hDθ hDU d]
    change (c.primaryCharacter D hDclosed hDθ hDU (π d)).toAdd = 0
    rw [hπ, hz]
  have hh := hc d
  change PadicInt.toZModPow n (c.toFun (Subgroup.inclusion hDU d)) =
    (χ (π d)).toAdd at hh
  rw [hc0, map_zero, hπ] at hh
  exact hh.symm

end Yamaguchi26AbfaithfulGalois
