/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.Theorem6Dot1FormalHilbert90
import GaloisCohomology.ProfiniteIntegers.PadicPrimaryQuotient
import ProCGroups.Abelian.Transfer

/-!
# Transfer on fixed primary classes

Transfer of a p-adic character evaluates on a globally fixed primary
class as multiplication by the index of the open normal subgroup.
-/

namespace Yamaguchi26AbfaithfulGalois
open ProCGroups.Abelian ProCGroups.ProC ProCGroups.FiniteStepSolvableQuotients
universe u

/-- Transfer of a p-adic character evaluates on a globally fixed primary class
as multiplication by the index of the open normal subgroup. -/
theorem exists_primaryCharacter_transfer_fixed
    {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (D : Subgroup G) [D.Normal] (hD : IsClosed (D : Set G))
    (U : OpenNormalSubgroup G) (hDU : D ≤ (U : Subgroup G))
    (χ : (U : Subgroup G) →ₜ* Multiplicative (PadicInt ℓ))
    (f : PrimaryAbelianization ℓ D →ₜ* Multiplicative (PadicInt ℓ))
    (hχ : ∀ d : D, χ (Subgroup.inclusion hDU d) =
      f (QuotientGroup.mk' (proCResidualCore (ProCGroups.FiniteGroupClass.pGroup ℓ)
        (TopologicalAbelianization D)) (TopologicalAbelianization.mk D d))) :
    ∃ F : GroupPrimaryAbelianization ℓ G →ₜ* Multiplicative (PadicInt ℓ),
      ∀ a : PrimaryAbelianization ℓ D,
        a ∈ primaryFixedSubgroup ℓ D hD (⊤ : Subgroup G) →
          F (primaryInclusionMap ℓ D hD a) =
            f a ^ Nat.card (G ⧸ (U : Subgroup G)) := by
  classical
  let ψ := openNormalCharacterTransfer U χ
  let F := liftPadicCharacter (TopologicalAbelianization.lift ψ)
  refine ⟨F, ?_⟩
  intro a ha
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
    (proCResidualCore (ProCGroups.FiniteGroupClass.pGroup ℓ) (TopologicalAbelianization D)) a
  obtain ⟨d, rfl⟩ := TopologicalAbelianization.surjective_mk D b
  change ψ (d : G) =
    f (QuotientGroup.mk' (proCResidualCore (ProCGroups.FiniteGroupClass.pGroup ℓ)
      (TopologicalAbelianization D)) (TopologicalAbelianization.mk D d)) ^
      Nat.card (G ⧸ (U : Subgroup G))
  let : Fintype (G ⧸ (U : Subgroup G)) := Fintype.ofFinite _
  change openNormalCharacterTransfer U χ (Subgroup.inclusion hDU d) = _
  rw [openNormalCharacterTransfer_apply_of_mem]
  have hterm (q : G ⧸ (U : Subgroup G)) :
      χ (MulAut.conjNormal ((quotientOpenSubgroupSection (U : Subgroup G) q)⁻¹)
        (Subgroup.inclusion hDU d)) =
      f (QuotientGroup.mk' (proCResidualCore (ProCGroups.FiniteGroupClass.pGroup ℓ)
        (TopologicalAbelianization D)) (TopologicalAbelianization.mk D d)) := by
    let g := (quotientOpenSubgroupSection (U : Subgroup G) q)⁻¹
    have hconj : MulAut.conjNormal g (Subgroup.inclusion hDU d) =
        Subgroup.inclusion hDU (MulAut.conjNormal g d) := Subtype.ext rfl
    change χ (MulAut.conjNormal g (Subgroup.inclusion hDU d)) = _
    rw [hconj, hχ]
    have hfixed := ha (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G))
    change QuotientGroup.mk' _ (TopologicalAbelianization.mk D (MulAut.conjNormal g d)) =
      QuotientGroup.mk' _ (TopologicalAbelianization.mk D d) at hfixed
    exact congrArg f hfixed
  calc
    _ = ∏ _q : G ⧸ (U : Subgroup G),
        f (QuotientGroup.mk' (proCResidualCore (ProCGroups.FiniteGroupClass.pGroup ℓ)
          (TopologicalAbelianization D)) (TopologicalAbelianization.mk D d)) :=
      Fintype.prod_congr _ _ hterm
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]

end Yamaguchi26AbfaithfulGalois
