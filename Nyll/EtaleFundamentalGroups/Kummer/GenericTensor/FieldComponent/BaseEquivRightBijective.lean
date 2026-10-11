/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ChosenPrime.RootRefinedComponentLocal

/-!
# Right-coordinate bijectivity after a trivial field base change

If the field map on the left tensor factor is bijective, the tensor product
collapses to its right factor.  Every maximal quotient component is therefore
the literal collapse component, and its canonical right algebra map is an
isomorphism of underlying functions.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uK₀ uK₁ uL

variable {K₀ : Type uK₀} {K₁ : Type uK₁} {L : Type uL}
variable [Field K₀] [Field K₁] [Field L]
variable [Algebra K₀ K₁] [Algebra K₀ L]

/-- A bijective base-field map makes the canonical right map into every
selected tensor component bijective.  The maximal component is not compared
by hypothesis: its equality with the collapse kernel is produced internally. -/
theorem genericTensorFieldComponentRight_bijective_of_base_bijective
    (hbase : Function.Bijective (algebraMap K₀ K₁))
    (m : Ideal (K₁ ⊗[K₀] L)) [m.IsMaximal] :
    letI : Algebra L (GenericTensorFieldComponent m) :=
      genericTensorFieldComponentRightAlgebra m
    Function.Bijective
      (algebraMap L (GenericTensorFieldComponent m)) := by
  let : Algebra L (GenericTensorFieldComponent m) :=
    genericTensorFieldComponentRightAlgebra m
  let eForward : K₀ ≃ₐ[K₀] K₁ :=
    AlgEquiv.ofBijective (Algebra.ofId K₀ K₁) hbase
  let e : K₁ ≃ₐ[K₀] K₀ := eForward.symm
  let T : (K₁ ⊗[K₀] L) ≃ₐ[K₀] L :=
    tensorAlongFieldEquivCollapseAlgEquiv
      (E := K₀) (K := K₁) (M := L) e
  let q := tensorAlongFieldEquivCollapseIdeal
    (E := K₀) (K := K₁) (M := L) e
  let : q.IsMaximal :=
    tensorAlongFieldEquivCollapseIdeal_isMaximal
      (E := K₀) (K := K₁) (M := L) e
  let Eq : GenericTensorFieldComponent q ≃ₐ[K₀] L :=
    tensorAlongFieldEquivCollapseComponentAlgEquiv
      (E := K₀) (K := K₁) (M := L) e
  have hmk (z : K₁ ⊗[K₀] L) :
      Eq (Ideal.Quotient.mk q z) = T z := by
    exact Ideal.quotientKerAlgEquivOfSurjective_mk T.surjective z
  have hqcoord (y : L) :
      Eq (genericTensorFieldComponentRight q y) = y := by
    change Eq (Ideal.Quotient.mk q ((1 : K₁) ⊗ₜ[K₀] y)) = y
    rw [hmk]
    simp [T, tensorAlongFieldEquivCollapseAlgEquiv]
  have hqright : Function.Bijective
      (genericTensorFieldComponentRight q) := by
    constructor
    · intro x y hxy
      have := congrArg Eq hxy
      simpa only [hqcoord] using this
    · intro z
      refine ⟨Eq z, Eq.injective ?_⟩
      exact hqcoord (Eq z)
  have hqbot : q = ⊥ := by
    change RingHom.ker T.toRingHom = ⊥
    exact (RingHom.injective_iff_ker_eq_bot T.toRingHom).mp T.injective
  have hqm : q = m := by
    exact (inferInstance : q.IsMaximal).eq_of_le
      (inferInstance : m.IsMaximal).ne_top (by
        rw [hqbot]
        exact bot_le)
  let E : GenericTensorFieldComponent q ≃ₐ[K₁]
      GenericTensorFieldComponent m :=
    Ideal.quotientEquivAlgOfEq K₁ hqm
  have hcoord (y : L) :
      E (genericTensorFieldComponentRight q y) =
        genericTensorFieldComponentRight m y := by
    change E (Ideal.Quotient.mk q ((1 : K₁) ⊗ₜ[K₀] y)) =
      Ideal.Quotient.mk m ((1 : K₁) ⊗ₜ[K₀] y)
    exact Ideal.quotientEquivAlgOfEq_mk K₁ hqm _
  have hright : Function.Bijective
      (genericTensorFieldComponentRight m) := by
    have htransported : Function.Bijective
        (fun y : L ↦ E (genericTensorFieldComponentRight q y)) := by
      change Function.Bijective
        (E ∘ genericTensorFieldComponentRight q)
      exact E.bijective.comp hqright
    simpa only [hcoord] using htransported
  change Function.Bijective (genericTensorFieldComponentRight m)
  exact hright

end EtaleFundamentalGroups.Kummer

end
