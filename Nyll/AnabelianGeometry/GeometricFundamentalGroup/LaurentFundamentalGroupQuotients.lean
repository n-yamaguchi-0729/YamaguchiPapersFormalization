/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentCoverAutomorphisms
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Nyll.EtaleFundamentalGroups.Pi1.FiniteEtale.GaloisCategory
import Nyll.EtaleFundamentalGroups.GaloisCategories.GaloisObjectQuotient
import Nyll.ProCGroups.ProC.InverseLimits.Predicates
import Nyll.ProCGroups.Generation.Procyclic
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Cyclic finite quotients of the actual multiplicative-line fundamental group

The stabilizers of pointed Galois covers form a neighbourhood basis for the actual fibre-functor
automorphism group. Each such stabilizer is the kernel of the quotient to the opposite cover
automorphism group. The proved geometric cyclicity therefore implies cyclicity of every open
normal quotient. No classification of covers or cofinal Kummer system is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open scoped Topology

namespace AnabelianGeometry.GeometricFundamentalGroup

/-- Every open normal quotient of the actual etale fundamental group of the multiplicative
line is cyclic over an algebraically closed field of characteristic zero. -/
theorem isCyclic_openNormalQuotient_fundamentalGroup_laurent
    {K Ω : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (LaurentPolynomial K)))
    (U : OpenNormalSubgroup π₁ᵉᵗ(ξ)) : IsCyclic (π₁ᵉᵗ(ξ) ⧸ (U : Subgroup π₁ᵉᵗ(ξ))) := by
  let F := fiber ξ
  have hU : (U : Set (Aut F)) ∈ 𝓝 (1 : Aut F) :=
    U.toOpenSubgroup.isOpen'.mem_nhds U.one_mem'
  obtain ⟨A, _, hA⟩ := (nhds_one_has_basis_stabilizers F).mem_iff.mp hU
  have connected : ConnectedSpace A.obj.left := connectedSpace_left_of_isConnected A.obj
  have cyclicCover : IsCyclic (Aut A.obj) := isCyclic_aut_of_connected_finite_etale_laurent A.obj
  have cyclicOpposite : IsCyclic (Aut A.obj)ᵐᵒᵖ :=
    isCyclic_of_surjective (MulEquiv.inv' (Aut A.obj)).toMonoidHom
      (MulEquiv.inv' (Aut A.obj)).surjective
  let q : Aut F →* (Aut A.obj)ᵐᵒᵖ := galoisObjectQuotientMonoidHom F (Aut F) A.obj A.pt
  have kernel_le : q.ker ≤ (U : Subgroup (Aut F)) := by
    rw [galoisObjectQuotientMonoidHom_ker]
    exact hA
  let e : (Aut F ⧸ q.ker) ≃* q.range := QuotientGroup.quotientKerEquivRange q
  have cyclicKernelQuotient : IsCyclic (Aut F ⧸ q.ker) :=
    isCyclic_of_injective e.toMonoidHom e.injective
  let projection : (Aut F ⧸ q.ker) →* (Aut F ⧸ (U : Subgroup (Aut F))) :=
    QuotientGroup.map q.ker (U : Subgroup (Aut F)) (MonoidHom.id (Aut F)) kernel_le
  apply isCyclic_of_surjective projection
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup (Aut F)) x
  exact ⟨QuotientGroup.mk' q.ker g, rfl⟩

/-- The actual quotient topology on the multiplicative-line fundamental group admits an open
normal basis with cyclic finite quotients. -/
theorem hasCyclicOpenNormalBasis_fundamentalGroup_laurent
    {K Ω : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (LaurentPolynomial K))) :
    ProCGroups.ProC.HasCyclicOpenNormalBasis π₁ᵉᵗ(ξ) := by
  apply ProCGroups.ProC.HasOpenNormalBasisInClass.of_allOpenNormalQuotients
  intro U
  exact ⟨inferInstance, isCyclic_openNormalQuotient_fundamentalGroup_laurent ξ U⟩

/-- The actual multiplicative-line fundamental group has a topological generator. -/
theorem exists_topological_generator_fundamentalGroup_laurent
    {K Ω : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (LaurentPolynomial K))) :
    ∃ g : π₁ᵉᵗ(ξ), ProCGroups.Generation.TopologicallyGenerates ({g} : Set π₁ᵉᵗ(ξ)) := by
  exact ProCGroups.Generation.exists_topologicallyGenerates_singleton_of_cyclic_quotients
    (isCyclic_openNormalQuotient_fundamentalGroup_laurent ξ)

end AnabelianGeometry.GeometricFundamentalGroup
