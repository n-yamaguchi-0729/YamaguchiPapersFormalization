/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality

/-!
# The canonical field fundamental-group map

The field-specific comparison of geometric fibers agrees with the usual
fundamental-group map after transporting the composite geometric point to the
chosen point.  The only remaining ambiguity is the explicit inner
conjugation obtained by comparing the two fiber-functor isomorphisms.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

variable (k K Omega : Type u)
variable [Field k] [Field K] [Field Omega]
variable [Algebra k K] [Algebra K Omega] [Algebra k Omega]
variable [IsScalarTower k K Omega] [IsSepClosed Omega]

/-- Transport of the canonical composite geometric point to the geometric
point defined by the composite algebra map. -/
noncomputable def fieldBasePointFiberIso :
    fiber (ξ K Omega ≫ ξ k K) ≅ fib k Omega :=
  eqToIso (congrArg fiber (fieldGeometricPoint_comp k K Omega))

/-- The field-specific comparison with its target transported back to the
literal composite geometric point. -/
private noncomputable def fieldUntransportedPullbackFiberIso :
    pullback (ξ k K) ⋙ fib K Omega ≅ fiber (ξ K Omega ≫ ξ k K) :=
  fieldPullbackFiberIso k K Omega ≪≫
    (fieldBasePointFiberIso k K Omega).symm

/-- The explicit automorphism measuring the difference between the canonical
transported comparison and the field-specific comparison. -/
noncomputable def fieldFundamentalGroupComparisonAut : Aut (fib k Omega) :=
  (fieldBasePointFiberIso k K Omega).conjAut
    ((pullbackFiberIso (ξ k K) (ξ K Omega)).symm ≪≫
      (fieldPullbackFiberIso k K Omega ≪≫
        (fieldBasePointFiberIso k K Omega).symm))

private theorem conjAut_symm_cancel
    {C : Type u} [Category C] {F G : C}
    (p : F ≅ G) (a : Aut G) :
    p.conjAut (p.symm.conjAut a) = a := by
  rw [← p.symm.trans_conjAut p]
  rw [p.symm_self_id]
  apply Aut.ext
  exact Iso.refl_conj a.hom

private theorem conjAut_inner
    {C : Type u} [Category C] {F G : C}
    (p : F ≅ G) (a b : Aut F) :
    p.conjAut (MulAut.conj a b) =
      MulAut.conj (p.conjAut a) (p.conjAut b) := by
  simp only [MulAut.conj_apply, map_mul, map_inv]

private theorem fieldFundamentalGroupHom_eq_conj_core
    (sigma : Aut (fib K Omega)) :
    CategoryTheory.PreGaloisCategory.autHomOfCompIso
        (pullback (ξ k K))
        (fieldUntransportedPullbackFiberIso k K Omega) sigma =
      MulAut.conj
        (G := Aut (fiber (ξ K Omega ≫ ξ k K)))
        ((pullbackFiberIso (ξ k K) (ξ K Omega)).symm ≪≫
          fieldUntransportedPullbackFiberIso k K Omega)
        (fundamentalGroupHom (ξ k K) (ξ K Omega) sigma) := by
  exact fundamentalGroupHom_eq_conj_of_comparison
    (ξ k K) (ξ K Omega)
    (fieldUntransportedPullbackFiberIso k K Omega) sigma

/-- After transport along the equality of base points, the field-specific
fundamental-group homomorphism differs from the usual one precisely by inner
conjugation with `fieldFundamentalGroupComparisonAut`. -/
theorem fieldFundamentalGroupHom_eq_conj_fundamentalGroupHom
    (sigma : Aut (fib K Omega)) :
    fieldFundamentalGroupHom k K Omega inferInstance sigma =
      MulAut.conj (G := Aut (fib k Omega))
        (fieldFundamentalGroupComparisonAut k K Omega)
        ((fieldBasePointFiberIso k K Omega).conjAut
          (fundamentalGroupHom (ξ k K) (ξ K Omega) sigma)) := by
  let p := fieldBasePointFiberIso k K Omega
  let t := fieldUntransportedPullbackFiberIso k K Omega
  have htransport :
      p.conjAut
          (CategoryTheory.PreGaloisCategory.autHomOfCompIso
            (pullback (ξ k K)) t sigma) =
        fieldFundamentalGroupHom k K Omega inferInstance sigma := by
    rw [CategoryTheory.PreGaloisCategory.autHomOfCompIso_apply]
    change p.conjAut
        ((fieldPullbackFiberIso k K Omega ≪≫ p.symm).conjAut _) =
      (fieldPullbackFiberIso k K Omega).conjAut _
    rw [Iso.trans_conjAut]
    exact conjAut_symm_cancel p _
  let a : Aut (fiber (ξ K Omega ≫ ξ k K)) :=
    (pullbackFiberIso (ξ k K) (ξ K Omega)).symm ≪≫ t
  let b : Aut (fiber (ξ K Omega ≫ ξ k K)) :=
    fundamentalGroupHom (ξ k K) (ξ K Omega) sigma
  have h := congrArg (fun x : Aut (fiber (ξ K Omega ≫ ξ k K)) ↦ p.conjAut x)
    (fieldFundamentalGroupHom_eq_conj_core k K Omega sigma)
  rw [htransport] at h
  change _ = p.conjAut (MulAut.conj a b) at h
  rw [conjAut_inner p a b] at h
  change _ = MulAut.conj (p.conjAut a) (p.conjAut b)
  exact h

end AlgebraicGeometry.FiniteEtale

end
