/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.FiberQuotient
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenNormalUniverse
import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ClosedCommutator
import Nyll.ProCGroups.Profinite.Basic

/-!
# Kernels and finite-etale quotient extensions

If a finite-etale cover on the source of a scheme morphism is the pullback of
an actual finite-etale cover on the target, the kernel of the induced map on
fundamental groups fixes every point of its geometric fibre.  For a pointed
Galois cover this says that the kernel is killed by the represented finite
quotient.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace CategoryTheory.PreGaloisCategory

universe u₁ u₂ v₁ v₂ w

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
variable {C' : Type v₁} [Category.{v₂} C'] [GaloisCategory C']
variable {F : C ⥤ FintypeCat.{w}} [FiberFunctor F]
variable {F' : C' ⥤ FintypeCat.{w}} [FiberFunctor F']

/-- The kernel of the homomorphism induced by a functor of Galois
categories fixes every fibre point of an object which is explicitly
isomorphic to an object in the functor's image. -/
theorem autHomOfCompIso_kernel_fixed_of_obj_iso
    (H : C ⥤ C') (t : H ⋙ F' ≅ F)
    (X : C) (X' : C') (e : H.obj X ≅ X')
    (a : Aut F') (ha : autHomOfCompIso H t a = 1)
    (x : F'.obj X') :
    a • x = x := by
  let s := (functorToContActionCompIso H t).app X
  let ef := F'.mapIso e
  let y : F'.obj (H.obj X) := ef.inv x
  have heq := ConcreteCategory.congr_hom (s.hom.hom.comm a) y
  change (t.app X).hom (a • y) =
    autHomOfCompIso H t a • (t.app X).hom y at heq
  rw [ha, one_smul] at heq
  have hy : a • y = y := by
    exact (ConcreteCategory.bijective_of_isIso (t.app X).hom).injective heq
  have hxy : ef.hom y = x := FintypeCat.inv_hom_id_apply ef x
  calc
    a • x = a • ef.hom y := congrArg (a • ·) hxy.symm
    _ = ef.hom (a • y) := by
      change a • F'.map e.hom y = F'.map e.hom (a • y)
      exact mulAction_naturality F' a e.hom y
    _ = ef.hom y := congrArg ef.hom hy
    _ = x := hxy

end CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u v

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]

/-- A finite discrete abelian representation of an etale fundamental group
is represented, at the level of kernels, by a pointed finite-etale Galois
cover whose deck group is abelian. -/
theorem exists_abelianGaloisCover_quotient_ker_eq
    (xi : Spec (.of Omega) ⟶ X)
    (A : Type v) [Finite A] [TopologicalSpace A]
    [CommGroup A] [DiscreteTopology A]
    (phi : π₁ᵉᵗ(xi) →ₜ* A) :
    ∃ (W : FiniteEtale X) (hW : IsGalois W)
      (w : (fiber xi).obj W),
      letI : IsGalois W := hW
      IsMulCommutative (Aut W) ∧
        (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
          xi W hW w).ker = phi.ker := by
  let U : OpenNormalSubgroup π₁ᵉᵗ(xi) :=
    ProCGroups.ProC.OpenNormalSubgroup.ker phi
  obtain ⟨W, hW, w, hw⟩ :=
    exists_galois_object_point_stabilizer_eq_any_universe
      (C := FiniteEtale X) (fiber xi) U
  let : IsGalois W := hW
  let q :=
    EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
      xi W hW w
  have hqker : q.ker = phi.ker := by
    calc
      q.ker = MulAction.stabilizer π₁ᵉᵗ(xi) w :=
        EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_ker
          xi W hW w
      _ = (U : Subgroup π₁ᵉᵗ(xi)) := hw
      _ = phi.ker := rfl
  have hqsurj : Function.Surjective q :=
    EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_surjective
      xi W hW w
  have hcomm : IsMulCommutative (Aut W) :=
    IsMulCommutative.of_comm fun sigma tau ↦ by
      obtain ⟨g, hg⟩ := hqsurj (MulOpposite.op sigma)
      obtain ⟨h, hh⟩ := hqsurj (MulOpposite.op tau)
      have hphi : phi (g * h) = phi (h * g) := by
        simp only [map_mul]
        exact mul_comm _ _
      have hdiffPhi : g * h * (h * g)⁻¹ ∈ phi.ker := by
        apply MonoidHom.mem_ker.mpr
        change phi.toMonoidHom (g * h) =
          phi.toMonoidHom (h * g) at hphi
        rw [map_mul, map_inv, hphi, mul_inv_cancel]
      have hdiffQ : g * h * (h * g)⁻¹ ∈ q.ker := by
        rw [hqker]
        exact hdiffPhi
      have hqeq : q (g * h) = q (h * g) := by
        rw [← mul_inv_eq_one]
        rw [← map_inv, ← map_mul]
        exact MonoidHom.mem_ker.mp hdiffQ
      rw [map_mul, hg, hh, map_mul, hh, hg] at hqeq
      have hunop := congrArg MulOpposite.unop hqeq
      exact hunop.symm
  exact ⟨W, hW, w, hcomm, hqker⟩

/-- If a pointed finite-etale Galois cover of `X` extends over `Y`, the
finite quotient represented by the cover kills the kernel of
`pi₁(X) → pi₁(Y)`. -/
theorem fundamentalGroupHom_ker_le_finiteEtaleGaloisCoverQuotient_ker_of_pullback_iso
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (W : FiniteEtale X) (hW : IsGalois W)
    (w : (fiber xi).obj W)
    (Z : FiniteEtale Y) (e : (pullback f).obj Z ≅ W) :
    (fundamentalGroupHom f xi).ker ≤
      (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
        xi W hW w).ker := by
  let : IsGalois W := hW
  rw [EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_ker]
  intro a ha
  change a • w = w
  exact autHomOfCompIso_kernel_fixed_of_obj_iso
    (pullback f) (pullbackFiberIso f xi) Z W e a
      (MonoidHom.mem_ker.mp ha) w

/-- If every finite-etale Galois cover of the source extends to the target,
then the induced map on fundamental groups is injective.  It is enough to
extend Galois covers because their pointed quotients realize all open normal
subgroups, which separate points in a profinite group. -/
theorem fundamentalGroupHom_injective_of_galoisCover_extensions
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (extend : ∀ (W : FiniteEtale X) (_hW : IsGalois W),
      Σ Z : FiniteEtale Y, (pullback f).obj Z ≅ W) :
    Function.Injective (fundamentalGroupHom f xi) := by
  intro a b hab
  have hker : a * b⁻¹ ∈ (fundamentalGroupHom f xi).ker := by
    apply MonoidHom.mem_ker.mpr
    change (fundamentalGroupHom f xi).toMonoidHom a =
      (fundamentalGroupHom f xi).toMonoidHom b at hab
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have hone : a * b⁻¹ = 1 := by
    apply ProCGroups.ProfiniteGrp.eq_one_of_mem_all_openNormalSubgroups
    intro U
    obtain ⟨W, hW, w, hw⟩ :=
      exists_galois_object_point_stabilizer_eq_any_universe
        (fiber xi) U
    let : IsGalois W := hW
    obtain ⟨Z, e⟩ := extend W hW
    have hle : (fundamentalGroupHom f xi).ker ≤
        (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
          xi W hW w).ker :=
      fundamentalGroupHom_ker_le_finiteEtaleGaloisCoverQuotient_ker_of_pullback_iso
        f xi W hW w Z e
    rw [← hw, ←
      EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_ker
        xi W hW w]
    exact hle hker
  have hmul := congrArg (fun z ↦ z * b) hone
  simpa [mul_assoc] using hmul

/-- If every finite abelian Galois quotient cover on the source is supplied
with an actual finite-etale extension object on the target and a pullback
isomorphism, then every finite discrete abelian representation kills the
kernel of the induced fundamental-group map. -/
theorem fundamentalGroupHom_finiteDiscreteAbelianMapsKillKernel_of_galoisCover_extensions
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (extend : ∀ (W : FiniteEtale X) (_hW : IsGalois W),
      IsMulCommutative (Aut W) →
        Σ Z : FiniteEtale Y, (pullback f).obj Z ≅ W) :
    ProCGroups.ProC.FiniteDiscreteAbelianMapsKillKernel
      (fundamentalGroupHom f xi) := by
  intro A _hAfinite _hAtopology _hAcomm _hAdiscrete phi
  obtain ⟨W, hW, w, hWcomm, hker⟩ :=
    exists_abelianGaloisCover_quotient_ker_eq xi A phi
  obtain ⟨Z, e⟩ := extend W hW hWcomm
  calc
    (fundamentalGroupHom f xi).ker ≤
        (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
          xi W hW w).ker :=
      fundamentalGroupHom_ker_le_finiteEtaleGaloisCoverQuotient_ker_of_pullback_iso
        f xi W hW w Z e
    _ = phi.ker := hker

end AlgebraicGeometry.FiniteEtale

end
