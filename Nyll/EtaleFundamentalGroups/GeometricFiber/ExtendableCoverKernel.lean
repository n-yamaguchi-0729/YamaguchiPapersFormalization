/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCategories.GaloisObjectQuotient
import Nyll.EtaleFundamentalGroups.GaloisCategories.Surjectivity
import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
import Nyll.EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective
import Nyll.EtaleFundamentalGroups.Pi1.FiniteEtale.GaloisCategory

/-!
# Detecting the fundamental-group kernel by covers that extend

For a morphism inducing a surjective homomorphism on fundamental groups, its
kernel is the intersection of the pointed Galois quotient kernels for covers
which are actually pullbacks from the target. The descent condition is an
existence of an actual cover and an isomorphism; no extension theorem is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

private theorem isGalois_obj_of_connected
    {C C' : Type*} [Category C] [Category C']
    [GaloisCategory C] [GaloisCategory C']
    (F : C ⥤ FintypeCat) [FiberFunctor F]
    (F' : C' ⥤ FintypeCat) [FiberFunctor F']
    (H : C ⥤ C') (t : H ⋙ F' ≅ F)
    (Z : C) [IsGalois Z] [IsConnected (H.obj Z)] :
    IsGalois (H.obj Z) := by
  apply (isGalois_iff_pretransitive F' (H.obj Z)).mpr
  constructor
  intro x y
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut Z)
    ((t.app Z).hom x) ((t.app Z).hom y)
  refine ⟨H.mapAut Z σ, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (t.app Z).hom).injective
  have hn := ConcreteCategory.congr_hom (t.hom.naturality σ.hom) x
  change (t.app Z).hom ((H.mapAut Z σ) • x) = σ • ((t.app Z).hom x) at hn
  exact hn.trans hσ

/-- The kernel is detected by the pointed finite Galois covers which are
isomorphic to actual pullbacks from the target scheme. -/
theorem fundamentalGroupHom_ker_eq_iInf_extendableGalois
    {U X : Scheme.{0}} [ConnectedSpace U] [ConnectedSpace X]
    (j : U ⟶ X) {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ U)
    (hsurj : Function.Surjective (fundamentalGroupHom j ξ)) :
    (fundamentalGroupHom j ξ).toMonoidHom.ker =
      ⨅ (W : FiniteEtale U) (hW : IsGalois W) (w : (fiber ξ).obj W)
        (_h : ∃ Z : FiniteEtale X, Nonempty ((pullback j).obj Z ≅ W)),
        (let : IsGalois W := hW
         galoisObjectQuotientMonoidHom (fiber ξ) π₁ᵉᵗ(ξ) W w).ker := by
  let F := fiber (ξ ≫ j)
  let F' := fiber ξ
  let H := pullback j
  let t : H ⋙ F' ≅ F := pullbackFiberIso j ξ
  let : Limits.PreservesLimitsOfShape (Discrete PEmpty.{1}) H :=
    pullback_preservesLimitsOfShape_pempty j
  have hconn : ∀ Z : FiniteEtale X, IsConnected Z → IsConnected (H.obj Z) :=
    ((autHomOfCompIso_surjective_tfae F F' H t).out 1 3).mp hsurj
  apply le_antisymm
  · intro g hg
    simp only [Subgroup.mem_iInf]
    intro W hW w hdescent
    let : IsGalois W := hW
    rw [galoisObjectQuotientMonoidHom_ker, MulAction.mem_stabilizer_iff]
    obtain ⟨Z, ⟨e⟩⟩ := hdescent
    let z : F'.obj (H.obj Z) := F'.map e.inv w
    have hz : g • z = z := by
      have hm : g ∈ (MulAction.stabilizer (Aut F) ((t.app Z).hom z)).comap
          (autHomOfCompIso H t).toMonoidHom := by
        change (fundamentalGroupHom j ξ g) • ((t.app Z).hom z) = (t.app Z).hom z
        have hfg : fundamentalGroupHom j ξ g = 1 := MonoidHom.mem_ker.mp hg
        rw [hfg, one_smul]
      rw [← stabilizer_transportedPointOfCompIso H t] at hm
      have hp : transportedPointOfCompIso H t Z ((t.app Z).hom z) = z := by
        change (t.app Z).inv ((t.app Z).hom z) = z
        exact FintypeCat.hom_inv_id_apply (t.app Z) z
      rw [hp] at hm
      exact MulAction.mem_stabilizer_iff.mp hm
    apply (ConcreteCategory.bijective_of_isIso (F'.map e.inv)).injective
    exact (mulAction_naturality F' g e.inv w).symm.trans hz
  · intro g hg
    apply MonoidHom.mem_ker.mpr
    apply Iso.ext
    apply natTrans_ext_of_isGalois F
    intro Z hZ
    let : IsGalois Z := hZ
    let : IsConnected (H.obj Z) := hconn Z inferInstance
    let hP : IsGalois (H.obj Z) := isGalois_obj_of_connected F F' H t Z
    apply FintypeCat.hom_ext
    intro z
    have hm := Subgroup.mem_iInf.mp
      (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp
        (Subgroup.mem_iInf.mp hg (H.obj Z)) hP)
          (transportedPointOfCompIso H t Z z)) ⟨Z, ⟨Iso.refl _⟩⟩
    let : IsGalois (H.obj Z) := hP
    rw [galoisObjectQuotientMonoidHom_ker,
      stabilizer_transportedPointOfCompIso H t] at hm
    change (autHomOfCompIso H t g) • z = z at hm
    exact hm

end AlgebraicGeometry.FiniteEtale
