/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.H1Character
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteCharacterSheaf
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteAbelianConstants
import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionPullback
import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionMonodromyEvaluation

/-!
# Every finite continuous character is an actual étale H¹ class

A character gives a finite triangular representation on `A × End(A)`.
Its descended short exact sequence is pulled back along the constant map
`ℤ → End(A)` sending `1` to the identity. Evaluation in the actual middle
stalk recovers the original character. Only connectedness and a geometric
point of the scheme are required.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped FintypeCatDiscrete

universe u

namespace EtaleFundamentalGroups.Cohomology

/-- For finite constant abelian coefficients, every continuous character of
the actual étale fundamental group comes from the existing derived H¹. -/
theorem h1Character_surjective {X : Scheme.{u}} [ConnectedSpace X]
    (A : AddCommGrpCat.{u}) [Finite A]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X) :
    Function.Surjective (h1Character A ξ) := by
  intro χ
  let : Fintype A := Fintype.ofFinite A
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  let χ₀ : Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative A := χ
  let : DistribMulAction (Aut (FiniteEtale.fiber ξ)) A :=
    trivialAdditiveAction (Aut (FiniteEtale.fiber ξ)) A
  have : ContinuousSMul (Aut (FiniteEtale.fiber ξ)) A := ⟨continuous_snd⟩
  have : Finite (A →+ A) := Finite.of_injective
    (fun f : A →+ A => (f : A → A)) DFunLike.coe_injective
  let : Fintype (A →+ A) := Fintype.ofFinite _
  let : TopologicalSpace (A →+ A) := ⊥
  have : DiscreteTopology (A →+ A) := ⟨rfl⟩
  let : DistribMulAction (Aut (FiniteEtale.fiber ξ)) (A →+ A) :=
    trivialAdditiveAction (Aut (FiniteEtale.fiber ξ)) (A →+ A)
  have : ContinuousSMul (Aut (FiniteEtale.fiber ξ)) (A →+ A) := ⟨continuous_snd⟩
  let : TopologicalSpace (A × (A →+ A)) := ⊥
  have : DiscreteTopology (A × (A →+ A)) := ⟨rfl⟩
  let action : DistribMulAction (Aut (FiniteEtale.fiber ξ)) (A × (A →+ A)) :=
    characterExtensionAction χ₀
  let : SMul (Aut (FiniteEtale.fiber ξ)) (A × (A →+ A)) := action.toSMul
  have : ContinuousSMul (Aut (FiniteEtale.fiber ξ)) (A × (A →+ A)) :=
    characterExtensionAction_continuous χ₀
  let α := AddMonoidHom.inl A (A →+ A)
  let β := AddMonoidHom.snd A (A →+ A)
  have hα (g : Aut (FiniteEtale.fiber ξ)) (a : A) : α (g • a) = g • α a :=
    (characterExtensionAction_inclusion χ₀ g a).symm
  have hβ (g : Aut (FiniteEtale.fiber ξ)) (a : A × (A →+ A)) :
      β (g • a) = g • β a := rfl
  let S := ShortComplex.mk (finiteAbelianMonodromySheafMap ξ A (A × (A →+ A)) α hα)
    (finiteAbelianMonodromySheafMap ξ (A × (A →+ A)) (A →+ A) β hβ)
    (finiteAbelianMonodromySheafMap_comp_zero ξ A (A × (A →+ A)) (A →+ A)
      α β hα hβ (characterExtension_inclusion_projection_zero A))
  have hS : S.ShortExact := finiteAbelianMonodromyComplex_shortExact
    ξ A (A × (A →+ A)) (A →+ A) α β hα hβ
    (characterExtension_inclusion_projection_zero A)
    (characterExtension_inclusion_projection_shortExact A)
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let eA := finiteAbelianConstantSheafIso ξ A (fun _ _ => rfl)
  let eQ := finiteAbelianConstantSheafIso ξ (A →+ A) (fun _ _ => rfl)
  let unitEnd : ULift.{u} ℤ →+ (A →+ A) :=
    { toFun := fun n => n.down • AddMonoidHom.id A
      map_zero' := zero_zsmul _
      map_add' := fun m n => add_zsmul _ _ _ }
  let γ := C.map (AddCommGrpCat.ofHom unitEnd) ≫ eQ.hom
  let P := coefficientPullbackExtension S eA γ
  have hP : P.ShortExact := coefficientPullbackExtension_shortExact S eA γ hS
  refine ⟨hP.extClass, ?_⟩
  rw [h1Character_extClass A ξ P.f P.g P.zero hP]
  let t := integerUnitSection X
  let Φ := Scheme.pointSmallEtale ξ
  let v := extensionMonodromyEvaluation A P.f P.g P.zero hP t ξ
  let f : P.X₂ ⟶ S.X₂ := pullback.fst S.g γ
  let e := finiteAbelianMonodromyStalkAddEquiv ξ (A × (A →+ A))
  let e0 := finiteAbelianMonodromyStalkAddEquiv ξ A
  let e1 := finiteAbelianMonodromyStalkAddEquiv ξ (A →+ A)
  let c0 := constantAbelianStalkIso ξ A
  let F := fun q => e (Φ.sheafFiber.map f (v q))
  let T := extensionMonodromyTorsor A P.f P.g P.zero hP t ξ
  have htrans (a : Multiplicative A)
      (q : (extensionMonodromy A P.f P.g P.zero hP t ξ).obj.V) :
      F (a • q) = (a.toAdd, 0) + F q := by
    have hv := extensionMonodromyEvaluation_translation A P.f P.g P.zero hP t ξ a q
    have hi : Φ.sheafFiber.map P.f ≫ Φ.sheafFiber.map f =
        Φ.sheafFiber.map eA.hom ≫ Φ.sheafFiber.map S.f :=
      (Φ.sheafFiber.map_comp P.f f).symm.trans
        ((congrArg (fun k => Φ.sheafFiber.map k)
          (coefficientPullbackExtension_f_fst S eA γ)).trans
            (Φ.sheafFiber.map_comp eA.hom S.f))
    have hi' := ConcreteCategory.congr_hom hi (c0.inv a.toAdd)
    have he0 : e0 (Φ.sheafFiber.map eA.hom (c0.inv a.toAdd)) = a.toAdd :=
      (finiteAbelianConstantSheafMap_stalk ξ A (fun _ _ => rfl)
        (c0.inv a.toAdd)).trans (c0.inv_hom_id_apply a.toAdd)
    have hin : e (Φ.sheafFiber.map f (Φ.sheafFiber.map P.f (c0.inv a.toAdd))) =
        (a.toAdd, 0) :=
      (congrArg e hi').trans
        ((finiteAbelianMonodromyStalkEquiv_map ξ A (A × (A →+ A)) α hα
          (Φ.sheafFiber.map eA.hom (c0.inv a.toAdd))).trans (congrArg α he0))
    change e (Φ.sheafFiber.map f (v (a • q))) = _
    exact (congrArg (fun x => e (Φ.sheafFiber.map f x)) hv).trans
      ((congrArg e ((Φ.sheafFiber.map f).hom.map_add _ _)).trans
        ((e.map_add _ _).trans (congrArg (· + F q) hin)))
  have hproj (q : (extensionMonodromy A P.f P.g P.zero hP t ξ).obj.V) :
      (F q).2 = AddMonoidHom.id A := by
    obtain ⟨U, x, a, hva, hpa⟩ :=
      extensionMonodromyEvaluation_exists_germ A P.f P.g P.zero hP t ξ q
    have hb := finiteAbelianMonodromyStalkEquiv_map
      ξ (A × (A →+ A)) (A →+ A) β hβ (Φ.sheafFiber.map f (v q))
    have hp : Φ.sheafFiber.map f ≫ Φ.sheafFiber.map S.g =
        Φ.sheafFiber.map P.g ≫ Φ.sheafFiber.map γ :=
      (Φ.sheafFiber.map_comp f S.g).symm.trans
        ((congrArg (fun k => Φ.sheafFiber.map k)
          (show f ≫ S.g = P.g ≫ γ from pullback.condition)).trans
            (Φ.sheafFiber.map_comp P.g γ))
    have hp' := ConcreteCategory.congr_hom hp (v q)
    have hvp : Φ.sheafFiber.map P.g (v q) =
        Φ.toPresheafFiber U x (C.obj (AddCommGrpCat.of (ULift.{u} ℤ))).obj
          (t.app (op U) PUnit.unit) :=
      (congrArg (Φ.sheafFiber.map P.g) hva).trans
        ((Φ.toPresheafFiber_naturality_apply P.g.hom U x a).trans
          (congrArg (Φ.toPresheafFiber U x P.X₃.obj) hpa))
    let z := Φ.sheafFiber.map (C.map (AddCommGrpCat.ofHom unitEnd))
      (Φ.sheafFiber.map P.g (v q))
    have hz : z = Φ.toPresheafFiber U x (C.obj (AddCommGrpCat.of (A →+ A))).obj
        ((toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (A →+ A)))).app (op U)
            (AddMonoidHom.id A)) := by
      have hn := Φ.toPresheafFiber_naturality_apply
        (C.map (AddCommGrpCat.ofHom unitEnd)).hom U x (t.app (op U) PUnit.unit)
      have hu := constantAbelianUnit_naturality (AddCommGrpCat.ofHom unitEnd)
        (op U) (ULift.up 1)
      have hunitEnd : unitEnd (ULift.up 1) = AddMonoidHom.id A := one_zsmul _
      exact (congrArg (Φ.sheafFiber.map (C.map (AddCommGrpCat.ofHom unitEnd))) hvp).trans
        (hn.trans (congrArg
          (Φ.toPresheafFiber U x (C.obj (AddCommGrpCat.of (A →+ A))).obj)
          (hu.trans (congrArg
            ((toSheafify X.smallEtaleTopology
              ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (A →+ A)))).app (op U)) hunitEnd))))
    have hend : e1 (Φ.sheafFiber.map γ (Φ.sheafFiber.map P.g (v q))) =
        AddMonoidHom.id A := by
      have hc := finiteAbelianConstantSheafMap_stalk ξ (A →+ A) (fun _ _ => rfl) z
      have hu := ConcreteCategory.congr_hom
        (constantAbelianStalkIso_unit ξ (AddCommGrpCat.of (A →+ A)) U x)
        (AddMonoidHom.id A)
      have hγ := ConcreteCategory.congr_hom (Φ.sheafFiber.map_comp
        (C.map (AddCommGrpCat.ofHom unitEnd)) eQ.hom) (Φ.sheafFiber.map P.g (v q))
      exact (congrArg e1 hγ).trans
        (hc.trans ((congrArg
          ((constantAbelianStalkIso ξ (AddCommGrpCat.of (A →+ A))).hom) hz).trans hu))
    exact hb.symm.trans ((congrArg e1 hp').trans hend)
  apply ContinuousMonoidHom.ext
  intro g
  let q := Classical.choice T.nonempty
  let d : Multiplicative A := (g • q) /ₛ q
  have hg := extensionMonodromyEvaluation_smul
    A P.f P.g P.zero hP t ξ (A × (A →+ A)) f g q
  have hd := congrArg F (sdiv_smul (g • q) q)
  have hv := congrArg Prod.fst ((htrans d q).symm.trans (hd.trans hg))
  change d.toAdd + (F q).1 = (F q).1 + (F q).2 (χ g).toAdd at hv
  rw [hproj, AddMonoidHom.id_apply] at hv
  have heq : d.toAdd = (χ g).toAdd := add_right_cancel (hv.trans (add_comm _ _))
  change d = χ g
  exact congrArg Multiplicative.ofAdd heq

end EtaleFundamentalGroups.Cohomology
