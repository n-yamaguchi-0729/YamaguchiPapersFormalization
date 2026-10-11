/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelSubPicGroup.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Picard.SubPicCondition
import AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import AlgebraicCurves.Geometry.Picard.RelativeGroupLawGrpObj
import AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import SchemeTheory.Modules.Monoidal
import SchemeTheory.Modules.PullbackMonoidal
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_tensor_inverse

/-!
Tensor products and the commutative-group presheaf associated with a group-stable Picard
condition.
-/

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
    AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

/-- The tensor product of rigidified line bundles, with the induced rigidification. -/
def RigidifiedLineBundle.tensor {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (L M : RigidifiedLineBundle c ε t) : RigidifiedLineBundle c ε t where
  L := L.L ⊗ M.L
  isInvertible := L.isInvertible.tensor M.isInvertible
  rigidified := ⟨(Scheme.Modules.pullbackTensorObjIso _ _ _) ≪≫ (L.rigidified.some ⊗ᵢ
    M.rigidified.some) ≪≫ λ_ _⟩

theorem RigidifiedLineBundle.tensor_congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {L L' M M' : RigidifiedLineBundle c ε t} (hL : L ≈ L') (hM : M ≈ M') : L.tensor M ≈
      L'.tensor M' :=
  ⟨Nonempty.some (hL : Nonempty (L.L ≅ L'.L)) ⊗ᵢ Nonempty.some (hM : Nonempty (M.L ≅ M'.L))⟩

theorem RigidifiedLineBundle.nonempty_tensor_pullbackAlong_iso {T T' : Scheme.{u}} {t : T ⟶ Spec
    (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) (L M : RigidifiedLineBundle c ε
      t) :
    Nonempty (((L.tensor M).pullbackAlong ψ).L ≅ ((L.pullbackAlong ψ).tensor (M.pullbackAlong
      ψ)).L) :=
  ⟨Scheme.Modules.pullbackTensorObjIso _ _ _⟩

theorem RigidifiedLineBundle.exists_tensor_iso_unit {T : Scheme.{u}} {t : T ⟶ Spec
    (CommRingCat.of R)}
    (L : RigidifiedLineBundle c ε t) :
    ∃ M : RigidifiedLineBundle c ε t, Nonempty ((L.tensor M).L ≅ (RigidifiedLineBundle.unit (c
      := c) (ε := ε) t).L) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := L.isInvertible.exists_tensor_inverse
  refine ⟨⟨N, hN, ⟨?_⟩⟩, ⟨e⟩⟩
  exact (λ_ _).symm ≪≫ (L.rigidified.some.symm ⊗ᵢ Iso.refl _) ≪≫
    (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _

/-- A Picard condition closed under tensor products and under taking tensor inverses. -/
structure SubPicGroupCondition (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) extends SubPicCondition c ε where
  /-- The tensor product of two bundles satisfying the condition also satisfies it. -/
  tensor_mem : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L M : RigidifiedLineBundle
    c ε t),
    P t L → P t M → P t (L.tensor M)
  /-- A tensor inverse of a bundle satisfying the condition also satisfies the condition. -/
  inv_mem : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L M : RigidifiedLineBundle c ε t),
    Nonempty ((L.tensor M).L ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L) → P t L → P t M

/-- Multiplication of classes in the sub-Picard presheaf, induced by tensor product. -/
def SubPicGroupCondition.mulObj (P : SubPicGroupCondition c ε) (X : (Over (Spec (CommRingCat.of
    R)))ᵒᵖ)
    (x y : (relSubPicPresheaf c ε P.toSubPicCondition).obj X) :
    (relSubPicPresheaf c ε P.toSubPicCondition).obj X :=
  ⟨Quotient.map₂ (fun L M => L.tensor M) (fun _ _ hL _ _ hM => RigidifiedLineBundle.tensor_congr
    hL hM) x.1 y.1, by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    induction x using Quotient.ind
    induction y using Quotient.ind
    exact P.tensor_mem _ _ _ hx hy⟩

/-- The unit class in the sub-Picard presheaf. -/
def SubPicGroupCondition.oneObj (P : SubPicGroupCondition c ε) (X : (Over (Spec (CommRingCat.of
    R)))ᵒᵖ) :
    (relSubPicPresheaf c ε P.toSubPicCondition).obj X :=
  ⟨relPicardPresheaf.unitClass c ε X.unop, P.unit_mem _⟩

/-- The class of a chosen tensor inverse in the sub-Picard presheaf. -/
def SubPicGroupCondition.invObj (P : SubPicGroupCondition c ε) (X : (Over (Spec (CommRingCat.of
    R)))ᵒᵖ)
    (x : (relSubPicPresheaf c ε P.toSubPicCondition).obj X) :
    (relSubPicPresheaf c ε P.toSubPicCondition).obj X :=
  ⟨Quotient.mk _ (RigidifiedLineBundle.exists_tensor_iso_unit x.1.out).choose,
    P.inv_mem _ x.1.out _ (RigidifiedLineBundle.exists_tensor_iso_unit x.1.out).choose_spec
      (by have hx := x.2; rw [← Quotient.out_eq x.1] at hx; exact hx)⟩
/-- The commutative group structure on classes supplied by the group-stable Picard condition. -/
@[reducible]
def SubPicGroupCondition.commGroupObj (P : SubPicGroupCondition c ε) (X : (Over (Spec
    (CommRingCat.of R)))ᵒᵖ) :
    CommGroup ((relSubPicPresheaf c ε P.toSubPicCondition).obj X) where
  mul := P.mulObj X
  one := P.oneObj X
  inv := P.invObj X
  mul_assoc := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    apply Subtype.ext
    induction x using Quotient.ind
    induction y using Quotient.ind
    induction z using Quotient.ind
    exact Quotient.sound ⟨α_ _ _ _⟩
  one_mul := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    induction x using Quotient.ind
    exact Quotient.sound ⟨λ_ _⟩
  mul_one := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    induction x using Quotient.ind
    exact Quotient.sound ⟨ρ_ _⟩
  mul_comm := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    apply Subtype.ext
    induction x using Quotient.ind
    induction y using Quotient.ind
    exact Quotient.sound ⟨β_ _ _⟩
  inv_mul_cancel := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    have key : ∀ (L₀ M : RigidifiedLineBundle c ε X.unop.hom),
        Nonempty ((L₀.tensor M).L ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) X.unop.hom).L) →
        Quotient.map₂ (fun L M => L.tensor M) (fun _ _ hL _ _ hM =>
          RigidifiedLineBundle.tensor_congr hL hM)
          (Quotient.mk _ M : RigidifiedLineBundle.Classes c ε X.unop.hom)
          (Quotient.mk _ L₀ : RigidifiedLineBundle.Classes c ε X.unop.hom) =
        (Quotient.mk _ (RigidifiedLineBundle.unit X.unop.hom) : RigidifiedLineBundle.Classes c ε
          X.unop.hom) :=
      fun L₀ M hM => Quotient.sound ⟨β_ _ _ ≪≫ hM.some⟩
    have h := key x.out _ (RigidifiedLineBundle.exists_tensor_iso_unit x.out).choose_spec
    change Quotient.map₂ (fun L M => L.tensor M)
      (fun _ _ hL _ _ hM => RigidifiedLineBundle.tensor_congr hL hM)
      (Quotient.mk _ (RigidifiedLineBundle.exists_tensor_iso_unit x.out).choose) x =
      Quotient.mk _ (RigidifiedLineBundle.unit X.unop.hom)
    exact (congrArg (fun q : RigidifiedLineBundle.Classes c ε X.unop.hom =>
      Quotient.map₂ (fun L M => L.tensor M)
        (fun _ _ hL _ _ hM => RigidifiedLineBundle.tensor_congr hL hM)
        (Quotient.mk _ (RigidifiedLineBundle.exists_tensor_iso_unit x.out).choose) q)
      (Quotient.out_eq x)).symm.trans h

/-- The commutative-group-valued presheaf of classes satisfying the group-stable Picard
condition.
-/
def relSubPicCommGrpPresheaf (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec
    (CommRingCat.of R))) c)
    (P : SubPicGroupCondition c ε) : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj X := @CommGrpCat.of ((relSubPicPresheaf c ε P.toSubPicCondition).obj X) (P.commGroupObj X)
  map {X X'} φ :=
    letI := P.commGroupObj X
    letI := P.commGroupObj X'
    CommGrpCat.ofHom
      { toFun := (relSubPicPresheaf c ε P.toSubPicCondition).map φ
        map_one' := by
          apply Subtype.ext
          exact Quotient.sound ⟨Scheme.Modules.pullbackUnitIso _⟩
        map_mul' := by
          rintro ⟨x, hx⟩ ⟨y, hy⟩
          apply Subtype.ext
          induction x using Quotient.ind
          induction y using Quotient.ind
          exact Quotient.sound (RigidifiedLineBundle.nonempty_tensor_pullbackAlong_iso _ _ _) }
  map_id X := by
    let := P.commGroupObj X
    refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
    change ((relSubPicPresheaf c ε P.toSubPicCondition).map (𝟙 X)) x = x
    exact ConcreteCategory.congr_hom ((relSubPicPresheaf c ε P.toSubPicCondition).map_id X) x
  map_comp {X X' X''} φ ψ := by
    let := P.commGroupObj X
    let := P.commGroupObj X'
    let := P.commGroupObj X''
    refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
    change ((relSubPicPresheaf c ε P.toSubPicCondition).map (φ ≫ ψ)) x =
      ((relSubPicPresheaf c ε P.toSubPicCondition).map ψ)
        (((relSubPicPresheaf c ε P.toSubPicCondition).map φ) x)
    exact ConcreteCategory.congr_hom ((relSubPicPresheaf c ε P.toSubPicCondition).map_comp φ ψ) x

end AlgebraicGeometry.RelPicard

end
