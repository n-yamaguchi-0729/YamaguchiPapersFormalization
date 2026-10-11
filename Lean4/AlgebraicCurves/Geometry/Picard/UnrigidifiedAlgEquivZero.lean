/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
The fibre-pullback calculation is adapted from:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Copyright (c) 2026 Naganori Yamaguchi.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of the unrigidified construction: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import AlgebraicCurves.Geometry.Picard.Unrigidified
import AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import SchemeTheory.Modules.Monoidal
import SchemeTheory.Modules.PullbackMonoidal

/-!
# The unrigidified degree-zero Picard presheaf

The geometric-fibre condition is invariant under tensoring with a base line bundle.
It therefore defines an actual subfunctor of relative classes. At a chosen section,
normalization identifies this subfunctor with the existing pointed Picard-zero functor.
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry NeronModelInfra

noncomputable section

namespace AlgebraicGeometry.RelPicard.Unrigidified

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}

/-- Algebraic equivalence to zero on all geometric fibres, without a rigidifying section. -/
def FibrewiseZero {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : LineBundle c t) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
    IsAlgEquivZero (fibreAt c t s)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj M.1)

theorem fibrewiseZero_baseTwist_iff {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {M N : LineBundle c t} (h : BaseTwist c t M N) : FibrewiseZero M ↔ FibrewiseZero N := by
  obtain ⟨Q, hQ, ⟨e⟩⟩ := h
  have hFibre : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      Nonempty ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj N.1 ≅
        (Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj M.1) := by
    intro k _ s
    obtain ⟨q⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k
      ((Scheme.Modules.pullback s).obj Q) (hQ.pullback s)
    let φ : pullback (pullback.snd c t) s ⟶ pullback c t := pullback.fst (pullback.snd c t) s
    have hQf : (Scheme.Modules.pullback φ).obj
        ((Scheme.Modules.pullback (pullback.snd c t)).obj Q) ≅ 𝟙_ _ :=
      (Scheme.Modules.pullbackComp _ _).app Q ≪≫
        (Scheme.Modules.pullbackCongr
          (pullback.condition (f := pullback.snd c t) (g := s))).app Q ≪≫
        ((Scheme.Modules.pullbackComp _ _).app Q).symm ≪≫
        (Scheme.Modules.pullback (fibreAt c t s)).mapIso q ≪≫
        Scheme.Modules.pullbackUnitIso (fibreAt c t s)
    exact ⟨(Scheme.Modules.pullback φ).mapIso e ≪≫
      Scheme.Modules.pullbackTensorObjIso φ
        ((Scheme.Modules.pullback (pullback.snd c t)).obj Q) M.1 ≪≫
      (hQf ⊗ᵢ Iso.refl _) ≪≫ λ_ _⟩
  constructor
  · intro hM k _ _ s
    exact (hM k s).of_iso (hFibre k s).some.symm
  · intro hN k _ _ s
    exact (hN k s).of_iso (hFibre k s).some

theorem fibrewiseZero_pullback {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t)
    {M : LineBundle c t} (hM : FibrewiseZero M) : FibrewiseZero (pullbackAlong ψ M) := by
  intro k _ _ s
  have hψ : pullback.snd c t' ≫ ψ.1 = baseChangeSnd c ψ ≫ pullback.snd c t :=
    (baseChangeSnd_snd ψ).symm
  let e : pullback (pullback.snd c t') s ⟶ pullback (pullback.snd c t) (s ≫ ψ.1) :=
    pullback.map _ _ _ _ (baseChangeSnd c ψ) (𝟙 _) ψ.1 hψ
      (by rw [Category.id_comp])
  have he : e ≫ fibreAt c t (s ≫ ψ.1) = fibreAt c t' s := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) (s ≫ ψ.1) =
      pullback.fst (pullback.snd c t') s ≫ baseChangeSnd c ψ :=
    pullback.lift_fst _ _ _
  refine IsAlgEquivZero.of_iso ?_ ((hM k (s ≫ ψ.1)).pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app M.1 ≪≫
    (Scheme.Modules.pullbackCongr hfst).app M.1 ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.1).symm

/-- The fibrewise zero condition descends to actual relative classes. -/
def classesZero {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Classes c t → Prop :=
  Quot.lift FibrewiseZero (fun _ _ h => propext (fibrewiseZero_baseTwist_iff h))

theorem classesZero_map {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t)
    (x : Classes c t) (hx : classesZero t x) : classesZero t' (classesMap ψ x) := by
  induction x using Quot.ind with
  | _ M => exact fibrewiseZero_pullback ψ hx

/-- The actual subfunctor of fibrewise algebraically trivial relative classes. -/
def zeroSubfunctor (c : C ⟶ Spec (CommRingCat.of R)) : Subfunctor (presheaf c) where
  obj X := {x | classesZero X.unop.hom x}
  map φ := fun x hx => classesZero_map ⟨φ.unop.left, Over.w φ.unop⟩ x hx

/-- The unrigidified Picard-zero presheaf. -/
def zeroPresheaf (c : C ⟶ Spec (CommRingCat.of R)) :
    (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1) :=
  (zeroSubfunctor c).toFunctor

theorem normalize_zero_iff
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : Classes c t) :
    classesZero t x ↔ (algEquivZeroCut c ε).onClasses t (normalize ε t x) := by
  induction x using Quot.ind with
  | _ M =>
    exact fibrewiseZero_baseTwist_iff (M := M)
      (N := ⟨(RigidifiedLineBundle.ofInvertible (ε := ε) M.1 M.2).L,
        (RigidifiedLineBundle.ofInvertible (ε := ε) M.1 M.2).isInvertible⟩)
      ⟨rigCorrection ε t M.1, (M.2.pullback (rigSection c t ε)).dual.1,
        ⟨β_ M.1 ((Scheme.Modules.pullback (pullback.snd c t)).obj (rigCorrection ε t M.1))⟩⟩

/-- Normalization restricts to the fibrewise-zero classes. -/
def zeroClassesEquiv (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    {x : Classes c t // classesZero t x} ≃
      {x : RigidifiedLineBundle.Classes c ε t // (algEquivZeroCut c ε).onClasses t x} where
  toFun x := ⟨classesEquiv ε t x.1, (normalize_zero_iff ε t x.1).1 x.2⟩
  invFun y := ⟨(classesEquiv ε t).symm y.1, (normalize_zero_iff ε t _).2
    (by
      change (algEquivZeroCut c ε).onClasses t
        ((classesEquiv ε t) ((classesEquiv ε t).symm y.1))
      rw [Equiv.apply_symm_apply]
      exact y.2)⟩
  left_inv x := Subtype.ext ((classesEquiv ε t).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((classesEquiv ε t).apply_symm_apply y.1)

/-- The unrigidified and pointed Picard-zero presheaves are naturally isomorphic
whenever the curve is supplied with an actual section. -/
def zeroPresheafIso (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    zeroPresheaf c ≅ relSubPicPresheaf c ε (algEquivZeroCut c ε) :=
  NatIso.ofComponents (fun X => Equiv.toIso (zeroClassesEquiv ε X.unop.hom))
    (fun {X Y} φ => by
      apply TypeCat.homEquiv.injective
      funext x
      apply Subtype.ext
      exact congrArg (fun f => f x.1) ((presheafIso ε).hom.naturality φ))

end AlgebraicGeometry.RelPicard.Unrigidified
