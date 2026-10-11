/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.PureInseparableDescent
import Nyll.EtaleFundamentalGroups.GeometricFiber.AlgebraicClosureTower
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticExact
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticMap
import Nyll.EtaleFundamentalGroups.GeometricFiber.SeparableInjectivity
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroupComposition
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence

/-!
# Arithmetic Algebraic Closure

The geometric map is injective after extension to an algebraic closure.
-/

noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.FiniteEtale

private theorem pi1_transport_injective
    {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    {xi eta : Spec (.of Ω) ⟶ X} (h : xi = eta) :
    Function.Injective (fun a : π₁ᵉᵗ(xi) ↦ h ▸ a) := by
  cases h
  exact Function.injective_id

private theorem pi1_transport_symm_cancel
    {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    {xi eta : Spec (.of Ω) ⟶ X} (h : xi = eta) (a : π₁ᵉᵗ(eta)) :
    h ▸ (h.symm ▸ a) = a := by
  cases h
  rfl

private theorem fundamentalGroupHom_eq_one_transport
    {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω]
    {xi eta : Spec (.of Ω) ⟶ X} (h : xi = eta) (a : π₁ᵉᵗ(xi)) :
    fundamentalGroupHom f eta (h ▸ a) = 1 ↔
      fundamentalGroupHom f xi a = 1 := by
  cases h
  rfl

private theorem separableClosureProjection_pullback_isEquivalence
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsAlgClosure k L]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    (pullback (separableClosureProjection k L X f)).IsEquivalence := by
  let K := separableClosure k L
  let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let ψ := Spec.map (CommRingCat.ofHom
    (AlgHom.toRingHom (IntermediateField.val (separableClosure k L))))
  let XK := Limits.pullback φK f
  let fK := Limits.pullback.fst φK f
  let q := Limits.pullback.snd ψ fK
  let e := EtaleFundamentalGroups.constantFieldTowerIso k L (separableClosure k L) X f
  let : (pullback q).IsEquivalence :=
    pullback_isEquivalence_of_purelyInseparable_constant_extension K L XK fK
  let E : FiniteEtale (Limits.pullback ψ fK) ≌
      FiniteEtale (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ e
  let : (pullback e.inv).IsEquivalence := E.isEquivalence_functor
  let : MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) e.inv :=
    ⟨fun h hf ↦ MorphismProperty.of_isPullback
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) q :=
    ⟨fun h hf ↦ MorphismProperty.of_isPullback
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩
  let : MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) e.inv := ⟨fun _ _ ↦ inferInstance⟩
  let : MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) q := ⟨fun _ _ ↦ inferInstance⟩
  let c : pullback (separableClosureProjection k L X f) ≅
      pullback q ⋙ pullback e.inv :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤) e.inv q
  exact Functor.isEquivalence_of_iso c.symm

private theorem separableClosureProjection_fundamentalGroupHom_bijective
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsAlgClosure k L]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) :
    Function.Bijective (fundamentalGroupHom (separableClosureProjection k L X f) xi) := by
  let : ConnectedSpace ↑(Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k (separableClosure k L)))) f) :=
    connectedSpace_separableClosure_of_connected_constantField k L X f
  let : (pullback (separableClosureProjection k L X f)).IsEquivalence :=
    separableClosureProjection_pullback_isEquivalence k L X f
  exact fundamentalGroupHom_bijective_of_pullback_isEquivalence
    (separableClosureProjection k L X f) xi

private theorem separableClosureProjection_fundamentalGroupHom_comparison
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) :
    let r := separableClosureProjection k L X f
    let pK := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k (separableClosure k L)))) f
    let pL := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
    ∃ hpoint : (xi ≫ r) ≫ pK = xi ≫ pL,
      ∃ c : π₁ᵉᵗ(xi ≫ pL), ∀ a : π₁ᵉᵗ(xi),
        hpoint ▸ fundamentalGroupHom pK (xi ≫ r) (fundamentalGroupHom r xi a) =
          MulAut.conj c (fundamentalGroupHom pL xi a) := by
  let r := separableClosureProjection k L X f
  let pK := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k (separableClosure k L)))) f
  let pL := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
  have hp : pL = r ≫ pK := (separableClosureProjection_comp_snd k L X f).symm
  have hpoint : (xi ≫ r) ≫ pK = xi ≫ pL := by
    rw [Category.assoc, ← hp]
  let t : pullback pL ⋙ fiber xi ≅ fiber (xi ≫ pL) :=
    pullbackCompositeFiberIsoOfEq r pK pL hp xi (xi ≫ pL) hpoint
  refine ⟨hpoint, (pullbackFiberIso pL xi).symm ≪≫ t, ?_⟩
  intro a
  rw [fundamentalGroupHom_comp_transport_eq_autHomOfCompIso r pK pL hp xi (xi ≫ pL) hpoint]
  exact fundamentalGroupHom_eq_conj_of_comparison pL xi t a

/-- The geometric map is injective after extension to an algebraic closure. -/
theorem fundamentalGroupHom_injective_of_isAlgClosure
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsAlgClosure k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) :
    Function.Injective (fundamentalGroupHom (Limits.pullback.snd _ f) xi) := by
  let : IsAlgClosed L := IsAlgClosure.isAlgClosed k
  let K := separableClosure k L
  let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let pK := Limits.pullback.snd φK f
  let pL := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
  let r := separableClosureProjection k L X f
  let : ConnectedSpace ↑(Limits.pullback φK f) :=
    connectedSpace_separableClosure_of_connected_constantField k L X f
  let : ConnectedSpace X := connectedSpace_of_connected_constantField k L f
  have hbij := separableClosureProjection_fundamentalGroupHom_bijective k L X f xi
  have hsepInj := fundamentalGroupHom_injective_of_separable_constant_extension
    k K X f (xi ≫ r)
  obtain ⟨hpoint, c, hcompare⟩ :=
    separableClosureProjection_fundamentalGroupHom_comparison k L X f xi
  intro a b hab
  apply hbij.1
  apply hsepInj
  apply pi1_transport_injective hpoint
  change hpoint ▸ fundamentalGroupHom pK (xi ≫ r) (fundamentalGroupHom r xi a) =
    hpoint ▸ fundamentalGroupHom pK (xi ≫ r) (fundamentalGroupHom r xi b)
  exact (hcompare a).trans ((congrArg (MulAut.conj c) hab).trans (hcompare b).symm)

/-- Over an algebraic closure, the native field fundamental-group map has
kernel equal to the image of the geometric fundamental group. -/
theorem fundamentalGroupHom_constantField_ker_eq_range_of_isAlgClosure
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsAlgClosure k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) :
    (fundamentalGroupHom f (xi ≫ Limits.pullback.snd _ f)).toMonoidHom.ker =
      (fundamentalGroupHom (Limits.pullback.snd _ f) xi).toMonoidHom.range := by
  let : IsAlgClosed L := IsAlgClosure.isAlgClosed k
  let K := separableClosure k L
  let : IsSepClosed K := IsSepClosure.sep_closed k
  let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let pK := Limits.pullback.snd φK f
  let pL := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
  let r := separableClosureProjection k L X f
  let : ConnectedSpace ↑(Limits.pullback φK f) :=
    connectedSpace_separableClosure_of_connected_constantField k L X f
  have hbij := separableClosureProjection_fundamentalGroupHom_bijective k L X f xi
  have hsepKer := fundamentalGroupHom_constantField_ker_eq_range k K f (xi ≫ r)
  obtain ⟨hpoint, c, hcompare⟩ :=
    separableClosureProjection_fundamentalGroupHom_comparison k L X f xi
  apply le_antisymm
  · intro b hb
    have hb' : fundamentalGroupHom f (xi ≫ pL) (MulAut.conj c b) = 1 := by
      change fundamentalGroupHom f (xi ≫ pL) b = 1 at hb
      rw [MulAut.conj_apply, map_mul, map_mul, hb, mul_one, map_inv, mul_inv_cancel]
    let z : π₁ᵉᵗ((xi ≫ r) ≫ pK) := hpoint.symm ▸ MulAut.conj c b
    have hz : z ∈ (fundamentalGroupHom f ((xi ≫ r) ≫ pK)).toMonoidHom.ker :=
      (fundamentalGroupHom_eq_one_transport f hpoint.symm (MulAut.conj c b)).2 hb'
    rw [hsepKer] at hz
    obtain ⟨d, hd⟩ := hz
    obtain ⟨a, ha⟩ := hbij.2 d
    refine ⟨a, ?_⟩
    apply (MulAut.conj c).injective
    change MulAut.conj c (fundamentalGroupHom pL xi a) = MulAut.conj c b
    have hd' : fundamentalGroupHom pK (xi ≫ r) d = z := hd
    have hstep : hpoint ▸ fundamentalGroupHom pK (xi ≫ r) (fundamentalGroupHom r xi a) =
        MulAut.conj c b := by
      rw [ha, hd']
      exact pi1_transport_symm_cancel hpoint (MulAut.conj c b)
    exact (hcompare a).symm.trans hstep
  · intro b hb
    obtain ⟨a, rfl⟩ := hb
    have hcomp := fundamentalGroupHom_constantField_comp_eq_one k L f xi
    exact congrArg (fun h ↦ h a) hcomp

/-- The arithmetic short exact sequence for a connected algebraic constant
extension of a quasi-compact, quasi-separated scheme (Stacks Project, Tag 0BTX).
The absolute Galois group is represented using the canonical separable closure. -/
@[stacks 0BTX]
theorem arithmetic_exactSequence_of_isAlgClosure
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsAlgClosure k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) :
    let geometric := fundamentalGroupHom (Limits.pullback.snd _ f) xi
    let arithmetic := arithmeticFundamentalGroupHom k (SeparableClosure k) f
      (xi ≫ Limits.pullback.snd _ f)
    Function.Injective geometric ∧ Function.Surjective arithmetic ∧
      arithmetic.toMonoidHom.ker = geometric.toMonoidHom.range := by
  let : IsAlgClosed L := IsAlgClosure.isAlgClosed k
  refine ⟨fundamentalGroupHom_injective_of_isAlgClosure k L X f xi,
    arithmeticFundamentalGroupHom_surjective_of_connected_constantField
      k (SeparableClosure k) L f (xi ≫ Limits.pullback.snd _ f), ?_⟩
  exact (arithmeticFundamentalGroupHom_ker k (SeparableClosure k) f
    (xi ≫ Limits.pullback.snd _ f)).trans
      (fundamentalGroupHom_constantField_ker_eq_range_of_isAlgClosure k L X f xi)

end AlgebraicGeometry.FiniteEtale
