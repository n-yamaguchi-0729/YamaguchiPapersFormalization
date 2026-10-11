/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticSurjective

/-!
# Arithmetic Connected

Connectedness after a separably closed constant extension descends to the base.
-/

noncomputable section
universe u
open CategoryTheory Limits CategoryTheory.PreGaloisCategory
namespace AlgebraicGeometry.FiniteEtale

/-- Connectedness after a separably closed constant extension descends to the base. -/
theorem connectedSpace_of_connected_constantField
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)] :
    ConnectedSpace X := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let : Surjective φ := ⟨fun y ↦ ⟨Classical.choice (inferInstance : Nonempty (Spec (.of L))),
    Subsingleton.elim _ _⟩⟩
  exact (Limits.pullback.snd φ f).surjective.connectedSpace (Limits.pullback.snd φ f).continuous

/-- A connected finite étale cover of the field stays connected over a scheme
whose extension to a separably closed constant field is connected. -/
theorem isConnected_pullback_of_connected_constantField
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsSepClosed L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    (W : FiniteEtale (Spec (.of k))) [IsConnected W] :
    IsConnected ((pullback f).obj W) := by
  let : ConnectedSpace X := connectedSpace_of_connected_constantField k L f
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let : Field Γ(W.left, ⊤) := (isField_of_isConnected k W).toField
  let : Subsingleton W.left := ⟨fun x y ↦ by
    apply W.left.isoSpec.hom.homeomorph.injective
    have : Subsingleton (Spec Γ(W.left, ⊤)) := by
      change Subsingleton (PrimeSpectrum Γ(W.left, ⊤))
      infer_instance
    exact Subsingleton.elim _ _⟩
  have hz : Nonempty ((fiber φ).obj W) :=
    (not_initial_iff_fiber_nonempty (fiber φ) W).mp IsConnected.notInitial
  let z : Over.mk φ ⟶ W.toComma := fiberObjEquivHom φ W hz.some
  let s : Spec (.of L) ⟶ W.left := z.left
  have hs : s ≫ W.hom = φ := z.w
  let : Surjective s := ⟨fun y ↦ ⟨Classical.choice (inferInstance : Nonempty (Spec (.of L))),
    Subsingleton.elim _ _⟩⟩
  let q := Limits.pullback.fst φ f
  let p := Limits.pullback.snd φ f
  let m : Limits.pullback φ f ⟶ Limits.pullback W.hom f :=
    Limits.pullback.lift (q ≫ s) p (by rw [Category.assoc, hs]; exact Limits.pullback.condition)
  have hm : IsPullback q m s (Limits.pullback.fst W.hom f) := by
    refine IsPullback.of_bot ?_ (Limits.pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback W.hom f)
    dsimp [m]
    rw [Limits.pullback.lift_snd, hs]
    exact IsPullback.of_hasPullback φ f
  let : Surjective m := MorphismProperty.of_isPullback (P := @Surjective) hm inferInstance
  let : ConnectedSpace ((pullback f).obj W).left :=
    m.surjective.connectedSpace m.continuous
  exact isConnected_of_connectedSpace_left ((pullback f).obj W)

/-- The arithmetic fundamental-group map is surjective under exactly the
geometric connectedness test needed for the arithmetic exact sequence. -/
theorem fundamentalGroupHom_surjective_of_connected_constantField
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsSepClosed L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    Function.Surjective (fundamentalGroupHom f xi) := by
  let : ConnectedSpace X := connectedSpace_of_connected_constantField k L f
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) (pullback f) :=
    pullback_preservesLimitsOfShape_pempty f
  change Function.Surjective (autHomOfCompIso (pullback f) (pullbackFiberIso f xi))
  apply ((autHomOfCompIso_surjective_tfae (fiber (xi ≫ f)) (fiber xi) (pullback f)
    (pullbackFiberIso f xi)).out 3 1).mp
  intro W hW
  let : IsConnected W := hW
  exact isConnected_pullback_of_connected_constantField k L f W

end AlgebraicGeometry.FiniteEtale
