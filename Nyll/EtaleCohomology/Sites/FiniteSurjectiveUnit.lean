/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
import Nyll.EtaleCohomology.Sites.PushforwardStalkComparison
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Nyll.SchemeTheory.Etale.FiniteGeometricPoints
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Conservative
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Injectivity of the actual unit for a finite surjection

Choose algebraically closed residue-field points on the target. Surjectivity
and finiteness supply a lift of each of these points using the same field.
The unit followed by its concrete stalk component is an isomorphism, so the
unit is injective on every stalk of this conservative family.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

/-- The inverse-image/direct-image unit for a finite surjection is a
monomorphism for every étale module sheaf. -/
theorem etaleFiniteSurjective_unit_mono
    {X Y : Scheme.{u}} (q : Y ⟶ X) [IsFinite q] [Surjective q]
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Mono ((etalePullbackPushforwardAdjunction q Λ).unit.app F) := by
  let Ω : X → Type u := fun x => AlgebraicClosure (X.residueField x)
  let t : ∀ x : X, Spec (CommRingCat.of (Ω x)) ⟶ X := fun x =>
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (Ω x))) ≫
      X.fromSpecResidueField x
  have ht (x : X) : t x default = x := by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply x _
  have hcover : ⋃ x : X, Set.range (t x) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, default, ht x⟩
  have hpoints := Scheme.isConservative_pointSmallEtale t hcover
  apply ((hpoints.jointlyReflectMonomorphisms (ModuleCat.{u} Λ)).mono_iff _).mpr
  rintro ⟨_, ⟨x⟩⟩
  obtain ⟨y, hy⟩ := q.surjective (t x default)
  obtain ⟨s, hs, _⟩ := q.exists_geometricLift_of_isFinite (t x) y hy
  change Mono ((Scheme.pointSmallEtale (t x)).sheafFiber.map
    ((etalePullbackPushforwardAdjunction q Λ).unit.app F))
  rw [← hs]
  let a := (Scheme.pointSmallEtale (s ≫ q)).sheafFiber.map
    ((etalePullbackPushforwardAdjunction q Λ).unit.app F)
  let b := etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩
    ((etalePullback q Λ).obj F)
  have hab : IsIso (a ≫ b) := etalePullbackUnit_stalkComponent_isIso q s Λ F
  apply (ModuleCat.mono_iff_injective a).mpr
  intro v w hvw
  apply (ModuleCat.mono_iff_injective (a ≫ b)).mp inferInstance
  exact congrArg b hvw

end EtaleCohomology
