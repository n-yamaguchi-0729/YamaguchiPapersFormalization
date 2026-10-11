/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.GaloisCategory

/-!
# Connected finite etale covers

For a connected base scheme, categorical connectedness in the Galois
category of finite etale covers agrees with connectedness of the underlying
source scheme.  This file records both directions, together with the
nonemptiness comparison used in their proofs.

Mathlib provides the abstract Galois-category notion `IsConnected` and the
topological class `ConnectedSpace`, but currently has no finite-etale scheme
bridge between them.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X : Scheme.{u}} [ConnectedSpace X]

/-- Pulling a nonempty finite etale cover of a preconnected base back to a
nonempty scheme again has nonempty source. -/
theorem pullback_obj_nonempty {S T : Scheme.{u}} [PreconnectedSpace T]
    (f : S ⟶ T) [Nonempty S] (Y : FiniteEtale T) [Nonempty Y.left] :
    Nonempty ((pullback f).obj Y).left := by
  let : IsFiniteEtale Y.hom := Y.2
  let : PreconnectedSpace ↑((Functor.fromPUnit T).obj Y.right) := by
    change PreconnectedSpace T
    infer_instance
  let : Nonempty ((Functor.id Scheme).obj Y.left) := by
    change Nonempty Y.left
    infer_instance
  let : Surjective Y.hom := IsFiniteEtale.surjective Y.hom
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  obtain ⟨y, hy⟩ := Y.hom.surjective (f.base s)
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback y s hy
  exact ⟨z⟩

/-- A nonempty finite etale cover of a connected scheme is not initial in the
finite etale category. -/
theorem notInitial_of_nonempty_left (Y : FiniteEtale X) [Nonempty Y.left] :
    IsInitial Y → False := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  let k : Type u := X.residueField x
  let Ω : Type u := AlgebraicClosure k
  let ξ : Spec (.of Ω) ⟶ X :=
    Spec.map (CommRingCat.ofHom <| algebraMap k Ω) ≫
      X.fromSpecResidueField x
  let F := fiber ξ
  apply (not_initial_iff_fiber_nonempty F Y).mpr
  let : IsFiniteEtale Y.hom := Y.2
  let : PreconnectedSpace ↑((Functor.fromPUnit X).obj Y.right) := by
    change PreconnectedSpace X
    infer_instance
  let : Nonempty ((Functor.id Scheme).obj Y.left) := by
    change Nonempty Y.left
    infer_instance
  let : Surjective Y.hom := IsFiniteEtale.surjective Y.hom
  obtain ⟨ω⟩ := (inferInstance : Nonempty (Spec (.of Ω)))
  obtain ⟨y, hy⟩ := Y.hom.surjective (ξ.base ω)
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback y ω hy
  exact ⟨z⟩

/-- A finite etale cover that is not initial has a nonempty source scheme. -/
theorem nonempty_left_of_notInitial (Y : FiniteEtale X)
    (hY : IsInitial Y → False) : Nonempty Y.left := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  let k : Type u := X.residueField x
  let Ω : Type u := AlgebraicClosure k
  let ξ : Spec (.of Ω) ⟶ X :=
    Spec.map (CommRingCat.ofHom <| algebraMap k Ω) ≫
      X.fromSpecResidueField x
  let F := fiber ξ
  exact ((not_initial_iff_fiber_nonempty F Y).mp hY).map
    fun z ↦ fiberPt z

/-- A categorically connected finite etale cover has connected source
scheme. -/
theorem connectedSpace_left_of_isConnected (Y : FiniteEtale X)
    [IsConnected Y] : ConnectedSpace Y.left := by
  let : Nonempty Y.left :=
    nonempty_left_of_notInitial Y IsConnected.notInitial
  let y : Y.left := Classical.choice (inferInstance : Nonempty Y.left)
  let : Finite (_root_.ConnectedComponents Y.left) := inferInstance
  let cover := Y.left.connectedComponents
  let i : _root_.ConnectedComponents Y.left :=
    _root_.ConnectedComponents.mk y
  let : ConnectedSpace (cover.X i) := by
    dsimp only [cover]
    infer_instance
  let hY : IsFiniteEtale Y.hom := Y.2
  let hcomp : IsFiniteEtale (cover.f i ≫ Y.hom) := by
    let _ : IsOpenImmersion (cover.f i) := by
      dsimp only [cover, Scheme.connectedComponents]
      infer_instance
    have hComponent : IsFiniteEtale (cover.f i) :=
      @IsFiniteEtale.mk _ _ _ inferInstance inferInstance
    exact MorphismProperty.comp_mem
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) _ _ hComponent hY
  let Z : FiniteEtale X :=
    @FiniteEtale.mk _ _ (cover.f i ≫ Y.hom) hcomp
  let j : Z ⟶ Y :=
    MorphismProperty.Over.homMk (by
      simpa only [Z, FiniteEtale.mk_left] using cover.f i)
  let : Mono j := by
    apply (FiniteEtale.forget _ ⋙ Over.forget _).mono_of_mono_map
    change Mono (cover.f i)
    infer_instance
  let : Nonempty Z.left := by
    have : Nonempty (cover.X i) := by
      refine ⟨⟨y, ?_⟩⟩
      change _root_.ConnectedComponents.mk y ∈
        ({i} : Set (_root_.ConnectedComponents Y.left))
      simp [i]
    simpa only [Z, FiniteEtale.mk_left] using this
  let : IsIso j :=
    IsConnected.noTrivialComponent Z j
      (notInitial_of_nonempty_left Z)
  let hjhom : IsIso j.hom := (FiniteEtale.forget X).map_isIso j
  let : IsIso j.left :=
    @Functor.map_isIso _ _ _ _ _ _ (Over.forget X) j.hom hjhom
  let eZ : Z.left ≅ cover.X i :=
    eqToIso (by simp only [Z, FiniteEtale.mk_left])
  let : ConnectedSpace Z.left :=
    eZ.hom.homeomorph.connectedSpace_iff.mpr inferInstance
  exact (@asIso _ _ _ _ j.left inferInstance).hom.homeomorph.connectedSpace_iff.mp
    (inferInstance : ConnectedSpace Z.left)

/-- A finite etale cover with connected source scheme is categorically
connected. -/
theorem isConnected_of_connectedSpace_left (Y : FiniteEtale X)
    [ConnectedSpace Y.left] : IsConnected Y := by
  constructor
  · exact notInitial_of_nonempty_left Y
  · intro Z i _ hZ
    let : Nonempty Z.left := nonempty_left_of_notInitial Z hZ
    obtain ⟨hiOpen, hiClosed⟩ :=
      (_root_.AlgebraicGeometry.FiniteEtale.mono_iff X Z Y i).mp inferInstance
    let : IsOpenImmersion i.left := hiOpen
    let : IsClosedImmersion i.left := hiClosed
    have hRangeNonempty : (Set.range i.left.base).Nonempty := by
      obtain ⟨z⟩ := (inferInstance : Nonempty Z.left)
      exact ⟨i.left.base z, z, rfl⟩
    have hRange : Set.range i.left.base = Set.univ :=
      IsClopen.eq_univ
        ⟨i.left.isClosedEmbedding.isClosed_range,
          i.left.isOpenEmbedding.isOpen_range⟩
        hRangeNonempty
    have hOpensRange : i.left.opensRange = ⊤ := by
      rw [← SetLike.coe_injective.eq_iff]
      simpa only [Scheme.Hom.coe_opensRange,
        TopologicalSpace.Opens.coe_top] using hRange
    let : IsIso i.left :=
      isIso_of_isOpenImmersion_of_opensRange_eq_top i.left hOpensRange
    exact isIso_of_isIso_left i

end AlgebraicGeometry.FiniteEtale
