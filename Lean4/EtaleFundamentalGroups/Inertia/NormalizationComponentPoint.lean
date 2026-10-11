/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NormalizationComponent
import EtaleFundamentalGroups.GaloisCovers.PullbackComponent
import SchemeTheory.FiniteEtale.Forget.FiniteCoproducts
import Mathlib.CategoryTheory.Galois.Decomposition
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Topology.Basic

/-!
# A normalized geometric point lies in an actual cover component

The finite connected decomposition of the original cover has clopen images
in its normalization. Their union contains the dense image of the cover and
is closed, so it covers the normalization. The open-immersion lifting
property then factors an actual geometric-point morphism through one of
these normalized components.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

variable {U S : Scheme.{u}} [ConnectedSpace U]

/-- Every geometric point of the relative normalization lies in the
normalization of a connected finite-etale component of the original cover. -/
theorem exists_normalizationComponent_geometricPoint
    (W : FiniteEtale U)
    (f : W.left ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Omega : Type u} [Field Omega]
    (z : Spec (.of Omega) ⟶ f.normalization) :
    ∃ (Z : FiniteEtale U) (i : Z ⟶ W)
      (q : Spec (.of Omega) ⟶ (i.left ≫ f).normalization),
      Mono i ∧ IsConnected Z ∧ q ≫ normalizationComponentInclusion f i = z := by
  obtain ⟨ι, Z, i, hcol, hconnected, hfinite⟩ := has_decomp_connected_components W
  let : Finite ι := hfinite
  have hmono (j : ι) : Mono (i j) :=
    MonoCoprod.mono_inj _ (Cofan.mk W i) hcol j
  let F := (FiniteEtale.forget U ⋙ Over.forget U) ⋙ Scheme.forgetToTop
  have htop := isColimitOfPreserves F hcol
  have hcover (w : W.left) : ∃ (j : ι) (v : (Z j).left), (i j).left v = w := by
    obtain ⟨⟨j⟩, v, hv⟩ := Concrete.isColimit_exists_rep
      (Discrete.functor Z ⋙ F) htop w
    exact ⟨j, v, hv⟩
  let A : Set f.normalization := ⋃ j : ι, Set.range (normalizationComponentInclusion f (i j))
  have hclosed : IsClosed A := by
    apply isClosed_iUnion_of_finite
    intro j
    let : Mono (i j) := hmono j
    exact (isClopen_range_normalizationComponentInclusion f (i j)).1
  have hrange : Set.range f.toNormalization ⊆ A := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨j, v, rfl⟩ := hcover w
    apply Set.mem_iUnion.mpr
    refine ⟨j, ((i j).left ≫ f).toNormalization v, ?_⟩
    exact congrArg (fun k : (Z j).left ⟶ f.normalization => k v)
      (toNormalization_normalizationComponentInclusion f (i j))
  have hall : Set.univ ⊆ A := by
    rw [← f.toNormalization.denseRange.closure_range]
    exact closure_minimal hrange hclosed
  let omega : Spec (.of Omega) := Classical.choice inferInstance
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hall (Set.mem_univ (z omega)))
  let : Mono (i j) := hmono j
  have hzrange : Set.range z ⊆ Set.range (normalizationComponentInclusion f (i j)) := by
    rintro _ ⟨a, rfl⟩
    have ha : a = omega := Subsingleton.elim a omega
    rw [ha]
    exact hj
  let q := IsOpenImmersion.lift (normalizationComponentInclusion f (i j)) z hzrange
  exact ⟨Z j, i j, q, hmono j, hconnected j,
    IsOpenImmersion.lift_fac (normalizationComponentInclusion f (i j)) z hzrange⟩

/-- For a pulled-back Galois cover, the component selected by an arbitrary
normalization point is itself Galois and can be pointed over any fixed
geometric base point. -/
theorem exists_galoisNormalizationComponent_geometricPoint
    {Y : Scheme.{u}} [ConnectedSpace Y]
    (b : U ⟶ Y) {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ U)
    (W : FiniteEtale Y) (hW : IsGalois W)
    (f : ((FiniteEtale.pullback b).obj W).left ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    {Omega' : Type u} [Field Omega']
    (q : Spec (.of Omega') ⟶ f.normalization) :
    ∃ (Z : FiniteEtale U) (i : Z ⟶ (FiniteEtale.pullback b).obj W)
      (qZ : Spec (.of Omega') ⟶ (i.left ≫ f).normalization)
      (z : (FiniteEtale.fiber xi).obj Z)
      (w : (FiniteEtale.fiber (xi ≫ b)).obj W),
      Mono i ∧ IsGalois Z ∧
        qZ ≫ normalizationComponentInclusion f i = q ∧
        (FiniteEtale.fiber xi).map i z =
          transportedPointOfCompIso (FiniteEtale.pullback b)
            (FiniteEtale.pullbackFiberIso b xi) W w := by
  obtain ⟨Z, i, qZ, hi, hZconnected, hqZ⟩ :=
    exists_normalizationComponent_geometricPoint ((FiniteEtale.pullback b).obj W) f q
  let : Mono i := hi
  let : IsConnected Z := hZconnected
  let F := FiniteEtale.fiber xi
  let z : F.obj Z := Classical.choice (nonempty_fiber_of_isConnected F Z)
  let w := (FiniteEtale.pullbackFiberIso b xi).hom.app W (F.map i z)
  have hiz : F.map i z =
      transportedPointOfCompIso (FiniteEtale.pullback b)
        (FiniteEtale.pullbackFiberIso b xi) W w :=
    (FintypeCat.hom_inv_id_apply ((FiniteEtale.pullbackFiberIso b xi).app W)
      (F.map i z)).symm
  obtain ⟨Z', i', z', hiz', hZ', hi'⟩ :=
    FiniteEtale.exists_galoisComponent_pullback b xi W hW w
  let : IsGalois Z' := hZ'
  let : Mono i' := hi'
  obtain ⟨e, _he⟩ := connected_component_unique F z' z i' i (hiz'.trans hiz.symm)
  have hZGalois : IsGalois Z := by
    apply (isGalois_iff_pretransitive F Z).mpr
    constructor
    intro a c
    obtain ⟨sigma, hsigma⟩ := evaluation_aut_surjective_of_isGalois F Z'
      (F.map e.inv a) (F.map e.inv c)
    refine ⟨e.symm ≪≫ sigma ≪≫ e, ?_⟩
    change F.map ((e.inv ≫ sigma.hom) ≫ e.hom) a = c
    simp only [Functor.map_comp, FintypeCat.comp_apply]
    exact (congrArg (fun v : F.obj Z' => F.map e.hom v) hsigma).trans
      (FintypeCat.inv_hom_id_apply (F.mapIso e) c)
  exact ⟨Z, i, qZ, z, w, hi, hZGalois, hqZ, hiz⟩

end EtaleFundamentalGroups.Inertia
