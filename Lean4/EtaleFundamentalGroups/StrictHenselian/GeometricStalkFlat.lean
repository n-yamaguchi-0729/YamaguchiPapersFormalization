/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Flat


/-!
# Flatness of the actual geometric étale stalk

A finite family of germs and a relation among them descend to one pointed
étale neighborhood. The filtered-colimit equality criterion makes that relation
zero on a further neighborhood. Choose an actual affine open neighborhood of
the geometric point there. Its structure map is étale, hence flat, so the
relation is trivial by the equational criterion for flatness. Its witnesses
map to witnesses in the geometric stalk.

This proves flatness of the structure map constructed in
`GeometricStalkStructure`. It does not assume an affine-colimit presentation
or flatness as a field of a strict-henselization package.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Every actual pointed étale neighborhood has an affine pointed étale
refinement, constructed by lifting the geometric point to an affine open. -/
theorem geometricStalk_exists_affine_refinement
    {S : Scheme.{u}} {Ω : Type u} [Field Ω]
    (s : Spec (.of Ω) ⟶ S) (W : S.Etale)
    (t : (Scheme.pointEtaleNeighborhoods s).fiber.obj W) :
    ∃ (V : S.Etale) (v : (Scheme.pointEtaleNeighborhoods s).fiber.obj V) (f : V ⟶ W),
      IsAffine V.left ∧ (Scheme.pointEtaleNeighborhoods s).fiber.map f v = t := by
  let tHom : Spec (CommRingCat.of Ω) ⟶ W.left := t.left
  let p : W.left ⟶ S := W.hom
  obtain ⟨A, j, hj, hmem, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := tHom default) (U := ⊤) (by trivial)
  let : IsOpenImmersion j := hj
  have hrange : Set.range tHom ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x default]
    exact hmem
  let l : Spec (CommRingCat.of Ω) ⟶ Spec A := IsOpenImmersion.lift j tHom hrange
  have hl : l ≫ j = tHom := IsOpenImmersion.lift_fac j tHom hrange
  have hjp : Etale (j ≫ p) := by
    let : Etale p := W.prop
    exact Etale.etale_comp j p
  let V : S.Etale := MorphismProperty.Over.mk ⊤ (j ≫ p) hjp
  have hlp : l ≫ (j ≫ p) = s := by
    rw [← Category.assoc, hl]
    exact Over.w t
  let v : (Scheme.pointEtaleNeighborhoods s).fiber.obj V := by
    change Over.mk s ⟶ Over.mk (j ≫ p)
    exact Over.homMk l hlp
  let f : V ⟶ W := MorphismProperty.Over.homMk (show V.left ⟶ W.left from j) rfl
  have hV : IsAffine V.left := by
    change IsAffine (Spec A)
    infer_instance
  refine ⟨V, v, f, hV, ?_⟩
  apply Over.OverMorphism.ext
  exact hl

variable {R Ω : Type u} [CommRing R] [Field Ω]
  (φ : R →+* Ω)

/-- The actual structure map to the geometric étale stalk is flat. A finite
relation is solved on an actual affine étale refinement and then mapped back. -/
theorem geometricStalkStructureMap_flat : (geometricStalkStructureMap φ).Flat := by
  classical
  let s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom φ)
  let : Algebra R (geometricStalk s) := (geometricStalkStructureMap φ).toAlgebra
  change Module.Flat R (geometricStalk s)
  apply Module.Flat.of_forall_isTrivialRelation
  intro n c x hrel
  change ∑ i, geometricStalkStructureMap φ (c i) * x i = 0 at hrel
  obtain ⟨W, t, z, hz⟩ := geometricStalk_exists_representatives s x
  let βW : R →+* Γ(W.left, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.hom.appTop).hom
  have hcoeffW (r : R) : geometricStalkGerm s W t (βW r) =
      geometricStalkStructureMap φ r :=
    RingHom.congr_fun (geometricStalkGerm_comp_structure φ W t) r
  let u : Γ(W.left, ⊤) := ∑ i, βW (c i) * z i
  have hzero : geometricStalkGerm s W t u = geometricStalkGerm s W t 0 := by
    change geometricStalkGerm s W t (∑ i, βW (c i) * z i) = geometricStalkGerm s W t 0
    rw [map_sum, map_zero]
    simp only [map_mul, hcoeffW, hz]
    exact hrel
  obtain ⟨W₁, f, t₁, hf, hzero₁⟩ :=
    ((Scheme.pointEtaleNeighborhoods s).toPresheafFiber_eq_iff'
      (P := etaleSections (Spec (CommRingCat.of R))) W t u 0).mp hzero
  change f.left.appTop u = f.left.appTop 0 at hzero₁
  rw [map_zero] at hzero₁
  obtain ⟨V, v, g, hVaffine, hg⟩ := geometricStalk_exists_affine_refinement s W₁ t₁
  let : IsAffine V.left := hVaffine
  let j : V ⟶ W := g ≫ f
  have hj : (Scheme.pointEtaleNeighborhoods s).fiber.map j v = t := by
    change (Scheme.pointEtaleNeighborhoods s).fiber.map (g ≫ f) v = t
    rw [Functor.map_comp]
    change (Scheme.pointEtaleNeighborhoods s).fiber.map f
      ((Scheme.pointEtaleNeighborhoods s).fiber.map g v) = t
    rw [hg, hf]
  let δ : Γ(W.left, ⊤) ⟶ Γ(V.left, ⊤) := j.left.appTop
  have hzeroV : δ u = 0 := by
    change (g.left ≫ f.left).appTop u = 0
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hzero₁, map_zero]
  let βV : R →+* Γ(V.left, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom
  have hbase : δ.hom.comp βW = βV := by
    change (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.hom.appTop) ≫
      j.left.appTop).hom = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom
    rw [Category.assoc, ← Scheme.Hom.comp_appTop]
    exact congrArg (fun k : V.left ⟶ Spec (CommRingCat.of R) =>
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ k.appTop).hom)
      (MorphismProperty.Over.w j)
  have hcoeff (r : R) : δ (βW r) = βV r := RingHom.congr_fun hbase r
  have hrelV : ∑ i, βV (c i) * δ (z i) = 0 := by
    change δ (∑ i, βW (c i) * z i) = 0 at hzeroV
    simpa only [map_sum, map_mul, hcoeff] using hzeroV
  have hflatV : βV.Flat := by
    change (V.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Flat
    exact (RingHom.Flat.of_bijective
      ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv).mp
        inferInstance)).comp
      (HasRingHomProperty.appTop (P := @Flat) (X := V.left)
        (Y := Spec (CommRingCat.of R)) V.hom (inferInstanceAs (Flat V.hom)))
  let : Algebra R Γ(V.left, ⊤) := βV.toAlgebra
  let : Module.Flat R Γ(V.left, ⊤) := hflatV
  have hrelV' : ∑ i, c i • δ (z i) = 0 := hrelV
  obtain ⟨k, b, y, hzy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrelV'
  have hgerm : δ ≫ geometricStalkGerm s V v = geometricStalkGerm s W t := by
    have h := (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w
      j v (etaleSections (Spec (CommRingCat.of R)))
    rw [hj] at h
    exact h
  have hcoeffV (r : R) : geometricStalkGerm s V v (βV r) =
      geometricStalkStructureMap φ r :=
    RingHom.congr_fun (geometricStalkGerm_comp_structure φ V v) r
  refine ⟨k, b, (fun a => geometricStalkGerm s V v (y a)), ?_, hc⟩
  intro i
  have hzyi : δ (z i) = ∑ a, βV (b i a) * y a := hzy i
  change x i = ∑ a, geometricStalkStructureMap φ (b i a) * geometricStalkGerm s V v (y a)
  calc
    x i = geometricStalkGerm s V v (δ (z i)) :=
      ((ConcreteCategory.congr_hom hgerm (z i)).trans (hz i)).symm
    _ = geometricStalkGerm s V v (∑ a, βV (b i a) * y a) :=
      congrArg (geometricStalkGerm s V v) hzyi
    _ = ∑ a, geometricStalkStructureMap φ (b i a) * geometricStalkGerm s V v (y a) := by
      simp only [map_sum, map_mul, hcoeffV]

/-- At a closed geometric point of a local base, the constructed structure map
is faithfully flat. -/
theorem geometricStalkStructureMap_faithfullyFlat [IsLocalRing R] [IsLocalHom φ] :
    (geometricStalkStructureMap φ).FaithfullyFlat := by
  let : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
    (geometricStalkStructureMap φ).toAlgebra
  let : Module.Flat R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
    geometricStalkStructureMap_flat φ
  let : IsLocalHom (algebraMap R (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
    change IsLocalHom (geometricStalkStructureMap φ)
    exact geometricStalkStructureMap_isLocalHom φ
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- In particular, the local base ring embeds into its constructed geometric
étale stalk. -/
theorem geometricStalkStructureMap_injective [IsLocalRing R] [IsLocalHom φ] :
    Function.Injective (geometricStalkStructureMap φ) :=
  (geometricStalkStructureMap_faithfullyFlat φ).injective

end EtaleFundamentalGroups.StrictHenselian
