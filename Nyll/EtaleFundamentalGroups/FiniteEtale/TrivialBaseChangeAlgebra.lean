/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.TrivialCoverAlgebra
import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
import Nyll.EtaleFundamentalGroups.GaloisCategories.GaloisObjectFixedFiber
import Mathlib.AlgebraicGeometry.Pullbacks


/-!
# Actual tensor splitting from the pullback action

The tensor spectrum is identified with the literal finite-etale pullback.
The fiber comparison then turns triviality of the induced fundamental-group
action into a splitting of the actual tensor algebra.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct


namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Triviality of the image action is exactly what is needed on the actual
pullback fiber. The canonical pullback-fiber comparison supplies the transport. -/
theorem pullback_fiber_fixed_of_image_fixed
    {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (f : X ⟶ Y) (point : Spec (.of Ω) ⟶ X) (W : FiniteEtale Y)
    (hfixed : ∀ (g : Aut (fiber point)) (w : (fiber (point ≫ f)).obj W),
      fundamentalGroupHom f point g • w = w) :
    ∀ (g : Aut (fiber point)) (w : (fiber point).obj ((pullback f).obj W)),
      g • w = w := by
  intro g w
  let t := pullbackFiberIso f point
  have hm : g ∈ (MulAction.stabilizer (Aut (fiber (point ≫ f))) ((t.app W).hom w)).comap
      (PreGaloisCategory.autHomOfCompIso (pullback f) t).toMonoidHom :=
    hfixed g ((t.app W).hom w)
  rw [← PreGaloisCategory.stabilizer_transportedPointOfCompIso (pullback f) t] at hm
  have hw : PreGaloisCategory.transportedPointOfCompIso (pullback f) t W
      ((t.app W).hom w) = w := FintypeCat.hom_inv_id_apply (t.app W) w
  rw [hw] at hm
  exact hm

/-- Fixedness on the actual pullback fiber gives fixedness under the induced
fundamental-group image, using the same canonical fiber comparison. -/
theorem image_fixed_of_pullback_fiber_fixed
    {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (f : X ⟶ Y) (point : Spec (.of Ω) ⟶ X) (W : FiniteEtale Y)
    (hfixed : ∀ (g : Aut (fiber point))
      (w : (fiber point).obj ((pullback f).obj W)), g • w = w) :
    ∀ (g : Aut (fiber point)) (w : (fiber (point ≫ f)).obj W),
      fundamentalGroupHom f point g • w = w := by
  intro g w
  let t := pullbackFiberIso f point
  have hm : g ∈ MulAction.stabilizer (Aut (fiber point))
      (PreGaloisCategory.transportedPointOfCompIso (pullback f) t W w) :=
    hfixed g _
  rw [PreGaloisCategory.stabilizer_transportedPointOfCompIso (pullback f) t] at hm
  exact hm

/-- A trivial induced action on an affine finite-etale cover supplies an
actual algebra isomorphism splitting its scalar extension. -/
theorem exists_tensor_algEquiv_pi_of_image_fixed
    (K L B : Type u) [CommRing K] [Field L] [CommRing B]
    [Algebra K L] [Algebra K B]
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap K B)))]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (point : Spec (.of Ω) ⟶ Spec (.of L))
    (hfixed : ∀ (g : Aut (fiber point))
      (w : (fiber (point ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj
        (mk (Spec.map (CommRingCat.ofHom (algebraMap K B))))),
      fundamentalGroupHom (Spec.map (CommRingCat.ofHom (algebraMap K L))) point g • w = w) :
    ∃ (ι : Type u) (_ : Finite ι), Nonempty ((L ⊗[K] B) ≃ₐ[L] (ι → L)) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let W : FiniteEtale (Spec (.of K)) := mk (Spec.map (CommRingCat.ofHom (algebraMap K B)))
  let P : FiniteEtale (Spec (.of L)) := (pullback f).obj W
  let e : Spec (.of (L ⊗[K] B)) ≅ P.left :=
    (pullbackSpecIso K L B).symm ≪≫ pullbackSymmetry f W.hom
  have he : e.hom ≫ P.hom = Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] B))) := by
    change ((pullbackSpecIso K L B).inv ≫
        (pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap K L)))
          (Spec.map (CommRingCat.ofHom (algebraMap K B)))).hom) ≫
      Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K B)))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) = _
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact pullbackSpecIso_inv_fst' K L B
  let : IsFiniteEtale e.hom := .mk
  let : IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] B)))) := by
    rw [← he]
    infer_instance
  let T : FiniteEtale (Spec (.of L)) :=
    mk (Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] B))))
  let E : T ≅ P := MorphismProperty.Over.isoMk e he
  apply exists_algEquiv_pi_of_fiber_fixed L (L ⊗[K] B) point
  intro g w
  apply (ConcreteCategory.bijective_of_isIso ((fiber point).map E.hom)).injective
  rw [← PreGaloisCategory.mulAction_naturality]
  exact pullback_fiber_fixed_of_image_fixed f point W hfixed g ((fiber point).map E.hom w)

end AlgebraicGeometry.FiniteEtale
