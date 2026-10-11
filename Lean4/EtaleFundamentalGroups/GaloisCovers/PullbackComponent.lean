/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.Basic
import EtaleFundamentalGroups.GaloisCategories.ConnectedActions
import EtaleFundamentalGroups.GeometricFiber.Functoriality
import EtaleFundamentalGroups.FiniteEtale.Connected

/-!
# Galois components of pulled-back covers

Pullback of a connected Galois cover need not remain connected.  Nevertheless,
the connected component containing the pullback of a chosen geometric-fiber
point is again Galois.  This is the componentwise form that is valid for an
arbitrary morphism of connected base schemes.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u u₁ u₂ w

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]

private theorem isGalois_of_stabilizer_normal
    {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (A : C) [IsConnected A] (a : F.obj A)
    (ha : (MulAction.stabilizer (Aut F) a).Normal) :
    IsGalois A := by
  let N := MulAction.stabilizer (Aut F) a
  let : N.Normal := ha
  let : MulAction.IsPretransitive (Aut F) (F.obj A) :=
    FiberFunctor.isPretransitive_of_isConnected F A
  let e : F.obj A ≃ Aut F ⧸ N :=
    (Equiv.Set.univ (F.obj A)).symm.trans <|
      (Set.equivOfEq ((MulAction.orbit_eq_univ (Aut F) a).symm)).trans <|
        MulAction.orbitEquivQuotientStabilizer (Aut F) a
  have he_symm (q : Aut F ⧸ N) :
      e.symm q = MulAction.ofQuotientStabilizer (Aut F) a q := by
    rfl
  have he_smul (g : Aut F) (x : F.obj A) :
      e (g • x) = g • e x := by
    apply e.symm.injective
    rw [e.symm_apply_apply, he_symm,
      MulAction.ofQuotientStabilizer_smul, ← he_symm,
      e.symm_apply_apply]
  apply (isGalois_iff_pretransitive F A).mpr
  constructor
  intro x y
  let qx : Aut F ⧸ N := e x
  let qy : Aut F ⧸ N := e y
  obtain ⟨g, hg⟩ := Quotient.exists_rep qx
  obtain ⟨h, hh⟩ := Quotient.exists_rep qy
  let r : (Aut F ⧸ N) ≃ (Aut F ⧸ N) :=
    Equiv.mulRight (QuotientGroup.mk' N (g⁻¹ * h))
  let p : F.obj A ≃ F.obj A := e.trans (r.trans e.symm)
  let s : (functorToAction F).obj A ≅ (functorToAction F).obj A :=
    Action.mkIso (FintypeCat.equivEquivIso p) (fun sigma ↦ by
      apply FintypeCat.hom_ext
      intro z
      let z' : F.obj A := z
      change p (sigma • z') = sigma • p z'
      apply e.injective
      simp only [p, Equiv.trans_apply, Equiv.apply_symm_apply]
      rw [he_smul, he_smul]
      rw [Equiv.apply_symm_apply]
      change (QuotientGroup.mk' N sigma * e z') *
          QuotientGroup.mk' N (g⁻¹ * h) =
        QuotientGroup.mk' N sigma *
          (e z' * QuotientGroup.mk' N (g⁻¹ * h))
      exact mul_assoc _ _ _)
  let phi : A ≅ A := (functorToAction F).preimageIso s
  refine ⟨phi, ?_⟩
  have hmap : (functorToAction F).map phi.hom = s.hom :=
    (functorToAction F).map_preimage s.hom
  have happ : F.map phi.hom x = s.hom.hom x :=
    ConcreteCategory.congr_hom (congrArg Action.Hom.hom hmap) x
  change F.map phi.hom x = y
  rw [happ]
  have hs_apply : s.hom.hom x = p x := rfl
  rw [hs_apply]
  apply e.injective
  simp only [p, Equiv.trans_apply, Equiv.apply_symm_apply]
  change qx * QuotientGroup.mk' N (g⁻¹ * h) = qy
  rw [← hg, ← hh]
  simp

/-- A chosen geometric-fiber point of a pulled-back Galois cover lies in a
connected component which is itself a Galois cover. -/
theorem exists_galoisComponent_pullback
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (W : FiniteEtale Y) (hW : IsGalois W)
    (w : (fiber (xi ≫ f)).obj W) :
    ∃ (Z : FiniteEtale X)
      (i : Z ⟶ (pullback f).obj W)
      (z : (fiber xi).obj Z),
      (fiber xi).map i z =
          transportedPointOfCompIso
            (pullback f) (pullbackFiberIso f xi) W w ∧
        IsGalois Z ∧ Mono i := by
  let : IsGalois W := hW
  let F := fiber (xi ≫ f)
  let F' := fiber xi
  let H := pullback f
  let t := pullbackFiberIso f xi
  let y : F'.obj (H.obj W) :=
    transportedPointOfCompIso H t W w
  obtain ⟨Z, i, z, hiz, hZconnected, hi⟩ :=
    fiber_in_connected_component F' (H.obj W) y
  let : IsConnected Z := hZconnected
  let : Mono i := hi
  have hi_injective : Function.Injective (F'.map i) := by
    let : Mono (F'.map i) := CategoryTheory.Functor.map_mono F' i
    exact ConcreteCategory.injective_of_mono_of_preservesPullback (F'.map i)
  have hstabilizer_component :
      MulAction.stabilizer (Aut F') z =
        MulAction.stabilizer (Aut F') y := by
    ext a
    simp only [MulAction.mem_stabilizer_iff]
    constructor
    · intro ha
      rw [← hiz, mulAction_naturality, ha]
    · intro ha
      apply hi_injective
      calc
        F'.map i (a • z) = a • F'.map i z :=
          (mulAction_naturality F' a i z).symm
        _ = a • y := congrArg (fun q ↦ a • q) hiz
        _ = y := ha
        _ = F'.map i z := hiz.symm
  have hstabilizer_pullback :
      MulAction.stabilizer (Aut F') y =
        (MulAction.stabilizer (Aut F) w).comap
          (autHomOfCompIso H t).toMonoidHom :=
    stabilizer_transportedPointOfCompIso H t W w
  have hnormal_original :
      (MulAction.stabilizer (Aut F) w).Normal :=
    stabilizer_normal_of_isGalois F W w
  have hnormal_pullback :
      ((MulAction.stabilizer (Aut F) w).comap
        (autHomOfCompIso H t).toMonoidHom).Normal := by
    let : (MulAction.stabilizer (Aut F) w).Normal := hnormal_original
    infer_instance
  have hnormal_component :
      (MulAction.stabilizer (Aut F') z).Normal := by
    rw [hstabilizer_component, hstabilizer_pullback]
    exact hnormal_pullback
  have hZgalois : IsGalois Z :=
    isGalois_of_stabilizer_normal F' Z z hnormal_component
  exact ⟨Z, i, z, hiz, hZgalois, hi⟩

end AlgebraicGeometry.FiniteEtale

end
