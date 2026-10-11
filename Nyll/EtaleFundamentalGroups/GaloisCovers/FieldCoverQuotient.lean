/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.Basic
import Nyll.EtaleFundamentalGroups.GaloisCovers.FiberQuotient
import Nyll.EtaleFundamentalGroups.GaloisCovers.PointedQuotientTransport
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFundamentalGroupConjugacy
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected

/-!
# Pointed finite quotients associated to finite Galois field extensions

A finite Galois extension gives a categorical Galois finite-etale cover of
the base field spectrum.  This file identifies its deck group and its pointed
fiber-functor quotient with the usual restriction homomorphism on Galois
groups.
-/

noncomputable section


open CategoryTheory AlgebraicGeometry
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [_root_.IsGalois K L]

/-- A finite-dimensional Galois extension gives a finite-etale morphism of
field spectra. -/
instance fieldSpecMap_isFiniteEtale : IsFiniteEtale (ξ K L) := by
  rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom,
    RingHom.finiteEtale_algebraMap_iff]
  let : Algebra.Etale K L :=
    ⟨Algebra.FormallyEtale.of_isSeparable K L,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  constructor

private noncomputable def fieldAlgEquivSchemeIso
    (sigma : Gal(L/K)) : Spec (.of L) ≅ Spec (.of L) where
  hom := Spec.map (CommRingCat.ofHom sigma.toRingEquiv.toRingHom)
  inv := Spec.map (CommRingCat.ofHom sigma.symm.toRingEquiv.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    rw [Spec.map_injective.eq_iff]
    ext z
    simp
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    rw [Spec.map_injective.eq_iff]
    ext z
    simp

private noncomputable def fieldAlgEquivToFiniteEtaleAut
    (sigma : Gal(L/K)) : Aut (FiniteEtale.mk (ξ K L)) := by
  let Y : FiniteEtale (Spec (.of K)) := FiniteEtale.mk (ξ K L)
  let e : Y.left ≅ Y.left := fieldAlgEquivSchemeIso K L sigma
  exact MorphismProperty.Over.isoMk e (by
    change e.hom ≫ ξ K L = ξ K L
    dsimp only [e, fieldAlgEquivSchemeIso]
    have hmap : CommRingCat.ofHom (algebraMap K L) ≫
        CommRingCat.ofHom sigma.toRingEquiv.toRingHom =
        CommRingCat.ofHom (algebraMap K L) := by
      ext z
      exact sigma.commutes z
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap K L))
      (CommRingCat.ofHom sigma.toRingEquiv.toRingHom)).symm.trans
      (congrArg Spec.map hmap))

private theorem fieldAlgEquivToFiniteEtaleAut_injective :
    Function.Injective (fieldAlgEquivToFiniteEtaleAut K L) := by
  intro sigma tau h
  have hleft := congrArg
    (fun a : Aut (FiniteEtale.mk (ξ K L)) ↦ a.hom.left) h
  change Spec.map (CommRingCat.ofHom sigma.toRingEquiv.toRingHom) =
    Spec.map (CommRingCat.ofHom tau.toRingEquiv.toRingHom) at hleft
  have hring := Spec.map_injective hleft
  apply AlgEquiv.ext
  intro z
  exact ConcreteCategory.congr_hom hring z

/-- The finite-etale cover of a field spectrum associated to a finite Galois
extension is a categorical Galois object. -/
theorem fieldFiniteEtaleCover_isGalois :
    IsGalois (FiniteEtale.mk (ξ K L)) := by
  let Y : FiniteEtale (Spec (.of K)) := FiniteEtale.mk (ξ K L)
  let : ConnectedSpace Y.left := by
    let : Unique Y.left := by
      dsimp only [Y, FiniteEtale.mk_left]
      infer_instance
    have h : (Set.univ : Set Y.left).Subsingleton :=
      fun x _ y _ ↦ Subsingleton.elim x y
    exact { toPreconnectedSpace := ⟨h.isPreconnected⟩
            toNonempty := inferInstance }
  let : IsConnected Y := isConnected_of_connectedSpace_left Y
  let Omega := AlgebraicClosure K
  let xi : Spec (.of Omega) ⟶ Spec (.of K) := ξ K Omega
  apply (isGalois_iff_card_aut_eq_finrank xi Y).mpr
  apply Nat.le_antisymm
  · exact card_aut_le_card_fiber_of_connected (fiber xi) Y |>.trans_eq
      (natCard_fiber_eq_finrank xi Y)
  · calc
      Y.hom.finrank (xi (IsLocalRing.closedPoint Omega)) =
          Module.finrank K L := by
        change Scheme.Hom.finrank (ξ K L)
          ((ξ K Omega) (IsLocalRing.closedPoint Omega)) = _
        calc
          _ = Module.rankAtStalk L
              ((ξ K Omega) (IsLocalRing.closedPoint Omega)) :=
            Scheme.Hom.finrank_SpecMap_algebraMap K L _
          _ = Module.finrank K L := by
            rw [Module.rankAtStalk_eq_finrank_of_free]
            rfl
      _ = Nat.card Gal(L/K) :=
        (_root_.IsGalois.card_aut_eq_finrank K L).symm
      _ ≤ Nat.card (Aut Y) :=
        Nat.card_le_card_of_injective
          (fieldAlgEquivToFiniteEtaleAut K L)
          (fieldAlgEquivToFiniteEtaleAut_injective K L)

private noncomputable def fieldGaloisToFiniteEtaleAutOpHom :
    Gal(L/K) →* (Aut (FiniteEtale.mk (ξ K L)))ᵐᵒᵖ where
  toFun sigma := MulOpposite.op (fieldAlgEquivToFiniteEtaleAut K L sigma)
  map_one' := by
    apply MulOpposite.unop_injective
    apply Aut.ext
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom ((1 : Gal(L/K)).toRingHom)) = 𝟙 _
    rw [← Spec.map_id]
    congr 1
  map_mul' sigma tau := by
    apply MulOpposite.unop_injective
    apply Aut.ext
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom ((sigma * tau).toRingHom)) =
      (MulOpposite.unop
        (MulOpposite.op (fieldAlgEquivToFiniteEtaleAut K L sigma) *
          MulOpposite.op (fieldAlgEquivToFiniteEtaleAut K L tau))).hom.left
    change Spec.map (CommRingCat.ofHom ((sigma * tau).toRingHom)) =
      Spec.map (CommRingCat.ofHom sigma.toRingHom) ≫
        Spec.map (CommRingCat.ofHom tau.toRingHom)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1

private theorem fieldGaloisToFiniteEtaleAutOpHom_bijective :
    Function.Bijective (fieldGaloisToFiniteEtaleAutOpHom K L) := by
  let : IsGalois (FiniteEtale.mk (ξ K L)) :=
    fieldFiniteEtaleCover_isGalois K L
  let : IsConnected (FiniteEtale.mk (ξ K L)) := inferInstance
  let : Finite (Aut (FiniteEtale.mk (ξ K L))) := inferInstance
  let : Finite ((Aut (FiniteEtale.mk (ξ K L)))ᵐᵒᵖ) :=
    Finite.of_injective MulOpposite.unop MulOpposite.unop_injective
  have hinj : Function.Injective (fieldGaloisToFiniteEtaleAutOpHom K L) := by
    intro sigma tau h
    apply fieldAlgEquivToFiniteEtaleAut_injective K L
    exact MulOpposite.op_injective h
  exact hinj.bijective_of_nat_card_le (by
    rw [_root_.IsGalois.card_aut_eq_finrank K L]
    rw [Nat.card_congr MulOpposite.opEquiv.symm]
    let Y : FiniteEtale (Spec (.of K)) := FiniteEtale.mk (ξ K L)
    let Omega := AlgebraicClosure K
    let xi : Spec (.of Omega) ⟶ Spec (.of K) := ξ K Omega
    have hcard : Nat.card (Aut Y) = Module.finrank K L := calc
      Nat.card (Aut Y) = Y.hom.finrank
          (xi (IsLocalRing.closedPoint Omega)) :=
        (isGalois_iff_card_aut_eq_finrank xi Y).mp inferInstance
      _ = Module.finrank K L := by
        change Scheme.Hom.finrank (ξ K L)
          ((ξ K Omega) (IsLocalRing.closedPoint Omega)) = _
        calc
          _ = Module.rankAtStalk L
              ((ξ K Omega) (IsLocalRing.closedPoint Omega)) :=
            Scheme.Hom.finrank_SpecMap_algebraMap K L _
          _ = Module.finrank K L := by
            rw [Module.rankAtStalk_eq_finrank_of_free]
            rfl
    exact hcard.le)

/-- The usual Galois group of a finite field extension is canonically the
opposite deck-transformation group of the corresponding scheme cover. -/
noncomputable def fieldGaloisToFiniteEtaleAutOpMulEquiv :
    Gal(L/K) ≃* (Aut (FiniteEtale.mk (ξ K L)))ᵐᵒᵖ :=
  MulEquiv.ofBijective (fieldGaloisToFiniteEtaleAutOpHom K L)
    (fieldGaloisToFiniteEtaleAutOpHom_bijective K L)

variable (Omega : Type u) [Field Omega] [Algebra K Omega]
  [Algebra L Omega] [IsScalarTower K L Omega] [IsSepClosed Omega]

/-- The canonical point of the field cover determined by the inclusion
`L → Omega`. -/
noncomputable def fieldFiniteEtaleCoverCanonicalPoint :
    (fib K Omega).obj (FiniteEtale.mk (ξ K L)) :=
  (fiberObjEquivHom (ξ K Omega) (FiniteEtale.mk (ξ K L))).symm
    (Over.homMk (ξ L Omega) (fieldGeometricPoint_comp K L Omega))

/-- Under the canonical deck-group equivalence, the pointed finite-cover
quotient is restriction of automorphisms to `L`. -/
theorem fieldFiniteEtaleCoverQuotient_apply
    [IsSepClosure K Omega] (sigma : Gal(Omega/K)) :
    let Y : FiniteEtale (Spec (.of K)) := FiniteEtale.mk (ξ K L)
    let hY : IsGalois Y := fieldFiniteEtaleCover_isGalois K L
    letI : IsGalois Y := hY
    let y := fieldFiniteEtaleCoverCanonicalPoint K L Omega
    (fieldGaloisToFiniteEtaleAutOpMulEquiv K L).symm
        (finiteEtaleGaloisCoverQuotientMonoidHom
          (ξ K Omega) Y hY y
          (absoluteGaloisToFiberAutMulEquiv K Omega inferInstance sigma)) =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := Omega) L sigma := by
  let Y : FiniteEtale (Spec (.of K)) := FiniteEtale.mk (ξ K L)
  let hY : IsGalois Y := fieldFiniteEtaleCover_isGalois K L
  let : IsGalois Y := hY
  let y := fieldFiniteEtaleCoverCanonicalPoint K L Omega
  let E := fieldGaloisToFiniteEtaleAutOpMulEquiv K L
  apply E.injective
  rw [E.apply_symm_apply]
  apply MulOpposite.unop_injective
  apply (evaluationEquivOfIsGalois (fib K Omega) Y y).injective
  simp only [evaluationEquivOfIsGalois_apply]
  rw [finiteEtaleGaloisCoverQuotientMonoidHom_evaluation]
  change
    (absoluteGaloisToFiberAutMulEquiv K Omega inferInstance sigma).hom.app Y y =
      (fib K Omega).map
        (fieldAlgEquivToFiniteEtaleAut K L
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := Omega) L sigma)).hom y
  rw [absoluteGaloisToFiberAutMulEquiv,
    CategoryTheory.PreGaloisCategory.toAutMulEquiv_apply,
    CategoryTheory.PreGaloisCategory.toAut_hom_app_apply]
  apply (fiberObjEquivHom (ξ K Omega) Y).injective
  rw [algEquiv_smul_fiber_def, Equiv.apply_symm_apply,
    ← fiberObjEquivHom_naturality]
  dsimp only [y, fieldFiniteEtaleCoverCanonicalPoint]
  rw [Equiv.apply_symm_apply]
  apply CategoryTheory.Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom sigma.toRingEquiv.toRingHom) ≫ ξ L Omega =
    ξ L Omega ≫ Spec.map (CommRingCat.ofHom
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Omega) L sigma).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  ext z
  exact (AlgEquiv.restrictNormal_commutes sigma L z).symm

end EtaleFundamentalGroups

end
