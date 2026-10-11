/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesTildePullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.tilde_pullbackSpecIso_unit

/-!
Base change of module sections on affine schemes when the canonical tilde-to-module comparison
is an isomorphism.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace AffineBC

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The global sections functor for modules on an affine scheme. -/
noncomputable abbrev ΓR : (Spec R).Modules ⥤ ModuleCat R := moduleSpecΓFunctor (R := R)

/-- Pullback of modules along the morphism of affine schemes induced by φ. -/
noncomputable abbrev pb : (Spec R).Modules ⥤ (Spec S).Modules := Scheme.Modules.pullback
    (Spec.map φ)

/-- Pushforward of modules along the morphism of affine schemes induced by φ. -/
noncomputable abbrev pf : (Spec S).Modules ⥤ (Spec R).Modules := Scheme.Modules.pushforward
    (Spec.map φ)

/-- The pullback and pushforward adjunction for the affine morphism. -/
noncomputable abbrev adj : pb φ ⊣ pf φ := Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)

/-- Extension of scalars along the ring homomorphism φ. -/
noncomputable abbrev ext : ModuleCat R ⥤ ModuleCat S := ModuleCat.extendScalars φ.hom
/-- Restriction of scalars along the ring homomorphism φ. -/
noncomputable abbrev res : ModuleCat S ⥤ ModuleCat R := ModuleCat.restrictScalars φ.hom
/-- The extension and restriction of scalars adjunction. -/
noncomputable abbrev adjER : ext φ ⊣ res φ := ModuleCat.extendRestrictScalarsAdj φ.hom

theorem isIso_map {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)
    [IsIso f] :
    IsIso (F.map f) :=
  ⟨⟨F.map (inv f), by rw [← F.map_comp, IsIso.hom_inv_id, F.map_id], by rw [← F.map_comp,
    IsIso.inv_hom_id, F.map_id]⟩⟩

theorem isIso_tilde_unit (N : ModuleCat.{u} R) : IsIso ((tilde.adjunction (R := R)).unit.app N)
    := by
  infer_instance

/-- The global sections map induced by the unit of the pullback and pushforward adjunction. -/
noncomputable def unitΓ (M : (Spec R).Modules) : (ΓR).obj M ⟶ (res φ).obj ((ΓR).obj ((pb φ).obj
    M)) :=
  (ΓR).map ((adj φ).unit.app M) ≫ (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app ((pb φ).obj M)

/-- The base change map on global sections obtained by the scalar adjunction. -/
noncomputable def baseChangeΓ (M : (Spec R).Modules) : (ext φ).obj ((ΓR).obj M) ⟶ (ΓR).obj ((pb
    φ).obj M) :=
  ((adjER φ).homEquiv _ _).symm (unitΓ φ M)

theorem baseChangeΓ_eq (M : (Spec R).Modules) :
    baseChangeΓ φ M = (ext φ).map (unitΓ φ M) ≫ (adjER φ).counit.app _ :=
  Adjunction.homEquiv_counit _ _ _ _

theorem unitΓ_naturality {M M' : (Spec R).Modules} (g : M ⟶ M') :
    (ΓR).map g ≫ unitΓ φ M' = unitΓ φ M ≫ (res φ).map ((ΓR).map ((pb φ).map g)) := by
  have h1 : g ≫ (adj φ).unit.app M' = (adj φ).unit.app M ≫ (pf φ).map ((pb φ).map g) := by
    have := (adj φ).unit.naturality g
    simpa only [Functor.comp_map, Functor.id_map] using this
  have h1' : (ΓR).map g ≫ (ΓR).map ((adj φ).unit.app M')
      = (ΓR).map ((adj φ).unit.app M) ≫ (ΓR).map ((pf φ).map ((pb φ).map g)) :=
    ((ΓR).map_comp _ _).symm.trans ((congrArg (ΓR).map h1).trans ((ΓR).map_comp _ _))
  have h2 : (ΓR).map ((pf φ).map ((pb φ).map g)) ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app ((pb φ).obj M')
      = (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app ((pb φ).obj M) ≫ (res φ).map
        ((ΓR).map ((pb φ).map g)) :=
    (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.naturality ((pb φ).map g)
  unfold unitΓ
  exact ((Category.assoc _ _ _).symm.trans (eq_whisker h1' _)).trans
    ((Category.assoc _ _ _).trans ((whisker_eq _ h2).trans (Category.assoc _ _ _).symm))

theorem baseChangeΓ_naturality {M M' : (Spec R).Modules} (g : M ⟶ M') :
    (ext φ).map ((ΓR).map g) ≫ baseChangeΓ φ M' = baseChangeΓ φ M ≫ (ΓR).map ((pb φ).map g) := by
  rw [baseChangeΓ_eq, baseChangeΓ_eq]
  have un := unitΓ_naturality φ g
  have hF : (ext φ).map ((ΓR).map g) ≫ (ext φ).map (unitΓ φ M')
      = (ext φ).map (unitΓ φ M) ≫ (ext φ).map ((res φ).map ((ΓR).map ((pb φ).map g))) :=
    ((ext φ).map_comp _ _).symm.trans ((congrArg (ext φ).map un).trans ((ext φ).map_comp _ _))
  have hc : (ext φ).map ((res φ).map ((ΓR).map ((pb φ).map g))) ≫ (adjER φ).counit.app ((ΓR).obj
    ((pb φ).obj M'))
      = (adjER φ).counit.app ((ΓR).obj ((pb φ).obj M)) ≫ (ΓR).map ((pb φ).map g) :=
    (adjER φ).counit_naturality _
  exact ((Category.assoc _ _ _).symm.trans (eq_whisker hF _)).trans
    ((Category.assoc _ _ _).trans ((whisker_eq _ hc).trans (Category.assoc _ _ _).symm))

/-- Compatibility of the affine pullback comparison with the units of the two adjunctions. -/
def UnitCompat (N : ModuleCat.{u} R) : Prop :=
  ((tilde.adjunction (R := R)).comp (adj φ)).unit.app N ≫
      (pf φ ⋙ moduleSpecΓFunctor (R := R)).map (tilde.pullbackSpecIso φ N).hom ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app (tilde ((ModuleCat.extendScalars
        φ.hom).obj N)) =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app N ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj N))

theorem unitΓ_tilde (N : ModuleCat.{u} R) (hunit : UnitCompat φ N) :
    (tilde.adjunction (R := R)).unit.app N ≫ unitΓ φ (tilde N) ≫ (res φ).map ((ΓR).map
      (tilde.pullbackSpecIso φ N).hom) =
      (adjER φ).unit.app N ≫ (res φ).map ((tilde.adjunction (R := S)).unit.app ((ext φ).obj N))
        := by
  have hcu : ((tilde.adjunction (R := R)).comp (adj φ)).unit.app N
      = (tilde.adjunction (R := R)).unit.app N ≫ (ΓR).map ((adj φ).unit.app (tilde N)) :=
    Adjunction.comp_unit_app _ _ N
  have h2 : (ΓR).map ((pf φ).map (tilde.pullbackSpecIso φ N).hom) ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app (tilde ((ext φ).obj N))
      = (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app ((pb φ).obj (tilde N)) ≫
        (res φ).map ((ΓR).map (tilde.pullbackSpecIso φ N).hom) :=
    (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.naturality (tilde.pullbackSpecIso φ N).hom
  have lhs : ((tilde.adjunction (R := R)).comp (adj φ)).unit.app N ≫
      (pf φ ⋙ moduleSpecΓFunctor (R := R)).map (tilde.pullbackSpecIso φ N).hom ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app (tilde ((ext φ).obj N))
      = (tilde.adjunction (R := R)).unit.app N ≫ unitΓ φ (tilde N) ≫
        (res φ).map ((ΓR).map (tilde.pullbackSpecIso φ N).hom) := by
    unfold unitΓ
    exact (eq_whisker hcu _).trans ((Category.assoc _ _ _).trans
      (whisker_eq _ ((whisker_eq _ h2).trans (Category.assoc _ _ _).symm)))
  exact lhs.symm.trans hunit

theorem baseChangeΓ_tilde (N : ModuleCat.{u} R) (hunit : UnitCompat φ N) :
    (ext φ).map ((tilde.adjunction (R := R)).unit.app N) ≫
        baseChangeΓ φ (tilde N) ≫ (ΓR).map (tilde.pullbackSpecIso φ N).hom =
      (tilde.adjunction (R := S)).unit.app ((ext φ).obj N) := by
  have key := unitΓ_tilde φ N hunit
  have key' := congrArg (fun t => (ext φ).map t ≫ (adjER φ).counit.app _) key
  simp only [Functor.map_comp, Category.assoc] at key'
  have hc1 : (ext φ).map ((res φ).map ((ΓR).map (tilde.pullbackSpecIso φ N).hom)) ≫
      (adjER φ).counit.app ((ΓR).obj (tilde ((ext φ).obj N)))
      = (adjER φ).counit.app ((ΓR).obj ((pb φ).obj (tilde N))) ≫ (ΓR).map (tilde.pullbackSpecIso
        φ N).hom :=
    (adjER φ).counit_naturality _
  have hc2 : (ext φ).map ((res φ).map ((tilde.adjunction (R := S)).unit.app ((ext φ).obj N))) ≫
      (adjER φ).counit.app ((ΓR).obj (tilde ((ext φ).obj N)))
      = (adjER φ).counit.app ((ext φ).obj N) ≫ (tilde.adjunction (R := S)).unit.app ((ext φ).obj
        N) :=
    (adjER φ).counit_naturality _
  have htri : (ext φ).map ((adjER φ).unit.app N) ≫ (adjER φ).counit.app ((ext φ).obj N) = 𝟙 _ :=
    (adjER φ).left_triangle_components N
  have rhs : (ext φ).map ((adjER φ).unit.app N) ≫
      (ext φ).map ((res φ).map ((tilde.adjunction (R := S)).unit.app ((ext φ).obj N))) ≫
      (adjER φ).counit.app ((ΓR).obj (tilde ((ext φ).obj N)))
      = (tilde.adjunction (R := S)).unit.app ((ext φ).obj N) :=
    (whisker_eq _ hc2).trans ((Category.assoc _ _ _).symm.trans ((eq_whisker htri _).trans
      (Category.id_comp _)))
  have lhs : (ext φ).map ((tilde.adjunction (R := R)).unit.app N) ≫ (ext φ).map (unitΓ φ (tilde
    N)) ≫
      (ext φ).map ((res φ).map ((ΓR).map (tilde.pullbackSpecIso φ N).hom)) ≫
      (adjER φ).counit.app ((ΓR).obj (tilde ((ext φ).obj N)))
      = (ext φ).map ((tilde.adjunction (R := R)).unit.app N) ≫
        baseChangeΓ φ (tilde N) ≫ (ΓR).map (tilde.pullbackSpecIso φ N).hom := by
    rw [baseChangeΓ_eq]
    exact whisker_eq _ ((whisker_eq _ hc1).trans (Category.assoc _ _ _).symm)
  have expandLeft : (ext φ).map ((tilde.adjunction (R := R)).unit.app N) ≫
      (ext φ).map (unitΓ φ (tilde N)) ≫
      (ext φ).map ((res φ).map ((ΓR).map (tilde.pullbackSpecIso φ N).hom)) ≫
      (adjER φ).counit.app ((ΓR).obj (tilde ((ext φ).obj N))) =
      (ext φ).map ((tilde.adjunction (R := R)).unit.app N) ≫
        (ext φ).map (unitΓ φ (tilde N) ≫ (res φ).map ((ΓR).map (tilde.pullbackSpecIso φ N).hom)) ≫
        (adjER φ).counit.app ((ΓR).obj (tilde ((ext φ).obj N))) :=
    whisker_eq _ ((Category.assoc _ _ _).symm.trans
      (eq_whisker ((ext φ).map_comp _ _).symm _))
  have collapseRight : (ext φ).map ((adjER φ).unit.app N ≫
      (res φ).map ((tilde.adjunction (R := S)).unit.app ((ext φ).obj N))) ≫
      (adjER φ).counit.app ((ΓR).obj (tilde ((ext φ).obj N))) =
      (tilde.adjunction (R := S)).unit.app ((ext φ).obj N) :=
    (eq_whisker ((ext φ).map_comp _ _) _).trans ((Category.assoc _ _ _).trans rhs)
  exact lhs.symm.trans (expandLeft.trans (key'.trans collapseRight))

theorem isIso_baseChangeΓ (M : (Spec R).Modules) [IsIso M.fromTildeΓ] (hunit : ∀ N, UnitCompat φ
    N) :
    IsIso (baseChangeΓ φ M) := by
  have hiso1 : IsIso (baseChangeΓ φ (tilde ((ΓR).obj M))) := by
    have htilde := baseChangeΓ_tilde φ ((ΓR).obj M) (hunit _)
    have i1 : IsIso ((ext φ).map ((tilde.adjunction (R := R)).unit.app ((ΓR).obj M))) :=
      @isIso_map _ _ _ _ _ _ _ _ (isIso_tilde_unit _)
    have i2 : IsIso ((ΓR).map (tilde.pullbackSpecIso φ ((ΓR).obj M)).hom) := isIso_map _ _
    have i5 : IsIso ((tilde.adjunction (R := S)).unit.app ((ext φ).obj ((ΓR).obj M))) :=
      isIso_tilde_unit _
    have i3 : IsIso ((ext φ).map ((tilde.adjunction (R := R)).unit.app ((ΓR).obj M)) ≫
        baseChangeΓ φ (tilde ((ΓR).obj M)) ≫ (ΓR).map (tilde.pullbackSpecIso φ ((ΓR).obj M)).hom) :=
      htilde ▸ i5
    have i4 := @IsIso.of_isIso_comp_left _ _ _ _ _
      ((ext φ).map ((tilde.adjunction (R := R)).unit.app ((ΓR).obj M)))
      (baseChangeΓ φ (tilde ((ΓR).obj M)) ≫ (ΓR).map (tilde.pullbackSpecIso φ ((ΓR).obj M)).hom)
        i1 i3
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (baseChangeΓ φ (tilde ((ΓR).obj M)))
      ((ΓR).map (tilde.pullbackSpecIso φ ((ΓR).obj M)).hom) i2 i4
  have hnat := baseChangeΓ_naturality φ M.fromTildeΓ
  have j1 : IsIso ((ΓR).map ((pb φ).map M.fromTildeΓ)) := @isIso_map _ _ _ _ _ _ _ _ (isIso_map _ _)
  have j2 : IsIso ((ext φ).map ((ΓR).map M.fromTildeΓ)) := @isIso_map _ _ _ _ _ _ _ _ (isIso_map
    _ _)
  have j3 : IsIso (baseChangeΓ φ (tilde ((ΓR).obj M)) ≫ (ΓR).map ((pb φ).map M.fromTildeΓ)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ hiso1 j1
  have j4 : IsIso ((ext φ).map ((ΓR).map M.fromTildeΓ) ≫ baseChangeΓ φ M) := hnat ▸ j3
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ j2 j4

end AffineBC

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules
    AlgebraicGeometry.Scheme.Modules in
theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec R).Modules) (hM : IsIso M.fromTildeΓ) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv
        ((moduleSpecΓFunctor (R := R)).obj M)
        ((moduleSpecΓFunctor (R := S)).obj ((Scheme.Modules.pullback (Spec.map φ)).obj M))).symm
      ((moduleSpecΓFunctor (R := R)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
        (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app ((Scheme.Modules.pullback (Spec.map
          φ)).obj M))) := by
  have := hM
  exact AffineBC.isIso_baseChangeΓ φ M (fun N => AlgebraicGeometry.tilde.pullbackSpecIso_unit φ N)
end Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
