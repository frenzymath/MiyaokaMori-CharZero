import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackCompMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.SheafDualLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.AlgebraMapToPushforwardMorphismLevel
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertyMonoidalPow
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertySymPowDesc

/-! # The local ring homomorphism `projBundle.localRingHom`

Companion of `ProjectiveBundleUniversalProperty.lean`:

* `projBundle.localRingHomComponent V f M ψ U e W m : Γ(W, Sym^m V^∨) →+ Γ(U ⊓ f⁻¹W, O)` — the `m`-th component of
  the local piece of the lift (Stacks 01O4): pull the section back along `g = (U ⊓ f⁻¹W ↪ T) ≫ f`, apply
  `Φ_m = c ≫ ι^*(Ψ_m) ≫ pullbackMonoidalPow ≫ e^{⊗m} ≫ unitPowCollapse`, evaluate on `⊤`;
  its named pieces `localRingHomIncl / Base / Base_top_le / Triv / SheafHom` and `localRingHomComponent_apply` (`rfl`);
* (1/6) `localRingHomComponent_one` via `pullback_map_one_comp_localRingHomSheafHom_zero` and
  `localRingHomComponent_zero_apply` (0-th component on `S.one.app W r` is `g^♯ r`);
* (2/6) `localRingHomComponent_mul` via `pullback_map_mul_comp_localRingHomSheafHom`
  (`g^*(S.mul i j) ≫ Φ_{i+j} = δ ≫ (Φ_i ⊗ₘ Φ_j) ≫ λ`, chained with `MulAux.chain_aux`) and adjoint transposition
  to `pushforwardUnitMul` on sections;
* `projBundle.localRingHom V f M ψ U e W : A(W) →+* Γ(U ⊓ f⁻¹W, O)` — `DirectSum.toSemiring` of the components.

Source: Stacks 01O4 (`lemma-apply-relative`), 01N8. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The `m`-th component of the local ring homomorphism (a local piece of the lift): `U ⊆ T` open,
`e : M|_U ≅ O_U` a trivialization, `W ⊆ X` open, `V := U ⊓ f⁻¹W`, `g := (V ↪ U ↪ T) ≫ f`. The map
`Γ(W, S_m) → Γ(V, O)` pulls a section back along `g` (adjunction unit, then restriction to `⊤ ≤ g⁻¹W`)
and applies
`g^*S_m ≅ (V→T)^*(f^*S_m) →(Sym^m ψ) (V→T)^*(M^{⊗m}) → ((V→T)^*M)^{⊗m} →(e^{⊗m}) O^{⊗m} → O`. -/

noncomputable def AlgebraicGeometry.Scheme.projBundle.localRingHomComponent {X T : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) (m : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsPiece W m →+
      Γ((U ⊓ f ⁻¹ᵁ W).toScheme, ⊤) :=
  let S := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)
  let j : (U ⊓ f ⁻¹ᵁ W).toScheme ⟶ U.toScheme := T.homOfLE inf_le_left
  let ι : (U ⊓ f ⁻¹ᵁ W).toScheme ⟶ T := j ≫ U.ι
  let g : (U ⊓ f ⁻¹ᵁ W).toScheme ⟶ X := ι ≫ f
  -- `(V → T)^*M ≅ O_V`: via `pullbackComp`, `restrict ≅ pullback` (Mathlib `restrictFunctorIsoPullback`), `e`
  -- and `j^*O ≅ O`
  let e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅
      SheafOfModules.unit (U ⊓ f ⁻¹ᵁ W).toScheme.ringCatSheaf :=
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp j U.ι).app M).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback j).mapIso
        (((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫ e) ≪≫
      AlgebraicGeometry.Scheme.Modules.pullbackUnitIso j
  let Φ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj (S.part m) ⟶
      SheafOfModules.unit (U ⊓ f ⁻¹ᵁ W).toScheme.ringCatSheaf :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).inv.app (S.part m) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback ι).map
        (AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc f ψ m) ≫
      AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow ι M m ≫
      AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom m ≫
      AlgebraicGeometry.Scheme.Modules.unitPowCollapse _ m
  have hgW : (⊤ : (U ⊓ f ⁻¹ᵁ W).toScheme.Opens) ≤ g ⁻¹ᵁ W := by
    intro y _
    show f.base ((j ≫ U.ι).base y) ∈ W
    rw [AlgebraicGeometry.Scheme.homOfLE_ι]
    exact y.2.2
  AddMonoidHom.mk' (fun s =>
    (Φ.val.app (Opposite.op ⊤)).hom
      (((AlgebraicGeometry.Scheme.Modules.pullback g).obj (S.part m)).presheaf.map
        (CategoryTheory.homOfLE hgW).op
        ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (S.part m)).val.app
          (Opposite.op W)).hom s))) (fun a b => by
    rw [map_add]
    exact (congrArg _ (map_add _ _ _)).trans (map_add _ _ _))

/-! ## Named pieces of `localRingHomComponent` and the computation of the degree-zero component

The `ι`, `g`, `hgW`, `e'`, `Φ` of the definition body as named declarations (definitionally equal to
the data of `localRingHomComponent`; `localRingHomComponent_apply` is `rfl`), and the computation of
the degree-zero component on `S.one.app W r` as `g^♯ r`. -/

section LocalRingHomPieces

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.projBundle

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- The open immersion `ι : U ⊓ f⁻¹W ↪ U ↪ T` (the `ι` of the definition of `localRingHomComponent`). -/
noncomputable def localRingHomIncl (f : T ⟶ X) (U : T.Opens) (W : X.Opens) :
    (U ⊓ f ⁻¹ᵁ W).toScheme ⟶ T :=
  T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι

/-- `g := ι ≫ f : U ⊓ f⁻¹W → X` (the `g` of the definition of `localRingHomComponent`). -/
noncomputable def localRingHomBase (f : T ⟶ X) (U : T.Opens) (W : X.Opens) :
    (U ⊓ f ⁻¹ᵁ W).toScheme ⟶ X :=
  localRingHomIncl f U W ≫ f

/-- `V = U ⊓ f⁻¹W` lies entirely in `g⁻¹W` (the `hgW` of the definition). -/
theorem localRingHomBase_top_le (f : T ⟶ X) (U : T.Opens) (W : X.Opens) :
    (⊤ : (U ⊓ f ⁻¹ᵁ W).toScheme.Opens) ≤ localRingHomBase f U W ⁻¹ᵁ W := by
  intro y _
  show f.base ((T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι).base y) ∈ W
  rw [AlgebraicGeometry.Scheme.homOfLE_ι]
  exact y.2.2

/-- The trivialization `e` pulled back along `V ↪ U`: `ι^*M ≅ O_V` (the `e'` of the definition). -/
noncomputable def localRingHomTriv (f : T ⟶ X) (M : T.Modules) (U : T.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) :
    (AlgebraicGeometry.Scheme.Modules.pullback (localRingHomIncl f U W)).obj M ≅
      SheafOfModules.unit (U ⊓ f ⁻¹ᵁ W).toScheme.ringCatSheaf :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackComp (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U)) U.ι).app M).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U))).mapIso
      (((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫ e) ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U))

/-- The sheaf morphism `g^*S_m ⟶ O_V` of the `m`-th component (the `Φ` of the definition). -/
noncomputable def localRingHomSheafHom (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X)
    (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) (m : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback (localRingHomBase f U W)).obj
        ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).part m) ⟶
      SheafOfModules.unit (U ⊓ f ⁻¹ᵁ W).toScheme.ringCatSheaf :=
  (AlgebraicGeometry.Scheme.Modules.pullbackComp (localRingHomIncl f U W) f).inv.app _ ≫
    (AlgebraicGeometry.Scheme.Modules.pullback (localRingHomIncl f U W)).map
      (AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc f ψ m) ≫
    AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow (localRingHomIncl f U W) M m ≫
    AlgebraicGeometry.Scheme.Modules.monoidalPowMap (localRingHomTriv f M U e W).hom m ≫
    AlgebraicGeometry.Scheme.Modules.unitPowCollapse _ m

/-- Unfolding of the definition of `localRingHomComponent` (`rfl`). -/
theorem localRingHomComponent_apply (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X)
    (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) (m : ℕ)
    (s : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsPiece W m) :
    localRingHomComponent V f M ψ U e W m s =
      ((localRingHomSheafHom V f M ψ U e W m).val.app (op ⊤)).hom
        (((AlgebraicGeometry.Scheme.Modules.pullback (localRingHomBase f U W)).obj _).presheaf.map
          (homOfLE (localRingHomBase_top_le f U W)).op
          ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (localRingHomBase f U W)).unit.app
            _).val.app (op W)).hom s)) := rfl

/-- `g^*(S.one) ≫ Φ_0 = (pullbackUnitIso g).hom`. Levelwise: naturality of `pullbackComp.inv`;
`f^*(S.one) ≫ Ψ_0 = pullbackUnitIso f` (`pullback_map_one_comp_symGradedPullbackDesc_zero`; `V^∨` is
quasi-coherent by `isLocallyFree_dual'` + `isQuasicoherent_of_isLocallyFree`); the remaining levels are
`𝟙` or `pullbackUnitIso ι` in degree `0`; finally `pullbackComp_hom_app_pullbackUnitIso_hom` composes them
to `pullbackUnitIso (ι ≫ f)`. -/
theorem pullback_map_one_comp_localRingHomSheafHom_zero (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) :
    (AlgebraicGeometry.Scheme.Modules.pullback (localRingHomBase f U W)).map
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).one ≫
        localRingHomSheafHom V f M ψ U e W 0 =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (localRingHomBase f U W)).hom := by
  have hq : (AlgebraicGeometry.Scheme.Modules.dual V).IsQuasicoherent :=
    haveI := AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual' V
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyFree _
  unfold localRingHomSheafHom localRingHomBase
  erw [AlgebraicGeometry.Scheme.Modules.monoidalPowMap_zero_eq_id,
    AlgebraicGeometry.Scheme.Modules.unitPowCollapse_zero_eq_id,
    AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow_zero_eq_unitIso, Category.comp_id]
  have e1 := (AlgebraicGeometry.Scheme.Modules.pullbackComp (localRingHomIncl f U W) f).inv.naturality_assoc
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).one
    ((AlgebraicGeometry.Scheme.Modules.pullback (localRingHomIncl f U W)).map
        (AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc f ψ 0) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (localRingHomIncl f U W)).hom)
  refine e1.trans ?_
  have e2 : (AlgebraicGeometry.Scheme.Modules.pullback (localRingHomIncl f U W)).map
        ((AlgebraicGeometry.Scheme.Modules.pullback f).map
          (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).one) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback (localRingHomIncl f U W)).map
        (AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc f ψ 0) =
      (AlgebraicGeometry.Scheme.Modules.pullback (localRingHomIncl f U W)).map
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom := by
    rw [← Functor.map_comp, AlgebraicGeometry.Scheme.Modules.pullback_map_one_comp_symGradedPullbackDesc_zero f _ hq ψ]
    exact rfl
  have e3 : (AlgebraicGeometry.Scheme.Modules.pullbackComp (localRingHomIncl f U W) f).inv.app _ ≫
      (AlgebraicGeometry.Scheme.Modules.pullback (localRingHomIncl f U W)).map
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (localRingHomIncl f U W)).hom =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (localRingHomIncl f U W ≫ f)).hom := by
    rw [← AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_pullbackUnitIso_hom]
    erw [Iso.inv_hom_id_app_assoc]
  refine Eq.trans ?_ e3
  refine congrArg (fun k => _ ≫ k) ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ _) e2)

/-- **The degree-zero component on `S.one.app W r` is `g^♯ r`** (restricted to `⊤ ≤ g⁻¹W`):
`app_top_map_unit_app_eq` rewrites it as the adjoint transpose of `Φ_0`; `homEquiv_naturality_left` and
`pullback_map_one_comp_localRingHomSheafHom_zero` turn the transpose into `unitToPushforwardObjUnit g`,
whose map on sections is the ring homomorphism `g^♯` (Mathlib `unitToPushforwardObjUnit_val_app_apply`,
`rfl`). This is the common generalization of (1/6) `localRingHomComponent_one` (`r = 1`) and (5/6)
`lift_hom`. -/
theorem localRingHomComponent_zero_apply (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X)
    (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens)
    (r : Γ(X, W)) :
    localRingHomComponent V f M ψ U e W 0
        ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).one.app W r) =
      (localRingHomBase f U W).appLE W ⊤ (localRingHomBase_top_le f U W) r := by
  refine (localRingHomComponent_apply V f M ψ U e W 0 _).trans ?_
  refine (AlgebraicGeometry.Scheme.Modules.app_top_map_unit_app_eq (localRingHomBase f U W)
    (localRingHomSheafHom V f M ψ U e W 0) W (localRingHomBase_top_le f U W) _).trans ?_
  have h := Adjunction.homEquiv_naturality_left
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (localRingHomBase f U W))
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).one
    (localRingHomSheafHom V f M ψ U e W 0)
  rw [pullback_map_one_comp_localRingHomSheafHom_zero] at h
  erw [AlgebraicGeometry.Scheme.Modules.homEquiv_pullbackUnitIso_hom_pbup] at h
  have h' := congrArg (fun k => (k.val.app (op W)).hom r) h
  refine congrArg _ (Eq.trans ?_ h'.symm)
  rfl

end AlgebraicGeometry.Scheme.projBundle

end LocalRingHomPieces

/-- **(1/6) The components preserve `1`**: the degree-zero component sends the graded unit of `A(W)` to
`1 ∈ Γ(V, O)` (the first hypothesis of `DirectSum.toSemiring`).

Reference: Stacks 01O4 / 01N8 (a morphism to the relative Proj is given by a graded map preserving
unit and multiplication).

Proof sketch. Write `S = symGradedAlgebra (dual V)`, `g = (V ⊓ f⁻¹W ↪ U ↪ T) ≫ f`, and `Φ_m` for the
sheaf morphism of the definition. `localRingHomComponent … W 0` sends `s ∈ Γ(W, S_0)` to
`Φ_0.app ⊤ (res_{⊤ ≤ g⁻¹W} (η_g.app W s))`, with `η_g` the unit of the pullback–pushforward adjunction.
The graded unit of `A(W)` is `S.one.app W 1` (by the definition of `sectionsGCommRing`). Since `V^∨` is
quasi-coherent, `symGradedAlgebra` takes the quasi-coherent branch and `S.one = symPowπ (dual V) 0`
(after `Sym^0 ≅ 𝟙_`), and `symGradedPullbackDesc f ψ 0 = symPowPullbackDesc f ψ 0`; on `Sym^0` the
descent of `ψ` is `(pullbackUnitIso f).hom` (`symPowπ_desc`, `monoidalPowMap ψ 0 = 𝟙`,
`pullbackMonoidalPow f W 0 = (pullbackUnitIso f).hom`), and the remaining levels are unit isomorphisms
in degree `0`. Hence `Φ_0 = (pullbackUnitIso g).hom` (compatibility of `pullbackUnitIso` with the
composite `ι ≫ f`: `pullbackComp_hom_app_pullbackUnitIso_hom`), whose adjoint transpose is
`unitToPushforwardObjUnit g^♯`, i.e. the ring homomorphism `g.app W` on sections, which preserves `1`;
the restriction map preserves `1` as well. Formally: `localRingHomComponent_zero_apply` with `r = 1`,
then `map_one`. -/
theorem AlgebraicGeometry.Scheme.projBundle.localRingHomComponent_one {X T : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) :
    AlgebraicGeometry.Scheme.projBundle.localRingHomComponent V f M ψ U e W 0
      GradedMonoid.GOne.one = 1 := by
  show AlgebraicGeometry.Scheme.projBundle.localRingHomComponent V f M ψ U e W 0
    ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).one.app W
      (1 : Γ(X, W))) = 1
  rw [AlgebraicGeometry.Scheme.projBundle.localRingHomComponent_zero_apply]
  exact map_one _

/-! ## (S3) multiplicativity of the sheaf-level pieces `Φ_m` -/

section SheafHomMul

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.projBundle

open CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme.Modules

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- **Multiplicativity of the sheaf-level pieces** (the core of (2/6)):
`g^*(S.mul i j) ≫ Φ_{i+j} = δ_g ≫ (Φ_i ⊗ₘ Φ_j) ≫ (λ_ O_V).hom`, where `Φ_m = localRingHomSheafHom … m` and
`S = Sym(V^∨)`. Chain (see `MulAux.chain_aux`): naturality of `pullbackComp.inv` (E1);
`pullback_map_mul_comp_symGradedPullbackDesc` pulled back along `ι` (E2); `δ_natural` of `ι^*` (E3);
the compatibilities (a) `pullbackMonoidalPow_monoidalPowCat` (E4), (b) `monoidalPowCat_monoidalPowMap` (E5),
(c) `unitPowCollapse_monoidalPowCat` (E6) from `ProjectiveBundleUniversalPropertyMonoidalPow`;
`pullbackComp_hom_app_pullbackTensorObjHom` in inverse form (E7, `MulAux.inv_comp_δ_aux`). -/
theorem pullback_map_mul_comp_localRingHomSheafHom (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (ψ : (Modules.pullback f).obj (dual V) ⟶ M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) (i j : ℕ) :
    (Modules.pullback (localRingHomBase f U W)).map ((symGradedAlgebra (dual V)).mul i j) ≫
        localRingHomSheafHom V f M ψ U e W (i + j) =
      pullbackTensorObjHom (localRingHomBase f U W) ((symGradedAlgebra (dual V)).part i)
          ((symGradedAlgebra (dual V)).part j) ≫
        (localRingHomSheafHom V f M ψ U e W i ⊗ₘ localRingHomSheafHom V f M ψ U e W j) ≫
        (λ_ (𝟙_ (U ⊓ f ⁻¹ᵁ W).toScheme.Modules)).hom := by
  have hq : (dual V).IsQuasicoherent :=
    haveI := isLocallyFree_dual' V
    isQuasicoherent_of_isLocallyFree _
  unfold localRingHomSheafHom localRingHomBase
  have E1 : (Modules.pullback (localRingHomIncl f U W ≫ f)).map ((symGradedAlgebra (dual V)).mul i j) ≫
        (pullbackComp (localRingHomIncl f U W) f).inv.app ((symGradedAlgebra (dual V)).part (i + j)) =
      (pullbackComp (localRingHomIncl f U W) f).inv.app
          ((symGradedAlgebra (dual V)).part i ⊗ (symGradedAlgebra (dual V)).part j) ≫
        (Modules.pullback (localRingHomIncl f U W)).map
          ((Modules.pullback f).map ((symGradedAlgebra (dual V)).mul i j)) :=
    (pullbackComp (localRingHomIncl f U W) f).inv.naturality _
  have E2 : (Modules.pullback (localRingHomIncl f U W)).map
          ((Modules.pullback f).map ((symGradedAlgebra (dual V)).mul i j)) ≫
        (Modules.pullback (localRingHomIncl f U W)).map (symGradedPullbackDesc f ψ (i + j)) =
      (Modules.pullback (localRingHomIncl f U W)).map
          (pullbackTensorObjHom f ((symGradedAlgebra (dual V)).part i) ((symGradedAlgebra (dual V)).part j)) ≫
        (Modules.pullback (localRingHomIncl f U W)).map
          (symGradedPullbackDesc f ψ i ⊗ₘ symGradedPullbackDesc f ψ j) ≫
        (Modules.pullback (localRingHomIncl f U W)).map (monoidalPowCat M i j).hom := by
    rw [← Functor.map_comp, pullback_map_mul_comp_symGradedPullbackDesc f _ hq ψ, Functor.map_comp,
      Functor.map_comp]
  have E3 : (Modules.pullback (localRingHomIncl f U W)).map
          (symGradedPullbackDesc f ψ i ⊗ₘ symGradedPullbackDesc f ψ j) ≫
        pullbackTensorObjHom (localRingHomIncl f U W) (monoidalPow M i) (monoidalPow M j) =
      pullbackTensorObjHom (localRingHomIncl f U W)
          ((Modules.pullback f).obj ((symGradedAlgebra (dual V)).part i))
          ((Modules.pullback f).obj ((symGradedAlgebra (dual V)).part j)) ≫
        ((Modules.pullback (localRingHomIncl f U W)).map (symGradedPullbackDesc f ψ i) ⊗ₘ
          (Modules.pullback (localRingHomIncl f U W)).map (symGradedPullbackDesc f ψ j)) :=
    (Functor.OplaxMonoidal.δ_natural (Modules.pullback (localRingHomIncl f U W)) _ _).symm
  have E4 := pullbackMonoidalPow_monoidalPowCat (localRingHomIncl f U W) M i j
  have E5 := (monoidalPowCat_monoidalPowMap (localRingHomTriv f M U e W).hom i j).symm
  have E6 := unitPowCollapse_monoidalPowCat (U ⊓ f ⁻¹ᵁ W).toScheme i j
  have E7 : (pullbackComp (localRingHomIncl f U W) f).inv.app
          ((symGradedAlgebra (dual V)).part i ⊗ (symGradedAlgebra (dual V)).part j) ≫
        (Modules.pullback (localRingHomIncl f U W)).map
          (pullbackTensorObjHom f ((symGradedAlgebra (dual V)).part i) ((symGradedAlgebra (dual V)).part j)) ≫
        pullbackTensorObjHom (localRingHomIncl f U W)
          ((Modules.pullback f).obj ((symGradedAlgebra (dual V)).part i))
          ((Modules.pullback f).obj ((symGradedAlgebra (dual V)).part j)) =
      pullbackTensorObjHom (localRingHomIncl f U W ≫ f) ((symGradedAlgebra (dual V)).part i)
          ((symGradedAlgebra (dual V)).part j) ≫
        ((pullbackComp (localRingHomIncl f U W) f).inv.app ((symGradedAlgebra (dual V)).part i) ⊗ₘ
          (pullbackComp (localRingHomIncl f U W) f).inv.app ((symGradedAlgebra (dual V)).part j)) :=
    MulAux.inv_comp_δ_aux _ _ (Iso.inv_hom_id_app _ _) _ _ (Iso.hom_inv_id_app _ _) _ _
      (Iso.hom_inv_id_app _ _) _ _ _
      (pullbackComp_hom_app_pullbackTensorObjHom (localRingHomIncl f U W) f _ _)
  exact MulAux.chain_aux _ _ _ _ _ _ E1 _ _ _ _ E2 _ _ _ _ E3 _ _ _ _ E4 _ _ _ _ E5 _ _ _ _ E6 _ E7

end AlgebraicGeometry.Scheme.projBundle

end SheafHomMul

set_option backward.isDefEq.respectTransparency.types false in
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.projBundle CategoryTheory.MonoidalCategory in
/-- **(2/6) The components are multiplicative**: `comp_{i+j}(s·t) = comp_i(s)·comp_j(t)` (the second
hypothesis of `DirectSum.toSemiring`).

Reference: Stacks 01O4 / 01N8 (graded maps preserve multiplication).

Proof sketch.
1. The multiplication of `Sym` is compatible with the descent of `ψ`
   (`pullback_map_mul_comp_symGradedPullbackDesc`):
   `f^*(symPowMul (dual V) i j) ≫ symPowPullbackDesc f ψ (i+j) = pullbackTensorObjHom f (Sym^i) (Sym^j) ≫ (symPowPullbackDesc f ψ i ⊗ symPowPullbackDesc f ψ j) ≫ (monoidalPowCat M i j).hom`.
   Take adjoint transposes (`homEquiv` is injective), cancel the epimorphism `π_i ⊗ π_j`
   (`symPowπ_tensorHom_cancel`), and chain `tensorHom_symPowπ_symPowMul`,
   `pullback_map_symPowπ_comp_symPowPullbackDesc` and the compatibilities (a), (b) of
   `ProjectiveBundleUniversalPropertyMonoidalPow`.
2. The remaining levels are compatible with multiplication
   (`pullback_map_mul_comp_localRingHomSheafHom`): `pullbackComp`, the monoidal functor `(V→T)^*`,
   `monoidalPowMap e'.hom`, `unitPowCollapse`, chained by `MulAux.chain_aux` (the identities E1–E7); the
   last segment `O^{⊗i} ⊗ O^{⊗j} → O ⊗ O → O` is the multiplication of `Γ(V, O)`
   (`MonoidalCategory.unitors_equal`).
3. Translation to sections: `app_top_map_unit_app_eq` writes the three components as "the transpose
   `φ_m = homEquiv Φ_m` evaluated on `W`, then restricted to `⊤`";
   `S.mul ≫ φ_{i+j} = (φ_i ⊗ φ_j) ≫ pushforwardUnitMul g` (transpose of step 2 and
   `tensorHom_homEquiv_pushforwardUnitMul`), evaluated on `tensorSections ai aj` via
   `tensorHom_tensorSections` and `pushforwardUnitMul_val_app_tensorSections` (the multiplication of
   `Γ(g⁻¹W, O)`); finally the restriction map is a ring homomorphism (`map_mul`). -/
theorem AlgebraicGeometry.Scheme.projBundle.localRingHomComponent_mul {X T : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) {i j : ℕ}
    (ai : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsPiece W i)
    (aj : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsPiece W j) :
    AlgebraicGeometry.Scheme.projBundle.localRingHomComponent V f M ψ U e W (i + j)
        (GradedMonoid.GMul.mul ai aj) =
      AlgebraicGeometry.Scheme.projBundle.localRingHomComponent V f M ψ U e W i ai *
        AlgebraicGeometry.Scheme.projBundle.localRingHomComponent V f M ψ U e W j aj := by
  have hmul : (GradedMonoid.GMul.mul ai aj : (symGradedAlgebra (dual V)).sectionsPiece W (i + j)) =
      (((symGradedAlgebra (dual V)).mul i j).val.app (op W)).hom
        (tensorSections ((symGradedAlgebra (dual V)).part i) ((symGradedAlgebra (dual V)).part j) W ai aj) :=
    rfl
  have key : (symGradedAlgebra (dual V)).mul i j ≫
        (pullbackPushforwardAdjunction (localRingHomBase f U W)).homEquiv _ _
          (localRingHomSheafHom V f M ψ U e W (i + j)) =
      ((pullbackPushforwardAdjunction (localRingHomBase f U W)).homEquiv _ _
          (localRingHomSheafHom V f M ψ U e W i) ⊗ₘ
        (pullbackPushforwardAdjunction (localRingHomBase f U W)).homEquiv _ _
          (localRingHomSheafHom V f M ψ U e W j)) ≫ pushforwardUnitMul (localRingHomBase f U W) := by
    rw [← Adjunction.homEquiv_naturality_left, pullback_map_mul_comp_localRingHomSheafHom]
    exact (tensorHom_homEquiv_pushforwardUnitMul _ _ _).symm
  rw [localRingHomComponent_apply, localRingHomComponent_apply, localRingHomComponent_apply,
    app_top_map_unit_app_eq, app_top_map_unit_app_eq, app_top_map_unit_app_eq, hmul]
  have h2 : (((pullbackPushforwardAdjunction (localRingHomBase f U W)).homEquiv _ _
        (localRingHomSheafHom V f M ψ U e W (i + j))).val.app (op W)).hom
        ((((symGradedAlgebra (dual V)).mul i j).val.app (op W)).hom
          (tensorSections ((symGradedAlgebra (dual V)).part i) ((symGradedAlgebra (dual V)).part j) W ai aj)) =
      (show Γ((U ⊓ f ⁻¹ᵁ W).toScheme, localRingHomBase f U W ⁻¹ᵁ W) from
          (((pullbackPushforwardAdjunction (localRingHomBase f U W)).homEquiv _ _
            (localRingHomSheafHom V f M ψ U e W i)).val.app (op W)).hom ai) *
        (show Γ((U ⊓ f ⁻¹ᵁ W).toScheme, localRingHomBase f U W ⁻¹ᵁ W) from
          (((pullbackPushforwardAdjunction (localRingHomBase f U W)).homEquiv _ _
            (localRingHomSheafHom V f M ψ U e W j)).val.app (op W)).hom aj) := by
    have h3 := congrArg (fun k => (k.val.app (op W)).hom
      (tensorSections ((symGradedAlgebra (dual V)).part i) ((symGradedAlgebra (dual V)).part j) W ai aj)) key
    refine Eq.trans h3 ?_
    show ((pushforwardUnitMul (localRingHomBase f U W)).val.app (op W)).hom
      ((((pullbackPushforwardAdjunction (localRingHomBase f U W)).homEquiv _ _
          (localRingHomSheafHom V f M ψ U e W i) ⊗ₘ
        (pullbackPushforwardAdjunction (localRingHomBase f U W)).homEquiv _ _
          (localRingHomSheafHom V f M ψ U e W j)).val.app (op W)).hom
        (tensorSections ((symGradedAlgebra (dual V)).part i) ((symGradedAlgebra (dual V)).part j) W ai aj)) = _
    rw [tensorHom_tensorSections]
    exact pushforwardUnitMul_val_app_tensorSections (localRingHomBase f U W) W _ _
  rw [h2]
  exact map_mul ((U ⊓ f ⁻¹ᵁ W).toScheme.presheaf.map (homOfLE (localRingHomBase_top_le f U W)).op).hom _ _


/-- The local ring homomorphism (a local piece of the lift): the components `localRingHomComponent`
assembled into a ring homomorphism on `A(W) = ⊕_m Γ(W, S_m)` (`DirectSum.toSemiring`).
The hypotheses `[V.IsLocallyFree] [V.IsFiniteType] [M.IsLineBundle]` are needed: if `V^∨` is not
quasi-coherent, `symGradedAlgebra` is the trivial graded algebra and `symGradedPullbackDesc` the zero
morphism, so the degree-zero component is `0` and unitality reads `0 = 1` (false when `U ⊓ f⁻¹W` is
nonempty); if `M` is not a line bundle, the transposition invariance of `symPowPullbackDesc` fails
(`M = O ⊕ O`). -/

noncomputable def AlgebraicGeometry.Scheme.projBundle.localRingHom {X T : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsRing W →+*
      Γ((U ⊓ f ⁻¹ᵁ W).toScheme, ⊤) :=
  DirectSum.toSemiring (AlgebraicGeometry.Scheme.projBundle.localRingHomComponent V f M ψ U e W)
    (AlgebraicGeometry.Scheme.projBundle.localRingHomComponent_one V f M ψ U e W)
    (fun ai aj => AlgebraicGeometry.Scheme.projBundle.localRingHomComponent_mul V f M ψ U e W ai aj)


end
