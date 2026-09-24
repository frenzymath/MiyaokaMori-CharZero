import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaUniversalDerivation
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentials
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaOpenImmersionSquare
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.OmegaSpecTilde
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentOfRestrictPresentation

/-! # Affine sections and quasi-coherence of `Ω_{X/S}`

For affine opens `U = Spec A ⊆ f⁻¹(V)`, `V = Spec R`, there is a unique isomorphism
`Γ(U, Ω_{X/S}) ≅ Ω_{A/R}` compatible with `d` (Stacks 01UT), and it is compatible with the
restriction maps; hence `Ω_{X/S}` is quasi-coherent (on `U` it is the tilde of `Ω_{A/R}`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped AlgebraicGeometry

/- The universal derivation `d_{X/S} : O_X → Ω_{X/S}`: the derivation corresponding to the identity
under `Omega.homEquivDerivation`. -/

noncomputable def AlgebraicGeometry.Omega.universalDerivation {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) :
    ((AlgebraicGeometry.Omega f).val).Derivation' (AlgebraicGeometry.Scheme.inverseImageStructureMap f) :=
  AlgebraicGeometry.Omega.homEquivDerivation f (AlgebraicGeometry.Omega f) (CategoryTheory.CategoryStruct.id _)

/-- The derivation `d_U : Γ(X, U) → Γ(U, Ω_{X/S})` on an affine pair `U ⊆ f⁻¹V`; it is
`Γ(S, V)`-linear because `d` kills the image of `f⁻¹O_S`, through which `f.appLE` factors. -/

noncomputable def AlgebraicGeometry.Omega_appDerivation {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    (V : S.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) :
    letI := (f.appLE V U e).hom.toAlgebra
    letI : Module Γ(S, V) Γ(AlgebraicGeometry.Omega f, U) := Module.compHom _ (f.appLE V U e).hom
    Derivation Γ(S, V) Γ(X, U) Γ(AlgebraicGeometry.Omega f, U) :=
  letI := (f.appLE V U e).hom.toAlgebra
  letI : Module Γ(S, V) Γ(AlgebraicGeometry.Omega f, U) := Module.compHom _ (f.appLE V U e).hom
  { toFun := fun a => (AlgebraicGeometry.Omega.universalDerivation f).d (X := Opposite.op U) a
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r a => by
      have h := (AlgebraicGeometry.Omega.universalDerivation f).d_mul (X := Opposite.op U)
        ((f.appLE V U e).hom r) a
      have h0 := AlgebraicGeometry.Omega.derivation_appLE f
        (AlgebraicGeometry.Omega.universalDerivation f) V U e r
      refine h.trans ?_
      rw [h0]
      erw [smul_zero, add_zero]
      rfl
    map_one_eq_zero' := (AlgebraicGeometry.Omega.universalDerivation f).d_one _
    leibniz' := fun a b =>
      (AlgebraicGeometry.Omega.universalDerivation f).d_mul (X := Opposite.op U) a b }

/-- The comparison map `Ω_{Γ(X,U)/Γ(S,V)} → Γ(U, Ω_{X/S})`, `d a ↦ d_U a` (universal property of
Kähler differentials). -/

noncomputable def AlgebraicGeometry.Omega_appHom {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    (V : S.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) :
    letI := (f.appLE V U e).hom.toAlgebra
    Ω[Γ(X, U)⁄Γ(S, V)] →ₗ[Γ(X, U)] Γ(AlgebraicGeometry.Omega f, U) :=
  letI := (f.appLE V U e).hom.toAlgebra
  letI : Module Γ(S, V) Γ(AlgebraicGeometry.Omega f, U) := Module.compHom _ (f.appLE V U e).hom
  haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(AlgebraicGeometry.Omega f, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  (AlgebraicGeometry.Omega_appDerivation f V U e).liftKaehlerDifferential

/-- The comparison map on generators: `d a ↦ d_U a`. -/

theorem AlgebraicGeometry.Omega_appHom_D {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    (V : S.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) (a : Γ(X, U)) :
    letI := (f.appLE V U e).hom.toAlgebra
    AlgebraicGeometry.Omega_appHom f V U e (KaehlerDifferential.D Γ(S, V) Γ(X, U) a) =
      (AlgebraicGeometry.Omega.universalDerivation f).d (X := Opposite.op U) a := by
  let _ := (f.appLE V U e).hom.toAlgebra
  let _ : Module Γ(S, V) Γ(AlgebraicGeometry.Omega f, U) := Module.compHom _ (f.appLE V U e).hom
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(AlgebraicGeometry.Omega f, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (AlgebraicGeometry.Omega_appDerivation f V U e).liftKaehlerDifferential_comp_D a

/-- Stacks 01UT: for affine `U`, `V` the comparison map is bijective. -/

theorem AlgebraicGeometry.Omega_appHom_bijective {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    {V : S.Opens} (hV : AlgebraicGeometry.IsAffineOpen V) {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) :
    Function.Bijective (AlgebraicGeometry.Omega_appHom f V U e) := by
  let _ := (f.appLE V U e).hom.toAlgebra
  have w := AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e
  have hg : hU.fromSpec ''ᵁ ⊤ = U := by
    rw [AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  -- θ̃_U : Γ(U, Ω_{X/S}) → Γ(fromSpec⁻¹U, Ω_{Spec A/Spec R}) is bijective
  have hθ : Function.Bijective ((AlgebraicGeometry.Omega.squareToPushforward f
      (AlgebraicGeometry.Spec.map (f.appLE V U e)) hU.fromSpec hV.fromSpec w).app U) := by
    have := AlgebraicGeometry.Omega.squareToPushforward_app_bijective f
      (AlgebraicGeometry.Spec.map (f.appLE V U e)) hU.fromSpec hV.fromSpec w ⊤
    rw [hg] at this
    exact this
  have hρ : Function.Bijective ((AlgebraicGeometry.Omega (AlgebraicGeometry.Spec.map
      (f.appLE V U e))).presheaf.map (eqToHom hU.fromSpec_preimage_self.symm).op) := by
    have : IsIso ((AlgebraicGeometry.Omega (AlgebraicGeometry.Spec.map
      (f.appLE V U e))).presheaf.map (eqToHom hU.fromSpec_preimage_self.symm).op) :=
      Functor.map_isIso _ _
    exact ConcreteCategory.bijective_of_isIso _
  -- ring elements: fromSpec^♯(c) restricted back to ⊤ is the global section corresponding to c
  have hring : ∀ c : Γ(X, U), (AlgebraicGeometry.Spec Γ(X, U)).presheaf.map
      (eqToHom hU.fromSpec_preimage_self.symm).op ((hU.fromSpec.app U).hom c) =
      (AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U)).inv.hom c := by
    intro c
    have h1 := hU.fromSpec_app_self_apply c
    have h2 : (AlgebraicGeometry.Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op ≫
        (AlgebraicGeometry.Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self.symm).op =
        𝟙 _ := by
      rw [← CategoryTheory.Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id,
        CategoryTheory.Functor.map_id]
    refine (congrArg ((AlgebraicGeometry.Spec Γ(X, U)).presheaf.map
      (eqToHom hU.fromSpec_preimage_self.symm).op).hom h1).trans ?_
    exact congrArg (fun t => t.hom ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U)).inv.hom c)) h2
  let Φ : Ω[Γ(X, U)⁄Γ(S, V)] →+
      Γ(AlgebraicGeometry.Omega (AlgebraicGeometry.Spec.map (f.appLE V U e)), ⊤) :=
    (((AlgebraicGeometry.Omega (AlgebraicGeometry.Spec.map (f.appLE V U e))).presheaf.map
        (eqToHom hU.fromSpec_preimage_self.symm).op).hom.comp
      ((AlgebraicGeometry.Omega.squareToPushforward f
        (AlgebraicGeometry.Spec.map (f.appLE V U e)) hU.fromSpec hV.fromSpec w).app U).hom).comp
      (AlgebraicGeometry.Omega_appHom f V U e).toAddMonoidHom
  let Ψ : Ω[Γ(X, U)⁄Γ(S, V)] →+
      Γ(AlgebraicGeometry.Omega (AlgebraicGeometry.Spec.map (f.appLE V U e)), ⊤) :=
    (AlgebraicGeometry.Omega.specKaehlerToΓ (f.appLE V U e)).hom.toAddMonoidHom
  have key : ∀ y : Ω[Γ(X, U)⁄Γ(S, V)], Φ y = Ψ y := by
    intro y
    have hy : y ∈ Submodule.span Γ(X, U) (Set.range (KaehlerDifferential.D Γ(S, V) Γ(X, U))) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      have s1 := AlgebraicGeometry.Omega_appHom_D f V U e a
      have s2 := AlgebraicGeometry.Omega.squareToPushforward_app_d f
        (AlgebraicGeometry.Spec.map (f.appLE V U e)) hU.fromSpec hV.fromSpec w U a
      have s3 := (AlgebraicGeometry.Omega.homEquivDerivation (AlgebraicGeometry.Spec.map (f.appLE V U e))
        _ (𝟙 _)).d_map (eqToHom hU.fromSpec_preimage_self.symm).op ((hU.fromSpec.app U).hom a)
      have s5 := AlgebraicGeometry.Omega.specKaehlerToΓ_d (f.appLE V U e) a
      refine Eq.trans ?_ s5.symm
      refine Eq.trans ?_ (congrArg _ (hring a))
      refine Eq.trans ?_ s3.symm
      refine Eq.trans ?_ (congrArg _ s2)
      exact congrArg (fun t => ((AlgebraicGeometry.Omega (AlgebraicGeometry.Spec.map
        (f.appLE V U e))).presheaf.map (eqToHom hU.fromSpec_preimage_self.symm).op).hom
          (((AlgebraicGeometry.Omega.squareToPushforward f (AlgebraicGeometry.Spec.map
            (f.appLE V U e)) hU.fromSpec hV.fromSpec w).app U).hom t)) s1
    | zero => rw [map_zero, map_zero]
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
    | smul c y _ hy =>
      have t1 : AlgebraicGeometry.Omega_appHom f V U e (c • y) =
          c • AlgebraicGeometry.Omega_appHom f V U e y := map_smul _ c y
      have t2 := AlgebraicGeometry.Scheme.Modules.Hom.app_smul
        (AlgebraicGeometry.Omega.squareToPushforward f (AlgebraicGeometry.Spec.map (f.appLE V U e))
          hU.fromSpec hV.fromSpec w) c (AlgebraicGeometry.Omega_appHom f V U e y)
      have t3 := AlgebraicGeometry.Scheme.Modules.map_smul
        (AlgebraicGeometry.Omega (AlgebraicGeometry.Spec.map (f.appLE V U e)))
        (eqToHom hU.fromSpec_preimage_self.symm) ((hU.fromSpec.app U).hom c)
        ((AlgebraicGeometry.Omega.squareToPushforward f (AlgebraicGeometry.Spec.map (f.appLE V U e))
          hU.fromSpec hV.fromSpec w).app U (AlgebraicGeometry.Omega_appHom f V U e y))
      have t4 : Ψ (c • y) = c • Ψ y :=
        (AlgebraicGeometry.Omega.specKaehlerToΓ (f.appLE V U e)).hom.map_smul c y
      have t5 := AlgebraicGeometry.Omega.smul_Spec_top
        (AlgebraicGeometry.Omega (AlgebraicGeometry.Spec.map (f.appLE V U e))) c (Ψ y)
      refine Eq.trans ?_ (t4.trans t5).symm
      rw [← hy, ← hring c]
      refine Eq.trans ?_ t3
      exact congrArg ((AlgebraicGeometry.Omega (AlgebraicGeometry.Spec.map
        (f.appLE V U e))).presheaf.map (eqToHom hU.fromSpec_preimage_self.symm).op).hom
          ((congrArg ((AlgebraicGeometry.Omega.squareToPushforward f (AlgebraicGeometry.Spec.map
            (f.appLE V U e)) hU.fromSpec hV.fromSpec w).app U).hom t1).trans t2)
  have hcomp : Function.Bijective (fun y => (AlgebraicGeometry.Omega (AlgebraicGeometry.Spec.map
      (f.appLE V U e))).presheaf.map (eqToHom hU.fromSpec_preimage_self.symm).op
        ((AlgebraicGeometry.Omega.squareToPushforward f
          (AlgebraicGeometry.Spec.map (f.appLE V U e)) hU.fromSpec hV.fromSpec w).app U
          (AlgebraicGeometry.Omega_appHom f V U e y))) := by
    refine (funext key : (fun y => _) = (Ψ : _ → _)) ▸ ?_
    exact AlgebraicGeometry.Omega.specKaehlerToΓ_bijective (f.appLE V U e)
  exact (Function.Bijective.of_comp_iff' (hρ.comp hθ) _).mp hcomp

/-- Stacks 01UT: the isomorphism `Γ(U, Ω_{X/S}) ≅ Ω_{Γ(X,U)/Γ(S,V)}` for affine `U ⊆ f⁻¹V`; the
algebra structure `Γ(S, V) → Γ(X, U)` is `f.appLE V U e`, and the isomorphism is
`Γ(X, U)`-linear. -/

noncomputable def AlgebraicGeometry.Omega_appIso {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    {V : S.Opens} (hV : AlgebraicGeometry.IsAffineOpen V) {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) :
    letI := (f.appLE V U e).hom.toAlgebra
    Γ(AlgebraicGeometry.Omega f, U) ≃ₗ[Γ(X, U)] Ω[Γ(X, U)⁄Γ(S, V)] :=
  letI := (f.appLE V U e).hom.toAlgebra
  (LinearEquiv.ofBijective (AlgebraicGeometry.Omega_appHom f V U e)
    (AlgebraicGeometry.Omega_appHom_bijective f hV hU e)).symm

/-- Compatibility with `d` (the characterization of 01UT, which determines `appIso`):
`appIso (d_U a) = d a`. -/

theorem AlgebraicGeometry.Omega_appIso_d {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    {V : S.Opens} (hV : AlgebraicGeometry.IsAffineOpen V) {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) (a : Γ(X, U)) :
    letI := (f.appLE V U e).hom.toAlgebra
    AlgebraicGeometry.Omega_appIso f hV hU e
        ((AlgebraicGeometry.Omega.universalDerivation f).d (X := Opposite.op U) a) =
      KaehlerDifferential.D Γ(S, V) Γ(X, U) a := by
  let _ := (f.appLE V U e).hom.toAlgebra
  let _ : Module Γ(S, V) Γ(AlgebraicGeometry.Omega f, U) := Module.compHom _ (f.appLE V U e).hom
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(AlgebraicGeometry.Omega f, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have h : AlgebraicGeometry.Omega_appHom f V U e (KaehlerDifferential.D Γ(S, V) Γ(X, U) a) =
      (AlgebraicGeometry.Omega.universalDerivation f).d (X := Opposite.op U) a :=
    (AlgebraicGeometry.Omega_appDerivation f V U e).liftKaehlerDifferential_comp_D a
  rw [← h]
  exact (LinearEquiv.ofBijective (AlgebraicGeometry.Omega_appHom f V U e)
    (AlgebraicGeometry.Omega_appHom_bijective f hV hU e)).symm_apply_apply _

/-- Compatibility with restriction: for affine opens `U' ⊆ U` in `f⁻¹V`, restriction corresponds
to the functorial map of Kähler differentials. -/

theorem AlgebraicGeometry.Omega_appIso_restrict {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    {V : S.Opens} (hV : AlgebraicGeometry.IsAffineOpen V) {U U' : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) (hU' : AlgebraicGeometry.IsAffineOpen U')
    (e : U ≤ f ⁻¹ᵁ V) (h : U' ≤ U) (x : Γ(AlgebraicGeometry.Omega f, U)) :
    letI := (f.appLE V U e).hom.toAlgebra
    letI := (f.appLE V U' (h.trans e)).hom.toAlgebra
    letI := (X.presheaf.map (CategoryTheory.homOfLE h).op).hom.toAlgebra
    haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(X, U') :=
      IsScalarTower.of_algebraMap_eq'
        (congrArg CommRingCat.Hom.hom (f.appLE_map e (CategoryTheory.homOfLE h).op)).symm;
    AlgebraicGeometry.Omega_appIso f hV hU' (h.trans e)
        ((AlgebraicGeometry.Omega f).presheaf.map (CategoryTheory.homOfLE h).op x) =
      KaehlerDifferential.map Γ(S, V) Γ(S, V) Γ(X, U) Γ(X, U')
        (AlgebraicGeometry.Omega_appIso f hV hU e x) := by
  let _ := (f.appLE V U e).hom.toAlgebra
  let _ := (f.appLE V U' (h.trans e)).hom.toAlgebra
  let _ := (X.presheaf.map (CategoryTheory.homOfLE h).op).hom.toAlgebra
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(X, U') :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (f.appLE_map e (CategoryTheory.homOfLE h).op)).symm
  have key : ∀ y : Ω[Γ(X, U)⁄Γ(S, V)],
      (AlgebraicGeometry.Omega f).presheaf.map (CategoryTheory.homOfLE h).op
          (AlgebraicGeometry.Omega_appHom f V U e y) =
        AlgebraicGeometry.Omega_appHom f V U' (h.trans e)
          (KaehlerDifferential.map Γ(S, V) Γ(S, V) Γ(X, U) Γ(X, U') y) := by
    intro y
    have hy : y ∈ Submodule.span Γ(X, U) (Set.range (KaehlerDifferential.D Γ(S, V) Γ(X, U))) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      rw [KaehlerDifferential.map_D, AlgebraicGeometry.Omega_appHom_D,
        AlgebraicGeometry.Omega_appHom_D]
      exact ((AlgebraicGeometry.Omega.universalDerivation f).d_map
        (CategoryTheory.homOfLE h).op a).symm
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, hy, hz]
    | smul c y _ hy =>
      rw [map_smul, AlgebraicGeometry.Scheme.Modules.map_smul, hy,
        map_smul (KaehlerDifferential.map Γ(S, V) Γ(S, V) Γ(X, U) Γ(X, U')),
        ← algebraMap_smul Γ(X, U') c, map_smul]
      rfl
  obtain ⟨y, rfl⟩ := (AlgebraicGeometry.Omega_appHom_bijective f hV hU e).2 x
  rw [key]
  have h1 : AlgebraicGeometry.Omega_appIso f hV hU e (AlgebraicGeometry.Omega_appHom f V U e y) = y :=
    (LinearEquiv.ofBijective (AlgebraicGeometry.Omega_appHom f V U e)
      (AlgebraicGeometry.Omega_appHom_bijective f hV hU e)).symm_apply_apply y
  rw [h1]
  exact (LinearEquiv.ofBijective (AlgebraicGeometry.Omega_appHom f V U' (h.trans e))
    (AlgebraicGeometry.Omega_appHom_bijective f hV hU' (h.trans e))).symm_apply_apply _

theorem AlgebraicGeometry.Omega_isQuasicoherent {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) :
    (AlgebraicGeometry.Omega f).IsQuasicoherent := by
  apply AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_restrict_presentation
  intro x
  obtain ⟨_, ⟨V, hV : AlgebraicGeometry.IsAffineOpen V, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU : AlgebraicGeometry.IsAffineOpen U, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).isOpen
  have e : U ≤ f ⁻¹ᵁ V := hUV
  refine ⟨_, hU.fromSpec, inferInstance, ?_, ⟨?_⟩⟩
  · rw [hU.range_fromSpec]; exact hxU
  · let i := AlgebraicGeometry.Omega.restrictIso f (AlgebraicGeometry.Spec.map (f.appLE V U e))
      hU.fromSpec hV.fromSpec (AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e)
    let j := AlgebraicGeometry.Omega.specTildeIso (f.appLE V U e)
    have hj : IsIso (C := SheafOfModules.{u} (AlgebraicGeometry.Spec Γ(X, U)).ringCatSheaf) j.hom :=
      ⟨j.inv, j.hom_inv_id, j.inv_hom_id⟩
    have hi : IsIso (C := SheafOfModules.{u} (AlgebraicGeometry.Spec Γ(X, U)).ringCatSheaf) i.inv :=
      ⟨i.hom, i.inv_hom_id, i.hom_inv_id⟩
    exact ((AlgebraicGeometry.presentationTilde _ Set.univ (by simp) _
      (Submodule.span_eq _)).ofIsIso j.hom).ofIsIso i.inv

end
