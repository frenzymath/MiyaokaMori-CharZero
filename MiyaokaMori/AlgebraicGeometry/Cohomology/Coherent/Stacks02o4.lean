import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOver
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesIsoTransport
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.FiniteTypeOfFiniteAffineSections
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.FlatFamilyRestrictAffineBase
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyZeroEquiv
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.ClosedSubschemeProjectiveSpaceCohomologyFinite
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphismAffineLocalClosedImmersion
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01wc
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01lc

/-! # Coherence of the higher direct images of a projective morphism (Stacks 02O4)

Stacks 02O4 (projective case): `S` locally Noetherian, `f` projective, `F` coherent ⇒ `R^i f_*F` is
coherent; stated in affine-local form: for every affine open `V` of `S`, `H^i(f⁻¹V, F)` is a finite
`Γ(S, V)`-module; for `i = 0`, `f_*F` is coherent.

Source: Stacks 02O4 (coherent-lemma-locally-projective-pushforward); Hartshorne III.8.8(b).

Route (Stacks 02O4, proof):
1. *Reduce to a closed subscheme of `P^n_R`, `R := Γ(S, V)`*
   (`IsProjectiveMorphism.exists_closedImmersion_projectiveSpaceOver`): a closed immersion
   `j : f⁻¹V → P^n_R = ProjectiveSpaceOver n R` with
   `j ≫ ProjectiveSpaceOver.toSpecBase n R = (f ∣_ V) ≫ isoSpec`.
2. *Finiteness for closed subschemes of `P^n_R`*
   (`finite_sheafCohomology_of_isClosedImmersion_projectiveSpaceOver`; = Stacks 0B5T(3) / Hartshorne III.5.2(a),
   itself assembled from 01Y6, 02UV and Stacks 01YS(3) over a Noetherian ring). `R` is Noetherian because
   `S` is locally Noetherian and `V` affine.
3. *Module structures agree*: the `R`-structure of step 2 is `sheafCohomology.moduleOver` for `f⁻¹V → P^n_R → Spec R`
   `= (f ∣_ V) ≫ isoSpec`, i.e. scalars restricted along `R ≅ Γ(Spec R, ⊤) → Γ(V, ⊤) → Γ(f⁻¹V, ⊤)`; the statement's
   structure restricts along `f.app V : Γ(S, V) → Γ(X, f⁻¹V) ≅ Γ(f⁻¹V, ⊤)`. These ring maps are equal
   (`isoSpec_hom_appTop`, `morphismRestrict_appTop`, naturality of `f.app`), so `Module.Finite` transports.
4. *`i = 0` ⇒ `f_*F` coherent*: `f_*F` is quasi-coherent (Stacks 01LC; `f` is proper by Stacks 01WC,
   hence qcqs); a quasi-coherent module with finite sections on an affine open neighbourhood of every
   point is of finite type (`isFiniteType_of_finite_affine_sections`); and
   `Γ(f_*F, V) = Γ(F, f⁻¹V) ≅ H^0(f⁻¹V, F|_{f⁻¹V})` `Γ(S, V)`-linearly (`sheafCohomologyZeroEquiv`, plus
   the restriction along `(f⁻¹V).ι ''ᵁ ⊤ = f⁻¹V`), so the first theorem at `i = 0` gives the finiteness.

Why not through 02O6/02O5 (proper case): the dévissage generator of 02O6 *uses* this result (Stacks'
proof of 02O5 has 02O4 as its base case), so that route would be circular.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Transport of `Module.Finite` along an equality of the ring homomorphisms defining two
`Module.compHom` structures on the same module. -/
private theorem finite_compHom_congr {R T : Type*} [CommRing R] [CommRing T] {H : Type*}
    [AddCommGroup H] [Module T H] {φ ψ : R →+* T} (h : φ = ψ)
    (hφ : @Module.Finite R H _ _ (Module.compHom H φ)) :
    @Module.Finite R H _ _ (Module.compHom H ψ) :=
  h ▸ hφ

/-- Stacks 02O4 (projective case): `S` locally Noetherian, `f` projective, `F` coherent ⇒ `R^i f_*F`
coherent, in affine-local form: for every affine open `V` of `S`, `H^i(f⁻¹V, F)` is a finite
`Γ(S, V)`-module via `Γ(S, V) → Γ(f⁻¹V, ⊤)` (since `S` is locally Noetherian, `R^i f_*F` is
quasi-coherent and `Γ(V, R^i f_*F) = H^i(f⁻¹V, F)` (Stacks 01XK), this is equivalent to coherence).
The case `i = 0` is restated as coherence of the pushforward below. -/

theorem AlgebraicGeometry.finite_sheafCohomology_restrict_of_isProjectiveMorphism
    {X S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    (f : X ⟶ S) [AlgebraicGeometry.IsProjectiveMorphism f] (F : X.Modules) [F.IsCoherent]
    (V : S.affineOpens) (i : ℕ) :
    letI : Module Γ(S, V.1) (AlgebraicGeometry.sheafCohomology (f ⁻¹ᵁ V.1).toScheme
        (AlgebraicGeometry.Scheme.Modules.restrict F (f ⁻¹ᵁ V.1).ι) i) :=
      Module.compHom _ (f.app V.1 ≫ (f ⁻¹ᵁ V.1).topIso.inv).hom
    Module.Finite Γ(S, V.1) (AlgebraicGeometry.sheafCohomology (f ⁻¹ᵁ V.1).toScheme
        (AlgebraicGeometry.Scheme.Modules.restrict F (f ⁻¹ᵁ V.1).ι) i) := by
  obtain ⟨n, j, hj, hcomp⟩ :=
    AlgebraicGeometry.IsProjectiveMorphism.exists_closedImmersion_projectiveSpaceOver f V
  have : IsNoetherianRing Γ(S, V.1) := AlgebraicGeometry.IsLocallyNoetherian.component_noetherian V
  have : F.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
  have hcoh : (AlgebraicGeometry.Scheme.Modules.restrict F (f ⁻¹ᵁ V.1).ι).IsCoherent := by
    have h1 := AlgebraicGeometry.Scheme.Modules.isCoherent_pullback_preimage_ι f F V.1
    let e : AlgebraicGeometry.Scheme.Modules.restrict F (f ⁻¹ᵁ V.1).ι ≅
        (AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V.1).ι).obj F :=
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V.1).ι).app F
    exact ⟨inferInstance, AlgebraicGeometry.Scheme.Modules.isFiniteType_of_iso e.symm h1.finiteType⟩
  have hQ := AlgebraicGeometry.finite_sheafCohomology_of_isClosedImmersion_projectiveSpaceOver j
    (AlgebraicGeometry.Scheme.Modules.restrict F (f ⁻¹ᵁ V.1).ι) i
  refine finite_compHom_congr ?_ hQ
  congr 1
  show (AlgebraicGeometry.Scheme.ΓSpecIso Γ(S, V.1)).inv ≫
      (j ≫ ProjectiveSpaceOver.toSpecBase n Γ(S, V.1)).appTop =
    f.app V.1 ≫ (f ⁻¹ᵁ V.1).topIso.inv
  have hV : AlgebraicGeometry.IsAffineOpen V.1 := V.2
  have e := AlgebraicGeometry.IsAffineOpen.isoSpec_hom_appTop (hU := hV)
  rw [hcomp, AlgebraicGeometry.Scheme.Hom.comp_appTop, e, Category.assoc, Iso.inv_hom_id_assoc,
    ← AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict, AlgebraicGeometry.Scheme.Hom.appTop,
    AlgebraicGeometry.Scheme.Hom.resLE_app_top, Iso.inv_hom_id_assoc,
    AlgebraicGeometry.Scheme.Hom.app_eq_appLE]

theorem AlgebraicGeometry.pushforward_isCoherent_of_isProjectiveMorphism
    {X S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    (f : X ⟶ S) [AlgebraicGeometry.IsProjectiveMorphism f] (F : X.Modules) [F.IsCoherent] :
    ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj F).IsCoherent := by
  have : AlgebraicGeometry.IsProper f := AlgebraicGeometry.IsProjectiveMorphism.isProper f
  have : F.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
  have hqc : ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward f F
  refine ⟨hqc, ?_⟩
  apply AlgebraicGeometry.Scheme.Modules.isFiniteType_of_finite_affine_sections
  intro y
  obtain ⟨V, hV, hy, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
      (show y ∈ (⊤ : S.Opens) from trivial)
  refine ⟨V, hV, hy, ?_⟩
  set U : X.Opens := f ⁻¹ᵁ V with hU
  set G : U.toScheme.Modules := AlgebraicGeometry.Scheme.Modules.restrict F U.ι with hG
  let _ : Module Γ(S, V) (AlgebraicGeometry.sheafCohomology U.toScheme G 0) :=
    Module.compHom _ (f.app V ≫ U.topIso.inv).hom
  have h0 : Module.Finite Γ(S, V) (AlgebraicGeometry.sheafCohomology U.toScheme G 0) :=
    AlgebraicGeometry.finite_sheafCohomology_restrict_of_isProjectiveMorphism f F ⟨V, hV⟩ 0
  -- the `Γ(S, V)`-linear surjection `H^0(f⁻¹V, F|) → Γ(F, f⁻¹V) = Γ(f_*F, V)`
  have hle : U ≤ U.ι ''ᵁ ⊤ := U.ι_image_top.ge
  have hle' : U.ι ''ᵁ ⊤ ≤ U := U.ι_image_top.le
  -- every endomorphism of `op U` in `X.Opensᵒᵖ` is the identity (thin category)
  have hX : ∀ g : op U ⟶ op U, X.presheaf.map g = 𝟙 _ := fun g => by
    rw [Subsingleton.elim g (𝟙 _), X.presheaf.map_id]
  have hF : ∀ g : op U ⟶ op U, F.presheaf.map g = 𝟙 _ := fun g => by
    rw [Subsingleton.elim g (𝟙 _), F.presheaf.map_id]
  let g : AlgebraicGeometry.sheafCohomology U.toScheme G 0 →ₗ[Γ(S, V)]
      Γ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj F, V) :=
    { toFun := fun x => F.presheaf.map (homOfLE hle).op
        ((F.restrictAppIso U.ι ⊤).hom (AlgebraicGeometry.sheafCohomologyZeroEquiv G x))
      map_add' := fun x y => by
        simp only [map_add]
        rfl
      map_smul' := fun r x => by
        show F.presheaf.map (homOfLE hle).op
            ((F.restrictAppIso U.ι ⊤).hom (AlgebraicGeometry.sheafCohomologyZeroEquiv G
              ((U.topIso.inv (f.app V r)) • x))) =
          (f.app V r) • F.presheaf.map (homOfLE hle).op
            ((F.restrictAppIso U.ι ⊤).hom (AlgebraicGeometry.sheafCohomologyZeroEquiv G x))
        rw [LinearEquiv.map_smul, AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom_apply,
          AlgebraicGeometry.Scheme.Opens.ι_appIso, Iso.refl_inv, AlgebraicGeometry.Scheme.Modules.map_smul]
        congr 1
        erw [ConcreteCategory.id_apply]
        have h1 : X.presheaf.map (homOfLE hle).op = U.topIso.hom := by
          rw [AlgebraicGeometry.Scheme.Opens.topIso_hom]
          congr 1
        erw [h1, Iso.inv_hom_id_apply] }
  have hg : Function.Surjective g := by
    intro z
    refine ⟨(AlgebraicGeometry.sheafCohomologyZeroEquiv G).symm
      ((F.restrictAppIso U.ι ⊤).inv (F.presheaf.map (homOfLE hle').op z)), ?_⟩
    show F.presheaf.map (homOfLE hle).op ((F.restrictAppIso U.ι ⊤).hom
      (AlgebraicGeometry.sheafCohomologyZeroEquiv G ((AlgebraicGeometry.sheafCohomologyZeroEquiv G).symm
        ((F.restrictAppIso U.ι ⊤).inv (F.presheaf.map (homOfLE hle').op z))))) = z
    rw [LinearEquiv.apply_symm_apply, Iso.inv_hom_id_apply]
    show (F.presheaf.map (homOfLE hle').op ≫ F.presheaf.map (homOfLE hle).op) z = z
    rw [← F.presheaf.map_comp, hF]
    rfl
  exact Module.Finite.of_surjective g hg

end
