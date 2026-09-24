import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01pb
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ShortExactLocalOnOpenCover

/-! # Quasi-coherent submodules and quotients of coherent sheaves are coherent (Stacks 01Y1)

Stacks 01Y1: on a locally Noetherian scheme, quasi-coherent submodules and quasi-coherent quotients
of a coherent sheaf are coherent.

Source: Stacks 01Y1 (`coherent-lemma-coherent-Noetherian-quasi-coherent-sub-quotient`).

Proof. Coherent = quasi-coherent + finite type (`IsCoherent`); quasi-coherence is a hypothesis, so
only finite type remains. Use the affine-local criterion `isFiniteType_of_finite_affine_sections` (the
"⇐" direction of Stacks 01PB): for every point take an affine open `U ∋ x` and show that `Γ(N, U)` (or
`Γ(Q, U)`) is a finite `Γ(X, U)`-module.

1. `X` locally Noetherian ⇒ `A := Γ(X, U)` is Noetherian (`IsLocallyNoetherian.component_noetherian`);
   `M` coherent ⇒ `Γ(M, U)` is a finite `A`-module (`finite_sections_of_isFiniteType`, Stacks 01PB "⇒"),
   hence a Noetherian `A`-module.
2. **The section functor on an affine open is exact on quasi-coherent sheaves**
   (`Stacks01y1Aux.injective_app_of_mono` / `surjective_app_of_epi`): restrict along
   `hU.fromSpec : Spec A → X` (which preserves finite limits and colimits, hence monomorphisms and
   epimorphisms) to a mono/epi `φ` between quasi-coherent sheaves on `Spec A`. `M ≅ (Γ M)~`
   (`fromTildeΓ` is an isomorphism for quasi-coherent sheaves, Stacks 01I8), and naturality of
   `fromTildeΓ` gives `(Γ φ)~ = fromTildeΓ ≫ φ ≫ (fromTildeΓ)⁻¹`, which is mono/epi together with `φ`;
   `tilde` is faithful, hence reflects monos/epis, so `Γ φ` is mono/epi in `ModuleCat A`, i.e. the
   section map is injective/surjective (`ModuleCat.mono_iff_injective` / `epi_iff_surjective`).
   `Γ(M.restrict f, ⊤) = Γ(M, f ''ᵁ ⊤)` holds by definition.
3. Submodules: `Γ(N, U) ↪ Γ(M, U)` is injective and submodules of Noetherian modules are finitely
   generated (`Module.Finite.of_injective`). Quotients: `Γ(M, U) ↠ Γ(Q, U)` is surjective and images of
   finite modules are finite (`Module.Finite.of_surjective`).

This avoids 01IC (kernels are quasi-coherent), 01XB (`H¹ = 0` on affines) and the long exact
cohomology sequence: exactness of the section functor on affines follows directly from the full
faithfulness of `tilde` (the same method as `finite_of_generatingSections` in `Stacks01pbAffineOpen`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace Stacks01y1Aux

open AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- On `Spec R`, a monomorphism between quasi-coherent modules induces a monomorphism on global
sections: `(Γ φ)~ ≅ φ` via `fromTildeΓ`, and `tilde` reflects monomorphisms. -/
theorem mono_Γ_map {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) [Mono φ] :
    Mono (moduleSpecΓFunctor.map φ) := by
  have hM : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  have hN : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  have hsq : (tilde.functor R).map (moduleSpecΓFunctor.map φ) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ φ := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality φ
  have heq : (tilde.functor R).map (moduleSpecΓFunctor.map φ) =
      M.fromTildeΓ ≫ φ ≫ inv N.fromTildeΓ := by
    rw [← Category.assoc, ← hsq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have : Mono ((tilde.functor R).map (moduleSpecΓFunctor.map φ)) := by
    rw [heq]; infer_instance
  exact (tilde.functor R).mono_of_mono_map this

set_option backward.isDefEq.respectTransparency false in
/-- On `Spec R`, an epimorphism between quasi-coherent modules induces an epimorphism on global
sections (same argument as `mono_Γ_map`). -/
theorem epi_Γ_map {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) [Epi φ] :
    Epi (moduleSpecΓFunctor.map φ) := by
  have hM : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  have hN : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  have hsq : (tilde.functor R).map (moduleSpecΓFunctor.map φ) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ φ := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality φ
  have heq : (tilde.functor R).map (moduleSpecΓFunctor.map φ) =
      M.fromTildeΓ ≫ φ ≫ inv N.fromTildeΓ := by
    rw [← Category.assoc, ← hsq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have : Epi ((tilde.functor R).map (moduleSpecΓFunctor.map φ)) := by
    rw [heq]; infer_instance
  exact (tilde.functor R).epi_of_epi_map this

set_option backward.isDefEq.respectTransparency false in
/-- `Spec R`: the global-sections map of a mono between quasi-coherent modules is injective. -/
theorem injective_app_top {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) [Mono φ] :
    Function.Injective (φ.app ⊤) := by
  have h := (ModuleCat.mono_iff_injective (moduleSpecΓFunctor.map φ)).mp (mono_Γ_map φ)
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- `Spec R`: the global-sections map of an epi between quasi-coherent modules is surjective. -/
theorem surjective_app_top {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) [Epi φ] :
    Function.Surjective (φ.app ⊤) := by
  have h := (ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map φ)).mp (epi_Γ_map φ)
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Sections over an affine open of a mono between quasi-coherent modules are injective. -/
theorem injective_app_of_mono {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (i : N ⟶ M) [Mono i] {U : X.Opens}
    (hU : IsAffineOpen U) : Function.Injective (i.app U) := by
  have hpres : PreservesFiniteLimits (Scheme.Modules.restrictFunctor hU.fromSpec) :=
    Scheme.Modules.restrictFunctor_preservesFiniteLimits _
  have hmono : Mono ((Scheme.Modules.restrictFunctor hU.fromSpec).map i) := inferInstance
  have hinj := injective_app_top ((Scheme.Modules.restrictFunctor hU.fromSpec).map i)
  have hV : hU.fromSpec ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have key : ∀ V : X.Opens, hU.fromSpec ''ᵁ ⊤ = V → Function.Injective (i.app V) := by
    rintro V rfl
    exact hinj
  exact key U hV

set_option backward.isDefEq.respectTransparency false in
/-- Sections over an affine open of an epi between quasi-coherent modules are surjective. -/
theorem surjective_app_of_epi {X : Scheme.{u}} {M Q : X.Modules}
    [M.IsQuasicoherent] [Q.IsQuasicoherent] (p : M ⟶ Q) [Epi p] {U : X.Opens}
    (hU : IsAffineOpen U) : Function.Surjective (p.app U) := by
  have hpres : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor hU.fromSpec) :=
    inferInstance
  have hepi : Epi ((Scheme.Modules.restrictFunctor hU.fromSpec).map p) := inferInstance
  have hsurj := surjective_app_top ((Scheme.Modules.restrictFunctor hU.fromSpec).map p)
  have hV : hU.fromSpec ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have key : ∀ V : X.Opens, hU.fromSpec ''ᵁ ⊤ = V → Function.Surjective (p.app V) := by
    rintro V rfl
    exact hsurj
  exact key U hV

/-- Every point lies in some affine open. -/
theorem exists_affineOpens_mem {X : Scheme.{u}} (x : X) : ∃ U : X.affineOpens, x ∈ (U : X.Opens) := by
  have : x ∈ (⊤ : X.Opens) := trivial
  rw [← iSup_affineOpens_eq_top X] at this
  exact Opens.mem_iSup.mp this

set_option backward.isDefEq.respectTransparency false in
/-- Affine-local statement for submodules: `Γ(N, U)` injects into the Noetherian module `Γ(M, U)`. -/
theorem finite_sections_of_mono {X : Scheme.{u}} [IsLocallyNoetherian X] {M N : X.Modules}
    (i : N ⟶ M) [Mono i] [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) : Module.Finite Γ(X, U) Γ(N, U) := by
  have hnoeth : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hfin : Module.Finite Γ(X, U) Γ(M, U) :=
    Scheme.Modules.finite_sections_of_isFiniteType M hU
  have : IsNoetherian Γ(X, U) Γ(M, U) := isNoetherian_of_isNoetherianRing_of_finite _ _
  let f : Γ(N, U) →ₗ[Γ(X, U)] Γ(M, U) :=
    { toFun := fun m => ConcreteCategory.hom (i.app U) m
      map_add' := fun a b => map_add (ConcreteCategory.hom (i.app U)) a b
      map_smul' := fun r m => Scheme.Modules.Hom.app_smul i r m }
  exact Module.Finite.of_injective f (fun a b h => injective_app_of_mono i hU h)

set_option backward.isDefEq.respectTransparency false in
/-- Affine-local statement for quotients: `Γ(Q, U)` is a quotient of the finite module `Γ(M, U)`. -/
theorem finite_sections_of_epi {X : Scheme.{u}} {M Q : X.Modules}
    (p : M ⟶ Q) [Epi p] [M.IsQuasicoherent] [M.IsFiniteType] [Q.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) : Module.Finite Γ(X, U) Γ(Q, U) := by
  have hfin : Module.Finite Γ(X, U) Γ(M, U) :=
    Scheme.Modules.finite_sections_of_isFiniteType M hU
  let f : Γ(M, U) →ₗ[Γ(X, U)] Γ(Q, U) :=
    { toFun := fun m => ConcreteCategory.hom (p.app U) m
      map_add' := fun a b => map_add (ConcreteCategory.hom (p.app U)) a b
      map_smul' := fun r m => Scheme.Modules.Hom.app_smul p r m }
  exact Module.Finite.of_surjective f (fun y => surjective_app_of_epi p hU y)

end Stacks01y1Aux

/-- **Stacks 01Y1 (submodules).** On a locally Noetherian scheme a quasi-coherent submodule of a
coherent module is coherent. Proof: see the file header. -/
theorem AlgebraicGeometry.Scheme.Modules.isCoherent_of_mono {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] {M N : X.Modules} (i : N ⟶ M)
    [CategoryTheory.Mono i] [M.IsCoherent] [N.IsQuasicoherent] : N.IsCoherent := by
  have hqc : M.IsQuasicoherent := IsCoherent.quasicoherent
  have hft : M.IsFiniteType := IsCoherent.finiteType
  refine ⟨inferInstance, ?_⟩
  apply isFiniteType_of_finite_affine_sections N
  intro x
  obtain ⟨⟨U, hU⟩, hxU⟩ := Stacks01y1Aux.exists_affineOpens_mem x
  exact ⟨U, hU, hxU, Stacks01y1Aux.finite_sections_of_mono i hU⟩

/-- **Stacks 01Y1 (quotients).** On a locally Noetherian scheme a quasi-coherent quotient of a
coherent module is coherent. Proof: see the file header (the Noetherian hypothesis is not needed
for this half). -/
theorem AlgebraicGeometry.Scheme.Modules.isCoherent_of_epi {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] {M Q : X.Modules} (p : M ⟶ Q)
    [CategoryTheory.Epi p] [M.IsCoherent] [Q.IsQuasicoherent] : Q.IsCoherent := by
  have hqc : M.IsQuasicoherent := IsCoherent.quasicoherent
  have hft : M.IsFiniteType := IsCoherent.finiteType
  refine ⟨inferInstance, ?_⟩
  apply isFiniteType_of_finite_affine_sections Q
  intro x
  obtain ⟨⟨U, hU⟩, hxU⟩ := Stacks01y1Aux.exists_affineOpens_mem x
  exact ⟨U, hU, hxU, Stacks01y1Aux.finite_sections_of_epi p hU⟩

end
