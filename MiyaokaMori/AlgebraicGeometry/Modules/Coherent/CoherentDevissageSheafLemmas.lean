import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkExact
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkFunctor
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupportBasics
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y1
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ic

/-! # Sheaf-level lemmas for the dévissage of coherent sheaves

Elementary sheaf-level facts used by the dévissage `CoherentDevissageSupportSubset`. The tools are the
exactness of the stalk functor (`stalkFunctor x` preserves finite limits and colimits),
Stacks 01IC (kernels/cokernels of quasi-coherent modules are quasi-coherent, `isQuasicoherent_kernel`)
and Stacks 01Y1 (quasi-coherent sub/quotients of coherent modules on a locally Noetherian scheme are
coherent, `isCoherent_of_mono` / `isCoherent_of_epi`).

* `isZero_of_support_eq_empty`: a module sheaf all of whose stalks vanish is a zero object
  (a section all of whose germs vanish is zero, Mathlib `TopCat.Presheaf.section_ext`).
* `support_eq_empty_of_isZero`, `support_subset_of_epi` (quotients have smaller support).
* `notMem_support_kernel_of_injective` / `notMem_support_cokernel_of_surjective`: the stalk of `ker φ`
  (resp. `coker φ`) at `x` vanishes when `φ_x` is injective (resp. surjective), because the stalk
  functor preserves kernels and cokernels.
* `kernelSequence_shortExact` / `cokernelSequence_shortExact`: `0 → ker g → X → Y → 0` for an epi `g`
  and `0 → X → Y → coker f → 0` for a mono `f` are short exact; the two special cases
  `0 → ker φ → X → coim φ → 0` (`coimageSequence_shortExact`) and `0 → im φ → Y → coker φ → 0`
  (`imageSequence_shortExact`) for an arbitrary `φ : X ⟶ Y` in the abelian category `X.Modules`
  (`Abelian.image φ = ker (coker.π φ)`, `Abelian.coimage φ = coker (ker.ι φ)`).
* Coherence of `ker φ`, `coker φ`, `im φ`, `coim φ` for `φ` between coherent modules on a locally
  Noetherian scheme (Stacks 01Y1 + 01IC), packaged per sequence; supports of the three terms of each
  sequence, packaged per sequence.
* `length_stalk_add_of_shortExact` (lengths of stalks are additive on short exact sequences; the same
  statement and proof as in `Stacks0benAux`, repeated here to avoid importing the 0BEN machinery),
  `length_stalk_eq_of_iso`, `length_stalk_eq_of_bijective`.

Some of these lemmas duplicate lemmas of `Stacks0benAux` and `Stacks0bemStep` (`support_subset_of_epi`,
`subsingleton_stalk_of_isZero`, `length_stalk_add_of_shortExact`, `isCoherent_cokernel`,
`cokernelSequence_shortExact`); those modules import the Euler-characteristic / Snapper machinery, which
is not needed here. All names live in the namespace `MiyaokaMori.CoherentDevissage` to avoid collisions.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.CoherentDevissage

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-! ### Stalks and zero objects -/

theorem stalk_preservesFiniteLimits (x : X) :
    PreservesFiniteLimits (AlgebraicGeometry.Scheme.Modules.stalkFunctor x) :=
  (stalk_preservesFiniteLimits_colimits x).1

theorem stalk_preservesColimits (x : X) :
    PreservesColimits (AlgebraicGeometry.Scheme.Modules.stalkFunctor x) :=
  (stalk_preservesFiniteLimits_colimits x).2

/-- The stalk of a zero object is a subsingleton. -/
theorem subsingleton_stalk_of_isZero {F : X.Modules} (hF : IsZero F) (x : X) :
    Subsingleton (F.stalk x) := by
  have hpres := stalk_preservesFiniteLimits x
  have hz : IsZero ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).obj F) :=
    (AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map_isZero hF
  exact ModuleCat.isZero_iff_subsingleton.mp hz

theorem support_eq_empty_of_isZero {F : X.Modules} (hF : IsZero F) : F.support = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have h1 : Nontrivial (F.stalk x) := hx
  have h2 := subsingleton_stalk_of_isZero hF x
  exact not_nontrivial_iff_subsingleton.mpr h2 h1

/-- A module sheaf all of whose stalks are subsingletons is a zero object: a section all of whose
germs vanish is zero (`TopCat.Presheaf.section_ext`). -/
theorem isZero_of_forall_subsingleton_stalk (F : X.Modules) (h : ∀ x : X, Subsingleton (F.stalk x)) :
    IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U s
  have hs : ∀ (x : X) (hx : x ∈ U),
      F.presheaf.germ U x hx s = F.presheaf.germ U x hx 0 := by
    intro x hx
    have : Subsingleton (F.presheaf.stalk x) := h x
    exact Subsingleton.elim _ _
  have key := TopCat.Presheaf.section_ext (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X) U s 0 hs
  simpa using key

theorem isZero_of_support_eq_empty (F : X.Modules) (h : F.support = ∅) : IsZero F := by
  apply isZero_of_forall_subsingleton_stalk
  intro x
  have hx : x ∉ F.support := by rw [h]; exact Set.notMem_empty x
  exact not_nontrivial_iff_subsingleton.mp hx

/-! ### Supports of kernels, cokernels, quotients -/

/-- A quotient has smaller support (the stalk functor preserves colimits, so epi ↦ surjective). -/
theorem support_subset_of_epi {F G : X.Modules} (π : F ⟶ G) [Epi π] : G.support ⊆ F.support := by
  intro x hx
  have hpres := stalk_preservesColimits x
  have hepi : Epi ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map π) :=
    preserves_epi_of_preservesColimit _ π
  have hsurj : Function.Surjective ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map π) :=
    (ModuleCat.epi_iff_surjective _).mp hepi
  have hG : Nontrivial ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).obj G) := hx
  exact hsurj.nontrivial

/-- If `φ_x` is injective, the stalk of `ker φ` at `x` vanishes. -/
theorem subsingleton_stalk_kernel_of_injective {M N : X.Modules} (φ : M ⟶ N) (x : X)
    (h : Function.Injective ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map φ).hom) :
    Subsingleton ((kernel φ).stalk x) := by
  have hpres := stalk_preservesFiniteLimits x
  have hmono : Mono ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map φ) :=
    (ModuleCat.mono_iff_injective _).mpr h
  have hz : IsZero (kernel ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map φ)) :=
    isZero_kernel_of_mono _
  have hz' : IsZero ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).obj (kernel φ)) :=
    hz.of_iso (PreservesKernel.iso (AlgebraicGeometry.Scheme.Modules.stalkFunctor x) φ)
  exact ModuleCat.isZero_iff_subsingleton.mp hz'

theorem notMem_support_kernel_of_injective {M N : X.Modules} (φ : M ⟶ N) (x : X)
    (h : Function.Injective ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map φ).hom) :
    x ∉ (kernel φ).support :=
  not_nontrivial_iff_subsingleton.mpr (subsingleton_stalk_kernel_of_injective φ x h)

/-- If `φ_x` is surjective, the stalk of `coker φ` at `x` vanishes. -/
theorem subsingleton_stalk_cokernel_of_surjective {M N : X.Modules} (φ : M ⟶ N) (x : X)
    (h : Function.Surjective ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map φ).hom) :
    Subsingleton ((cokernel φ).stalk x) := by
  have hpres := stalk_preservesColimits x
  have hepi : Epi ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map φ) :=
    (ModuleCat.epi_iff_surjective _).mpr h
  have hz : IsZero (cokernel ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map φ)) :=
    isZero_cokernel_of_epi _
  have hz' : IsZero ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).obj (cokernel φ)) :=
    hz.of_iso (PreservesCokernel.iso (AlgebraicGeometry.Scheme.Modules.stalkFunctor x) φ)
  exact ModuleCat.isZero_iff_subsingleton.mp hz'

theorem notMem_support_cokernel_of_surjective {M N : X.Modules} (φ : M ⟶ N) (x : X)
    (h : Function.Surjective ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map φ).hom) :
    x ∉ (cokernel φ).support :=
  not_nontrivial_iff_subsingleton.mpr (subsingleton_stalk_cokernel_of_surjective φ x h)

/-! ### Short exact sequences attached to a morphism -/

/-- `0 → ker g → X → Y → 0` is short exact for an epimorphism `g`. -/
theorem kernelSequence_shortExact {M N : X.Modules} (g : M ⟶ N) [Epi g] :
    (ShortComplex.kernelSequence g).ShortExact := by
  refine ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact g) inferInstance ?_
  show Epi g
  infer_instance

/-- `0 → X → Y → coker f → 0` is short exact for a monomorphism `f`. -/
theorem cokernelSequence_shortExact {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    (ShortComplex.cokernelSequence f).ShortExact := by
  refine ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact f) ?_ inferInstance
  show Mono f
  infer_instance

/-- `0 → ker φ → X → coim φ → 0`, with `coim φ = coker (ker.ι φ)`. -/
theorem coimageSequence_shortExact {M N : X.Modules} (φ : M ⟶ N) :
    (ShortComplex.cokernelSequence (kernel.ι φ)).ShortExact :=
  cokernelSequence_shortExact _

/-- `0 → im φ → Y → coker φ → 0`, with `im φ = ker (coker.π φ)`. -/
theorem imageSequence_shortExact {M N : X.Modules} (φ : M ⟶ N) :
    (ShortComplex.kernelSequence (cokernel.π φ)).ShortExact :=
  kernelSequence_shortExact _

/-! ### Coherence (locally Noetherian base) -/

section Coherent

variable [AlgebraicGeometry.IsLocallyNoetherian X]

/-- Kernels of maps of coherent sheaves are coherent (Stacks 01IC + 01Y1). -/
theorem isCoherent_kernel {M N : X.Modules} (φ : M ⟶ N) [hM : M.IsCoherent] [hN : N.IsCoherent] :
    (kernel φ).IsCoherent := by
  have := hM.quasicoherent
  have := hN.quasicoherent
  have : (kernel φ).IsQuasicoherent := (isQuasicoherent_kernel φ).1
  exact isCoherent_of_mono (kernel.ι φ)

/-- Cokernels of maps of coherent sheaves are coherent (Stacks 01IC + 01Y1). -/
theorem isCoherent_cokernel {M N : X.Modules} (φ : M ⟶ N) [hM : M.IsCoherent] [hN : N.IsCoherent] :
    (cokernel φ).IsCoherent := by
  have := hM.quasicoherent
  have := hN.quasicoherent
  have : (cokernel φ).IsQuasicoherent := (isQuasicoherent_kernel φ).2
  exact isCoherent_of_epi (cokernel.π φ)

/-- `im φ = ker (coker.π φ)` is coherent. -/
theorem isCoherent_image {M N : X.Modules} (φ : M ⟶ N) [M.IsCoherent] [N.IsCoherent] :
    (Abelian.image φ).IsCoherent := by
  have := isCoherent_cokernel φ
  exact isCoherent_kernel (cokernel.π φ)

/-- `coim φ = coker (ker.ι φ)` is coherent. -/
theorem isCoherent_coimage {M N : X.Modules} (φ : M ⟶ N) [M.IsCoherent] [N.IsCoherent] :
    (Abelian.coimage φ).IsCoherent := by
  have := isCoherent_kernel φ
  exact isCoherent_cokernel (kernel.ι φ)

/-- Coherence of an isomorphic copy (`isCoherent_of_epi` applied to `e.hom`). -/
theorem isCoherent_of_iso {M N : X.Modules} (e : M ≅ N) [hM : M.IsCoherent] : N.IsCoherent := by
  have hq : N.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hM.quasicoherent
  exact isCoherent_of_epi e.hom

theorem imageSequence_isCoherent {M N : X.Modules} (φ : M ⟶ N) [M.IsCoherent] [N.IsCoherent] :
    (ShortComplex.kernelSequence (cokernel.π φ)).X₁.IsCoherent ∧
      (ShortComplex.kernelSequence (cokernel.π φ)).X₂.IsCoherent ∧
      (ShortComplex.kernelSequence (cokernel.π φ)).X₃.IsCoherent :=
  ⟨isCoherent_image φ, ‹N.IsCoherent›, isCoherent_cokernel φ⟩

theorem coimageSequence_isCoherent {M N : X.Modules} (φ : M ⟶ N) [M.IsCoherent] [N.IsCoherent] :
    (ShortComplex.cokernelSequence (kernel.ι φ)).X₁.IsCoherent ∧
      (ShortComplex.cokernelSequence (kernel.ι φ)).X₂.IsCoherent ∧
      (ShortComplex.cokernelSequence (kernel.ι φ)).X₃.IsCoherent :=
  ⟨isCoherent_kernel φ, ‹M.IsCoherent›, isCoherent_coimage φ⟩

end Coherent

/-! ### Supports of the terms of the two sequences -/

theorem imageSequence_support {M N : X.Modules} (φ : M ⟶ N) :
    (ShortComplex.kernelSequence (cokernel.π φ)).X₁.support ⊆ N.support ∧
      (ShortComplex.kernelSequence (cokernel.π φ)).X₂.support ⊆ N.support ∧
      (ShortComplex.kernelSequence (cokernel.π φ)).X₃.support ⊆ N.support := by
  have h1 : (kernel (cokernel.π φ)).support ⊆ N.support := support_subset_of_mono (kernel.ι (cokernel.π φ))
  have h3 : (cokernel φ).support ⊆ N.support := support_subset_of_epi (cokernel.π φ)
  exact ⟨h1, le_rfl, h3⟩

theorem coimageSequence_support {M N : X.Modules} (φ : M ⟶ N) :
    (ShortComplex.cokernelSequence (kernel.ι φ)).X₁.support ⊆ M.support ∧
      (ShortComplex.cokernelSequence (kernel.ι φ)).X₂.support ⊆ M.support ∧
      (ShortComplex.cokernelSequence (kernel.ι φ)).X₃.support ⊆ M.support := by
  have h1 : (kernel φ).support ⊆ M.support := support_subset_of_mono (kernel.ι φ)
  have h3 : (cokernel (kernel.ι φ)).support ⊆ M.support := support_subset_of_epi (cokernel.π (kernel.ι φ))
  exact ⟨h1, le_rfl, h3⟩

/-! ### Lengths of stalks -/

/-- Length of stalks is additive on short exact sequences (the stalk functor is exact). Same proof as
`length_stalk_add_of_shortExact` in `Stacks0benAux`. -/
theorem length_stalk_add_of_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact) (x : X) :
    Module.length (X.presheaf.stalk x) (S.X₂.stalk x) =
      Module.length (X.presheaf.stalk x) (S.X₁.stalk x) +
        Module.length (X.presheaf.stalk x) (S.X₃.stalk x) := by
  have hpres1 := stalk_preservesFiniteLimits x
  have hpres2 := stalk_preservesColimits x
  have hmono : Mono S.f := hS.mono_f
  have hepi : Epi S.g := hS.epi_g
  have hmono' : Mono ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map S.f) :=
    preserves_mono_of_preservesLimit _ S.f
  have hepi' : Epi ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map S.g) :=
    preserves_epi_of_preservesColimit _ S.g
  have hS' : (S.map (AlgebraicGeometry.Scheme.Modules.stalkFunctor x)).ShortExact :=
    hS.map (AlgebraicGeometry.Scheme.Modules.stalkFunctor x)
  have hinj : Function.Injective (S.map (AlgebraicGeometry.Scheme.Modules.stalkFunctor x)).f :=
    hS'.moduleCat_injective_f
  have hsurj : Function.Surjective (S.map (AlgebraicGeometry.Scheme.Modules.stalkFunctor x)).g :=
    hS'.moduleCat_surjective_g
  have hex : Function.Exact (S.map (AlgebraicGeometry.Scheme.Modules.stalkFunctor x)).f
      (S.map (AlgebraicGeometry.Scheme.Modules.stalkFunctor x)).g :=
    (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS'.exact
  exact Module.length_eq_add_of_exact
    (S.map (AlgebraicGeometry.Scheme.Modules.stalkFunctor x)).f.hom
    (S.map (AlgebraicGeometry.Scheme.Modules.stalkFunctor x)).g.hom hinj hsurj hex

/-- Isomorphic sheaves have stalks of the same length. -/
theorem length_stalk_eq_of_iso {M N : X.Modules} (e : M ≅ N) (x : X) :
    Module.length (X.presheaf.stalk x) (M.stalk x) = Module.length (X.presheaf.stalk x) (N.stalk x) :=
  ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).mapIso e).toLinearEquiv.length_eq

/-- A morphism bijective on the stalk at `x` preserves the length of that stalk. -/
theorem length_stalk_eq_of_bijective {M N : X.Modules} (φ : M ⟶ N) (x : X)
    (h : Function.Bijective ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map φ).hom) :
    Module.length (X.presheaf.stalk x) (M.stalk x) = Module.length (X.presheaf.stalk x) (N.stalk x) :=
  (LinearEquiv.ofBijective _ h).length_eq

end MiyaokaMori.CoherentDevissage

end
