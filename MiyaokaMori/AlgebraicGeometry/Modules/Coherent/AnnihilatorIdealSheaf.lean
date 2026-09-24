import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentFreeStalksLocallyFree
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.SubschemeStalkKer
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.EmbeddedPartCoherent

/-! # The annihilator ideal sheaf of a coherent sheaf

The annihilator ideal sheaf `I = Ann(F) = ker(O_X → 𝓗om(F, F))` of a coherent sheaf `F` on a locally
Noetherian scheme `X` (step 1 of Stacks 02OM), in the form needed there:

* `IdealSheafData.IsAnnihilatorOf I F`: `I(U) = Ann_{Γ(U,O_X)} Γ(U,F)` for every affine open `U`;
* `exists_isAnnihilatorOf`: such an `I` exists;
* `IsAnnihilatorOf.coe_support_eq`: `Supp I = Supp F`;
* `IsAnnihilatorOf.ker_stalkMap_subschemeι_eq`: for `z ∈ Z = V(I)`, the kernel of
  `O_{X,ι z} → O_{Z,z}` is `Ann_{O_{X,ι z}} F_{ι z}`.

All three rest on one piece of commutative algebra, `Module.annihilator_eq_map_annihilator_of_isLocalizedModule`:
for a finite `R`-module `M` and a localization `M' = S⁻¹M` over `R' = S⁻¹R`, `Ann_{R'} M' = (Ann_R M) R'`.
Applied to `S = powers f` (quasi-coherence: `Γ(D(f),F) = Γ(U,F)_f`, `isLocalizedModule_basicOpen`) it gives
the compatibility `Ann(M)_f = Ann(M_f)` needed for `IdealSheafData`; applied to `S = A ∖ 𝔭_x` (Stacks 01I8:
`F_x = Γ(U,F)_𝔭`, `isLocalizedModule_germ`) it gives `Ann_{O_{X,x}} F_x = Ann(M)·O_{X,x}`
(`Modules.annihilator_stalk_eq_map_annihilator`), whence the stalk-kernel statement via
`IdealSheafData.ker_stalkMap_subschemeι`; the support statement uses `Module.mem_support_iff_of_finite`
(Stacks 00L2) transported along `F_x ≅ Γ(U,F)_𝔭` (`Modules.mem_support_iff_annihilator_le`).

Edge cases: `F = 0` gives `I = ⊤`, `Supp I = ∅ = Supp F`, `Z = ∅` (the stalk statement is vacuous);
`X = ∅` is trivial.

Source: Stacks 02OM (first paragraph), Stacks 01Y1 (kernels of maps of quasi-coherent sheaves), Stacks 00L2 /
Mathlib `Module.annihilator` + `IsLocalizedModule`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **The annihilator of a localized finite module is the localized annihilator**:
`Ann_{S⁻¹R}(S⁻¹M) = (Ann_R M)·S⁻¹R` for `M` a finite `R`-module (Stacks 00L2 / 02M7-style argument).

`⊇`: `a ∈ Ann_R M` kills every `m/s` since `a • (m/s) = (a • m)/s = 0`. `⊆`: write `b = a/s`; then
`a • g(m) = s • (b • g(m)) = 0` for all `m`, so `g(a • m) = 0` and some `c_m ∈ S` kills `a • m`. With
finitely many generators `m_i` and `t = ∏ c_{m_i} ∈ S`, `t a ∈ Ann_R M`, and `b = (a t)/(s t)` lies in
`(Ann_R M)·S⁻¹R`. -/
theorem Module.annihilator_eq_map_annihilator_of_isLocalizedModule
    {R : Type*} [CommRing R] (S : Submonoid R) {R' : Type*} [CommRing R'] [Algebra R R']
    [IsLocalization S R'] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {M' : Type*} [AddCommGroup M'] [Module R M'] [Module R' M'] [IsScalarTower R R' M']
    (g : M →ₗ[R] M') [IsLocalizedModule S g] :
    Module.annihilator R' M' = (Module.annihilator R M).map (algebraMap R R') := by
  classical
  apply le_antisymm
  · intro b hb
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S b
    change IsLocalization.mk' R' a s ∈ _
    have hkill : ∀ m : M, g (a • m) = g 0 := by
      intro m
      rw [map_zero, map_smul, ← algebraMap_smul R' a (g m), ← IsLocalization.mk'_spec' R' a s,
        mul_smul, Module.mem_annihilator.mp hb (g m), smul_zero]
    obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
    have hchoice : ∀ i : Fin n, ∃ c : S, c • (a • v i) = 0 := by
      intro i
      obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := g) (hkill (v i))
      exact ⟨c, by rw [hc, smul_zero]⟩
    choose c hc using hchoice
    set t : S := ∏ i, c i with ht
    have hta : a * (t : R) ∈ Module.annihilator R M := by
      rw [← Submodule.annihilator_top, ← hv, Submodule.mem_annihilator_span]
      rintro ⟨_, i, rfl⟩
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem c (Finset.mem_univ i)
      have h1 : a * (t : R) = (k : R) * ((c i : R) * a) := by
        rw [ht, hk, Submonoid.coe_mul]; ring
      have h2 : (c i : R) • (a • v i) = 0 := hc i
      rw [h1, mul_smul, mul_smul, h2, smul_zero]
    rw [← IsLocalization.mk'_cancel (S := R') a s t, IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hta)
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Module.mem_annihilator]
    intro m'
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S g m'
    change algebraMap R R' a • IsLocalizedModule.mk' g m s = 0
    rw [algebraMap_smul, ← IsLocalizedModule.mk'_smul, Module.mem_annihilator.mp ha m,
      IsLocalizedModule.mk'_zero]

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **`Ann_{O_{X,x}} F_x = Ann_A(M)·O_{X,x}`** for `F` coherent, `U ∋ x` affine, `A = Γ(U,O_X)`,
`M = Γ(U,F)` (Stacks 01I8 `F_x = M_𝔭` + `Module.annihilator_eq_map_annihilator_of_isLocalizedModule`). -/
theorem annihilator_stalk_eq_map_annihilator (F : X.Modules) [F.IsCoherent] (U : X.affineOpens)
    {x : X} (hx : x ∈ U.1) :
    Module.annihilator (X.presheaf.stalk x) (F.presheaf.stalk x) =
      (Module.annihilator Γ(X, U.1) Γ(F, U.1)).map (X.presheaf.germ U.1 x hx).hom := by
  have : F.IsQuasicoherent := IsCoherent.quasicoherent
  have : F.IsFiniteType := IsCoherent.finiteType
  set p := U.2.primeIdealOf ⟨x, hx⟩ with hp
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    U.2.isLocalization_stalk ⟨x, hx⟩
  let modA : Module Γ(X, U.1) (F.presheaf.stalk x) :=
    Module.compHom (F.presheaf.stalk x) (X.presheaf.germ U.1 x hx).hom
  have : IsScalarTower Γ(X, U.1) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let g : Γ(F, U.1) →ₗ[Γ(X, U.1)] F.presheaf.stalk x :=
    { toFun := F.presheaf.germ U.1 x hx
      map_add' := map_add _
      map_smul' := fun r m => CoherentFreeStalksAux.germ_smul' F hx r m }
  have : IsLocalizedModule p.asIdeal.primeCompl g :=
    CoherentFreeStalksAux.isLocalizedModule_germ F U.2 hx (fun _ _ => rfl) g (fun _ => rfl)
  have : Module.Finite Γ(X, U.1) Γ(F, U.1) := Scheme.Modules.finite_sections_of_isFiniteType F U.2
  exact Module.annihilator_eq_map_annihilator_of_isLocalizedModule p.asIdeal.primeCompl g

/-- **`x ∈ Supp F ↔ Ann_A Γ(U,F) ⊆ 𝔭_x`** for `F` coherent and `U ∋ x` affine (Stacks 00L2
`Supp M = V(Ann M)` for finite `M`, transported along `F_x ≅ M_𝔭`, Stacks 01I8). -/
theorem mem_support_iff_annihilator_le (F : X.Modules) [F.IsCoherent] (U : X.affineOpens)
    {x : X} (hx : x ∈ U.1) :
    x ∈ F.support ↔
      Module.annihilator Γ(X, U.1) Γ(F, U.1) ≤ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have : F.IsQuasicoherent := IsCoherent.quasicoherent
  have : F.IsFiniteType := IsCoherent.finiteType
  set p := U.2.primeIdealOf ⟨x, hx⟩ with hp
  let modA : Module Γ(X, U.1) (F.presheaf.stalk x) :=
    Module.compHom (F.presheaf.stalk x) (X.presheaf.germ U.1 x hx).hom
  let g : Γ(F, U.1) →ₗ[Γ(X, U.1)] F.presheaf.stalk x :=
    { toFun := F.presheaf.germ U.1 x hx
      map_add' := map_add _
      map_smul' := fun r m => CoherentFreeStalksAux.germ_smul' F hx r m }
  have : IsLocalizedModule p.asIdeal.primeCompl g :=
    CoherentFreeStalksAux.isLocalizedModule_germ F U.2 hx (fun _ _ => rfl) g (fun _ => rfl)
  have : Module.Finite Γ(X, U.1) Γ(F, U.1) := Scheme.Modules.finite_sections_of_isFiniteType F U.2
  have h1 : x ∈ F.support ↔ Nontrivial (F.presheaf.stalk x) := Iff.rfl
  rw [h1, ← (IsLocalizedModule.iso p.asIdeal.primeCompl g).toEquiv.nontrivial_congr,
    ← Module.mem_support_iff, Module.mem_support_iff_of_finite]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `I` is the annihilator ideal sheaf of `F`: on every affine open `U`, `I(U) = Ann_{Γ(U,O_X)} Γ(U,F)`. -/
def IsAnnihilatorOf (I : X.IdealSheafData) (F : X.Modules) : Prop :=
  ∀ U : X.affineOpens, I.ideal U = Module.annihilator Γ(X, U.1) Γ(F, U.1)

/-- **Existence of the annihilator ideal sheaf** (Stacks 02OM, step 1; Stacks 01Y1).

Proof. Put `J(U) := Ann_{A} M` for `A = Γ(U, O_X)`, `M = Γ(U, F)` (`U` affine). We must check the sheaf
condition of Mathlib's `IdealSheafData`, i.e. for `f ∈ A` and the basic open `D(f) ⊆ U`:
`J(D(f)) = J(U) · A_f`. Since `F` is quasi-coherent, `Γ(D(f), F) = M_f` as an `A_f`-module
(`Scheme.Modules.isLocalizedModule_basicOpen`); since `F` is of finite type and `U` affine,
`M` is a finite `A`-module (`Scheme.Modules.finite_sections_of_isFiniteType`, `Stacks01pbAffineOpen`).
For a finite module `Ann_{A_f}(M_f) = Ann_A(M) · A_f`
(`Module.annihilator_eq_map_annihilator_of_isLocalizedModule`). Then `I := ⟨J, compat⟩`. -/
theorem exists_isAnnihilatorOf [AlgebraicGeometry.IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] :
    ∃ I : X.IdealSheafData, I.IsAnnihilatorOf F := by
  have : F.IsQuasicoherent := Modules.IsCoherent.quasicoherent
  have : F.IsFiniteType := Modules.IsCoherent.finiteType
  refine ⟨{ ideal := fun U => Module.annihilator Γ(X, U.1) Γ(F, U.1)
            map_ideal_basicOpen := ?_ }, fun U => rfl⟩
  intro U f
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  let _modD : Module Γ(X, U.1) Γ(F, X.basicOpen f) :=
    Module.compHom Γ(F, X.basicOpen f) (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  have : IsScalarTower Γ(X, U.1) Γ(X, X.basicOpen f) Γ(F, X.basicOpen f) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have := Scheme.Modules.isLocalizedModule_basicOpen F U.2 f (fun _ _ => rfl)
    (CoherentFreeStalksAux.resBasicOpen F f) (fun _ => rfl)
  have : Module.Finite Γ(X, U.1) Γ(F, U.1) := Scheme.Modules.finite_sections_of_isFiniteType F U.2
  have key : Module.annihilator Γ(X, X.basicOpen f) Γ(F, X.basicOpen f) =
      (Module.annihilator Γ(X, U.1) Γ(F, U.1)).map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f)) :=
    Module.annihilator_eq_map_annihilator_of_isLocalizedModule (Submonoid.powers f)
      (CoherentFreeStalksAux.resBasicOpen F f)
  exact key.symm

/-- **`Supp Ann(F) = Supp F`** (Stacks 02OM, step 3; Stacks 00L2 `Supp M = V(Ann M)` for finite `M`).

Proof. Let `x ∈ U` affine, `A = Γ(U,O_X)`, `M = Γ(U,F)`, `𝔭 ⊆ A` the prime of `x`. By Mathlib
`IdealSheafData.mem_support_iff_of_mem`, `x ∈ Supp I ↔ x ∈ V(I(U))`, i.e. `x ∉ D(f)` for all
`f ∈ Ann_A M`, i.e. (`mem_basicOpen_iff_notMem_primeIdealOf`) `Ann_A M ≤ 𝔭`. On the other side
`x ∈ Supp F ↔ Ann_A M ≤ 𝔭` is `Modules.mem_support_iff_annihilator_le`. -/
theorem IsAnnihilatorOf.coe_support_eq [AlgebraicGeometry.IsLocallyNoetherian X] {I : X.IdealSheafData}
    {F : X.Modules} [F.IsCoherent] (hI : I.IsAnnihilatorOf F) :
    (I.support : Set X) = F.support := by
  ext x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have h1 : x ∈ (I.support : Set X) ↔ x ∈ I.support := Iff.rfl
  rw [h1, I.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU, Scheme.mem_zeroLocus_iff, hI ⟨U, hU⟩,
    Modules.mem_support_iff_annihilator_le F ⟨U, hU⟩ hxU]
  constructor
  · intro h a ha
    by_contra hap
    exact h a ha ((Modules.mem_basicOpen_iff_notMem_primeIdealOf hU hxU a).mpr hap)
  · intro h a ha hxa
    exact (Modules.mem_basicOpen_iff_notMem_primeIdealOf hU hxU a).mp hxa (h ha)

/-- **The stalk of `Ann(F)` is the annihilator of the stalk** (Stacks 02OM, steps 2 and 4; Stacks 01QP).

Proof. Let `z ∈ Z = V(I)`, `x = ι z ∈ U` affine, `A = Γ(U,O_X)`, `M = Γ(U,F)`, `𝔭` the prime of `x`. By
`IdealSheafData.ker_stalkMap_subschemeι` (`SubschemeStalkKer`),
`ker(O_{X,x} → O_{Z,z}) = I(U) · O_{X,x} = (Ann_A M) A_𝔭` (germ map = localization `A → A_𝔭`). Since `M` is a
finite `A`-module and `F_x = M_𝔭` (quasi-coherence), `(Ann_A M) A_𝔭 = Ann_{A_𝔭}(M_𝔭) = Ann_{O_{X,x}} F_x`
(`Modules.annihilator_stalk_eq_map_annihilator`). -/
theorem IsAnnihilatorOf.ker_stalkMap_subschemeι_eq [AlgebraicGeometry.IsLocallyNoetherian X]
    {I : X.IdealSheafData} {F : X.Modules} [F.IsCoherent] (hI : I.IsAnnihilatorOf F) (z : I.subscheme) :
    RingHom.ker (I.subschemeι.stalkMap z).hom =
      Module.annihilator (X.presheaf.stalk (I.subschemeι.base z)) (F.stalk (I.subschemeι.base z)) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (I.subschemeι.base z)) isOpen_univ
  rw [I.ker_stalkMap_subschemeι ⟨U, hU⟩ z hxU, hI ⟨U, hU⟩]
  exact (Modules.annihilator_stalk_eq_map_annihilator F ⟨U, hU⟩ hxU).symm

/-- The kernel of `O_{X,ι z} → O_{Z,z}` kills the stalk `F_{ι z}` (consequence of
`ker_stalkMap_subschemeι_eq`). -/
theorem IsAnnihilatorOf.smul_stalk_eq_zero [AlgebraicGeometry.IsLocallyNoetherian X]
    {I : X.IdealSheafData} {F : X.Modules} [F.IsCoherent] (hI : I.IsAnnihilatorOf F) (z : I.subscheme)
    {a : X.presheaf.stalk (I.subschemeι.base z)} (ha : a ∈ RingHom.ker (I.subschemeι.stalkMap z).hom)
    (m : F.stalk (I.subschemeι.base z)) : a • m = 0 := by
  rw [hI.ker_stalkMap_subschemeι_eq z] at ha
  exact Module.mem_annihilator.mp ha m

/-- `Supp F ⊆ Z = V(Ann F)` as a set of points (`range_subschemeι`). -/
theorem IsAnnihilatorOf.support_subset_range [AlgebraicGeometry.IsLocallyNoetherian X]
    {I : X.IdealSheafData} {F : X.Modules} [F.IsCoherent] (hI : I.IsAnnihilatorOf F) :
    F.support ⊆ Set.range I.subschemeι.base := by
  rw [I.range_subschemeι, hI.coe_support_eq]

end AlgebraicGeometry.Scheme.IdealSheafData

end
