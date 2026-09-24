import Mathlib.AlgebraicGeometry.Artinian
import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkExact
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesTensorStalk
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.FreeModuleStalkBasisSpan
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.GrothendieckVanishing
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyZeroEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ce01id
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineGenericCoordinates

/-! # The rank-zero case of Stacks 0AYT on an Artinian scheme

The degenerate `n = 0` case of Stacks 0AYT on an Artinian scheme: `E` locally free with
`rankAtStalk E = 0` everywhere (which, with Mathlib's `IsLocallyFree` and the `finrank` convention, allows
free of infinite rank), `G` coherent, then `χ(Z, G ⊗ E) = 0`. Read the docstring of the main theorem
before reusing anything here.

Route:

1. `Z` is finite, discrete and affine (Mathlib instances for `IsArtinianScheme`); `H^i(Z, G ⊗ E) = 0` for
   `i ≥ 1` by affine vanishing (Stacks 01XB, `sheafCohomology_subsingleton_of_isAffine`; `G ⊗ E` is
   quasi-coherent), so `χ = dim_k H⁰` with no `finsum` fallback.
2. `H⁰(Z, G ⊗ E) ≅ Γ(Z, G ⊗ E)` `k`-linearly (`sheafCohomologyZeroEquiv`).
3. Stalks of `G ⊗ E`: `(G ⊗ E)_z ≅ G_z ⊗ E_z` (Stacks 01CB, `tensorStalkEquiv`) and `E_z` has an
   `O_{Z,z}`-basis indexed by `I_z` for the local trivialisation `E|_U ≅ O_U^{(I_z)}`, `I_z` arbitrary
   (`exists_basis_stalk_of_restrict_iso_free`, from `free_stalk_basis_of_stalkFunctor`: the stalk functor
   preserves coproducts). Hence `(G ⊗ E)_z ≅ I_z →₀ G_z`; `rankAtStalk E z = 0` forces `I_z = ∅` or
   `I_z` infinite (`rankAtStalk_of_restrict_iso_free`), so `(G ⊗ E)_z` is a subsingleton or not
   finitely generated over `k` (`not_finite_stalk_tensorObj_of_rankAtStalk_eq_zero`,
   `Module.finite_finsupp_iff`).
4. If all stalks vanish, `Γ(Z, G ⊗ E) = 0` (sheaf separation `TopCat.Presheaf.section_ext`). Otherwise
   pick `z` with `(G ⊗ E)_z ≠ 0`: on a discrete space the germ map `Γ(Z, F) → F_z` is surjective
   (`germ_top_surjective_of_discreteTopology`: extend a section over the open point `{z}` by `0` on the
   open complement, `TopCat.Sheaf.isProductOfDisjoint`), so `Γ(Z, G ⊗ E)` is not finitely generated over
   `k` and `Module.finrank k = 0` by `Module.finrank_of_not_finite`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- The stalk of the free sheaf `O_Y^{(I)}` at `y` has an `O_{Y,y}`-basis indexed by `I`, for an
**arbitrary** index type `I` (generalises `rankLocalIso.free_stalk_basis`, which needs `I` finite).
Proof: `free I = ∐_I unit`; the stalk functor preserves colimits
(`stalk_preservesFiniteLimits_colimits`), coproducts in `ModuleCat` are direct sums
(`ModuleCat.coprodIsoDirectSum`), `⨁_I M ≅ I →₀ M` (`finsuppLEquivDirectSum`), and the stalk of `unit`
is `O_{Y,y}` (`unitStalkLinearEquiv`). -/
theorem free_stalk_basis_of_stalkFunctor {Y : AlgebraicGeometry.Scheme.{u}} (I : Type u) (y : Y) :
    Nonempty (Module.Basis I (Y.presheaf.stalk y)
      ((MiyaokaMori.FreeStalk.freeM Y I).presheaf.stalk y)) := by
  classical
  let _ := AlgebraicGeometry.Scheme.Modules.moduleStalkModule Y (SheafOfModules.unit Y.ringCatSheaf) y
  let _ := AlgebraicGeometry.Scheme.Modules.moduleStalkModule Y (MiyaokaMori.FreeStalk.freeM Y I) y
  have hpres : PreservesColimits (AlgebraicGeometry.Scheme.Modules.stalkFunctor y) :=
    (AlgebraicGeometry.Scheme.Modules.stalk_preservesFiniteLimits_colimits y).2
  let S := AlgebraicGeometry.Scheme.Modules.stalkFunctor y
  let f : I → Y.Modules := fun _ => SheafOfModules.unit Y.ringCatSheaf
  let e1 : S.obj (∐ f) ≅ ∐ fun j => S.obj (f j) := PreservesCoproduct.iso S f
  let e2 := ModuleCat.coprodIsoDirectSum (fun j => S.obj (f j))
  let L1 : S.obj (∐ f) ≃ₗ[Y.presheaf.stalk y]
      DirectSum I (fun _ : I => S.obj (SheafOfModules.unit Y.ringCatSheaf)) :=
    (e1 ≪≫ e2).toLinearEquiv
  let L2 := (finsuppLEquivDirectSum (Y.presheaf.stalk y)
    (S.obj (SheafOfModules.unit Y.ringCatSheaf)) I).symm
  let L3 := Finsupp.mapRange.linearEquiv (α := I)
    (AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv Y y)
  let L : S.obj (∐ f) ≃ₗ[Y.presheaf.stalk y] (I →₀ Y.presheaf.stalk y) := L1 ≪≫ₗ L2 ≪≫ₗ L3
  exact ⟨Module.Basis.ofRepr L⟩

/-- A module sheaf trivialised as `O_U^{(I)}` on an open `U ∋ x` (any `I`) has a stalk at `x` with an
`O_{X,x}`-basis indexed by `I`. Same transport as `rankAtStalk_of_restrict_iso_free`
(`moduleStalkFunctor`, then the semilinear equivalence `moduleRestrictStalkEquiv` along
`O_{U,x} ≅ O_{X,x}`), starting from `free_stalk_basis_of_stalkFunctor` instead of the finite version. -/
theorem exists_basis_stalk_of_restrict_iso_free {X : AlgebraicGeometry.Scheme.{u}}
    (E : X.Modules) (U : X.Opens) (I : Type u)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj E ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
    (x : X) (hx : x ∈ U) :
    Nonempty (Module.Basis I (X.presheaf.stalk x) (E.presheaf.stalk x)) := by
  let y : U := ⟨x, hx⟩
  let e' : E.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I :=
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app E ≪≫ e
  let _ := AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (E.restrict U.ι) y
  let _ := AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (MiyaokaMori.FreeStalk.freeM U.toScheme I) y
  let _ := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X E x
  let L := ((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme y).mapIso e').toLinearEquiv
  obtain ⟨b0⟩ := free_stalk_basis_of_stalkFunctor (Y := U.toScheme) I y
  let b1 := b0.map L.symm
  let σ := (U.stalkIso y).commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  exact MiyaokaMori.basis_of_semilinearEquiv
    (AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleRestrictStalkEquiv X E U y) b1

/-- On a scheme with discrete underlying space every germ at `x` is the germ of a **global** section:
a germ is the germ of a section over the open point `W = {x}`, and that section extends by `0` on the
open complement `Wᶜ` (`F(W ⊔ Wᶜ) = F(W) × F(Wᶜ)`, `TopCat.Sheaf.isProductOfDisjoint`). -/
theorem germ_top_surjective_of_discreteTopology {X : AlgebraicGeometry.Scheme.{u}}
    [DiscreteTopology X] (F : X.Modules) (x : X) :
    Function.Surjective (F.presheaf.germ ⊤ x trivial) := by
  intro g
  obtain ⟨V, hxV, s, rfl⟩ := F.presheaf.exists_germ_eq g
  let W : X.Opens := ⟨{x}, isOpen_discrete _⟩
  let W' : X.Opens := ⟨{x}ᶜ, isOpen_discrete _⟩
  have hxW : x ∈ W := Set.mem_singleton x
  have hWV : W ≤ V := fun z hz => by
    have hz' : z = x := hz
    rw [hz']; exact hxV
  have hinf : W ⊓ W' = ⊥ := by
    ext z
    simp [W, W']
  have hsup : W ⊔ W' = ⊤ := by
    ext z
    simp [W, W']
  let Fs : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F.val.presheaf, F.isSheaf⟩
  have hl := Fs.isProductOfDisjoint W W' hinf
  obtain ⟨l, hl1, -⟩ := BinaryFan.IsLimit.lift' hl (𝟙 (Fs.1.obj (op W))) 0
  let s' : Γ(F, W) := F.presheaf.map (homOfLE hWV).op s
  let t : Γ(F, W ⊔ W') := l s'
  have ht : F.presheaf.map (homOfLE le_sup_left : W ⟶ W ⊔ W').op t = s' :=
    ConcreteCategory.congr_hom hl1 s'
  refine ⟨F.presheaf.map (eqToHom hsup.symm).op t, ?_⟩
  have h1 := TopCat.Presheaf.germ_res_apply F.presheaf (eqToHom hsup.symm) x trivial t
  have h2 := TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE le_sup_left : W ⟶ W ⊔ W') x hxW t
  have h3 := TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hWV) x hxW s
  have h2' : F.presheaf.germ W x hxW s' =
      F.presheaf.germ (W ⊔ W') x ((homOfLE le_sup_left : W ⟶ W ⊔ W').le hxW) t := by
    rw [← ht]; exact h2
  exact h1.trans (h2'.symm.trans h3)

end AlgebraicGeometry.Scheme.Modules

/-- If `N` has an `A`-basis indexed by `I`, then `M ⊗[A] N ≃ₗ[A] (I →₀ M)`
(`b.repr` and `TensorProduct.finsuppScalarRight`). -/
def MiyaokaMori.tensorBasisFinsuppEquiv {A M N I : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [DecidableEq I] (b : Module.Basis I A N) :
    (M ⊗[A] N) ≃ₗ[A] (I →₀ M) :=
  TensorProduct.congr (LinearEquiv.refl A M) b.repr ≪≫ₗ TensorProduct.finsuppScalarRight A A M I

namespace AlgebraicGeometry.Scheme.Modules

/-- At a point `x` where `E` is locally free with `rankAtStalk E x = 0`, a **nontrivial** stalk of
`G ⊗ E` is not finitely generated over `k` (for any ring map `ρ : k → O_{X,x}`, `k` a field; the
`k`-structure is restriction of scalars along `ρ`). Proof: `(G ⊗ E)_x ≅ G_x ⊗ E_x ≅ I →₀ G_x` for the
local trivialisation `E|_U ≅ O_U^{(I)}` (`tensorStalkEquiv`, `exists_basis_stalk_of_restrict_iso_free`);
by `Module.finite_finsupp_iff` a finitely generated `I →₀ G_x` has `I = ∅`, or `G_x = 0`, or `I` finite;
the first two contradict nontriviality and the last gives `rankAtStalk E x = #I = 0`
(`rankAtStalk_of_restrict_iso_free`), i.e. `I = ∅` again. -/
theorem not_finite_stalk_tensorObj_of_rankAtStalk_eq_zero {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} (G E : X.Modules) [E.IsLocallyFree] (x : X)
    (ρ : k →+* X.presheaf.stalk x)
    (hE : AlgebraicGeometry.Scheme.Modules.rankAtStalk E x = 0)
    (hnt : Nontrivial ((MonoidalCategoryStruct.tensorObj (C := X.Modules) G E).presheaf.stalk x)) :
    letI : Module k ((MonoidalCategoryStruct.tensorObj (C := X.Modules) G E).presheaf.stalk x) :=
      Module.compHom _ ρ
    ¬ Module.Finite k ((MonoidalCategoryStruct.tensorObj (C := X.Modules) G E).presheaf.stalk x) := by
  classical
  let _ : Module k ((MonoidalCategoryStruct.tensorObj (C := X.Modules) G E).presheaf.stalk x) :=
    Module.compHom _ ρ
  intro hfin
  obtain ⟨U, I, hxU, ⟨e⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree E x
  obtain ⟨b⟩ := exists_basis_stalk_of_restrict_iso_free E U I e x hxU
  let _ : Algebra k (X.presheaf.stalk x) := ρ.toAlgebra
  let _ : Module k (G.presheaf.stalk x) := Module.compHom _ ρ
  have : IsScalarTower k (X.presheaf.stalk x) (G.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun c m => show ρ c • m = ρ c • m from rfl
  have : IsScalarTower k (X.presheaf.stalk x)
      ((MonoidalCategoryStruct.tensorObj (C := X.Modules) G E).presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun c m => show ρ c • m = ρ c • m from rfl
  let L : (MonoidalCategoryStruct.tensorObj (C := X.Modules) G E).presheaf.stalk x
      ≃ₗ[X.presheaf.stalk x] (I →₀ G.presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv G E x ≪≫ₗ MiyaokaMori.tensorBasisFinsuppEquiv b
  let Lk := L.restrictScalars k
  have hfin' : Module.Finite k (I →₀ G.presheaf.stalk x) := Module.Finite.equiv Lk
  have hnt' : Nontrivial (I →₀ G.presheaf.stalk x) := Lk.toEquiv.symm.nontrivial
  rcases Module.finite_finsupp_iff.mp hfin' with hI | hG | ⟨-, hIfin⟩
  · exact not_subsingleton_iff_nontrivial.mpr hnt' inferInstance
  · exact not_subsingleton_iff_nontrivial.mpr hnt' inferInstance
  · have := Fintype.ofFinite I
    have hcard := AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free E U I e x hxU
    rw [hE] at hcard
    have : IsEmpty I := Fintype.card_eq_zero_iff.mp hcard.symm
    exact not_subsingleton_iff_nontrivial.mpr hnt' inferInstance

end AlgebraicGeometry.Scheme.Modules

/-- **The `n = 0` case of Stacks 0AYT on an Artinian scheme.** `Z` Artinian, proper over `k`, `G`
coherent, `E` locally free with `rankAtStalk E z = 0` for all `z`. Then `χ(Z, G ⊗ E) = 0`.

**Degenerate case — read before reusing.** With Mathlib's `SheafOfModules.IsLocallyFree`
(free of *any* rank locally) and `rankAtStalk` defined through `Module.finrank` (which is `0` in infinite
dimension), the hypothesis `rankAtStalk E z = 0` does **not** force `E = 0`: at each point `E_z` is free on
an index set that is empty **or infinite**. The statement of Stacks 0AYT
(`sheafEulerCharacteristic_tensor_of_dim_support_le_zero`) nevertheless asserts `χ(F ⊗ E) = 0 · χ(F)`
in this situation, so this case has to be proved; it is true, but in the infinite-rank case only through
the `finrank` convention "`finrank` of a module that is not finitely generated is `0`"
(`Module.finrank_of_not_finite`). This lemma is therefore exempt from the discipline in the docstring of
`sheafEulerCharacteristic` ("do not derive values of `χ` from the fallback branch") — the value `0` is the
one the statement demands, and `G ⊗ E` is in general *not* coherent here. Do not generalise or
reuse this lemma elsewhere. Which branch is used:
* all stalks `(G ⊗ E)_z = 0` (e.g. `E = 0`, or `G_z = 0` wherever `I_z ≠ ∅`): then `Γ(Z, G ⊗ E) = 0`
  and `χ = 0` genuinely, no convention involved;
* some stalk `(G ⊗ E)_z ≠ 0`: then `I_z` is infinite, `H⁰` is not finitely generated over `k`, and
  `χ = finrank_k H⁰ = 0` **is** the `finrank` convention. Higher cohomology vanishes genuinely (affine).

Source: Stacks 0AYT (the honest content is the `n > 0` case, `sheafEulerCharacteristic_tensor_of_isArtinianScheme`);
the degenerate part is elementary. Proof: see the module docstring (steps 1–4); the hypothesis
`hZ : IsProperOver k Z` is not needed (affine vanishing suffices) and is kept only to match the caller. -/
theorem AlgebraicGeometry.sheafEulerCharacteristic_tensor_eq_zero_of_rankAtStalk_eq_zero_of_isArtinianScheme
    {k : Type u} [Field k] (Z : AlgebraicGeometry.Scheme.{u})
    [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hZ : IsProperOver k Z)
    [AlgebraicGeometry.IsArtinianScheme Z] (G : Z.Modules) [G.IsCoherent]
    (E : Z.Modules) [E.IsLocallyFree] (hE : ∀ z, AlgebraicGeometry.Scheme.Modules.rankAtStalk E z = 0) :
    AlgebraicGeometry.sheafEulerCharacteristic (k := k) Z (G.tensor E) = 0 := by
  classical
  have : Finite Z := inferInstance
  have : DiscreteTopology Z := inferInstance
  have : AlgebraicGeometry.IsAffine Z := inferInstance
  have hGq : G.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
  have hEq : E.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsLocallyFree E
  set F' : Z.Modules := MonoidalCategoryStruct.tensorObj (C := Z.Modules) G E with hF'def
  have hF' : F'.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj G E)
      (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensor G E)
  rw [AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj G E)]
  -- Step 1: `χ(F') = dim_k H⁰(F')` (affine vanishing kills `H^i`, `i ≥ 1`).
  unfold AlgebraicGeometry.sheafEulerCharacteristic
  rw [finsum_eq_single _ 0 (fun i hi => by
    have := AlgebraicGeometry.sheafCohomology_subsingleton_of_isAffine F' i (Nat.pos_of_ne_zero hi)
    simp [Module.finrank_zero_of_subsingleton])]
  simp only [pow_zero, one_mul, Nat.cast_eq_zero]
  -- Step 2: `H⁰(F') ≅ Γ(F', ⊤)` `k`-linearly.
  let φ : k →+* Γ(Z, ⊤) := ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom
  let _ : Module k Γ(F', ⊤) := Module.compHom _ φ
  let e := AlgebraicGeometry.sheafCohomologyZeroEquiv F'
  let e' : AlgebraicGeometry.sheafCohomology Z F' 0 ≃ₗ[k] Γ(F', ⊤) :=
    { toFun := e
      invFun := e.symm
      map_add' := e.map_add
      map_smul' := fun c x => e.map_smul (φ c) x
      left_inv := e.left_inv
      right_inv := e.right_inv }
  rw [e'.finrank_eq]
  -- Step 3: `Γ(F', ⊤)` is `0` (all stalks vanish) or not finitely generated over `k`.
  by_cases hsub : ∀ z : Z, Subsingleton (F'.presheaf.stalk z)
  · have : Subsingleton Γ(F', ⊤) := ⟨fun s t =>
      TopCat.Presheaf.section_ext (⟨F'.val.presheaf, F'.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} Z)
        ⊤ s t (fun z _ => @Subsingleton.elim _ (hsub z) _ _)⟩
    exact Module.finrank_zero_of_subsingleton
  · push Not at hsub
    obtain ⟨z, hnt⟩ := hsub
    apply Module.finrank_of_not_finite
    intro hfin
    let ρ : k →+* Z.presheaf.stalk z := (Z.presheaf.germ ⊤ z trivial).hom.comp φ
    let _ : Module k (F'.presheaf.stalk z) := Module.compHom _ ρ
    let g : Γ(F', ⊤) →ₗ[k] F'.presheaf.stalk z :=
      { toFun := F'.presheaf.germ ⊤ z trivial
        map_add' := map_add _
        map_smul' := fun c m =>
          PresheafOfModules.germ_smul (R := Z.presheaf) F'.val z ⊤ trivial (φ c) m }
    have hsurj : Function.Surjective g :=
      AlgebraicGeometry.Scheme.Modules.germ_top_surjective_of_discreteTopology F' z
    have hfinz : Module.Finite k (F'.presheaf.stalk z) := Module.Finite.of_surjective g hsurj
    exact AlgebraicGeometry.Scheme.Modules.not_finite_stalk_tensorObj_of_rankAtStalk_eq_zero
      G E z ρ (hE z) hnt hfinz

end
