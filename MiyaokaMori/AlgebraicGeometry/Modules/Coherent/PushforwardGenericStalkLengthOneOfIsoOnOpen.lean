import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ProjectionFormulaClosedImmersion
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle

/-! # The generic stalk of a pushforward along a morphism that is an isomorphism near the generic point

**The generic stalk of `π_*N` for `π` an isomorphism near the generic point** (a step in the
construction of the generator sheaf on an integral proper scheme; Stacks 02O5 proof, last sentence:
"`G_η ≅ N_{η'} ≅ κ(η)`").
`Z` integral with generic point `η`, `π : Z' → Z`, `U ⊆ Z` a nonempty open with `π ∣_ U` an isomorphism, `N` a
line bundle on `Z'`. Then `(π_*N)_η` is a one-dimensional `O_{Z,η}`-vector space: `length_{O_{Z,η}} (π_*N)_η = 1`
(`O_{Z,η} = κ(η)` is the function field, a field).

**Formalization.** Everything is proved at an arbitrary point `x ∈ π⁻¹U` with
`O_{Z, π x}` a field (`length_stalk_pushforward_eq_one_of_isIso_morphismRestrict`) and then specialized to the
generic point. The pieces:
* `pushforwardStalkMap_bijective_of_isIso_morphismRestrict`: the pushforward stalk map `(π_*N)_{π x} → N_x`
  (Mathlib `stalkPushforward`, `pushforwardStalkMap`) is bijective for `x ∈ π⁻¹U`, by a direct germ
  argument: `π` maps opens `W' ⊆ π⁻¹U` onto opens `π(W')` of `Z` with `π⁻¹(π(W')) = W'`
  (`(π⁻¹U).ι ≫ π = (π ∣_ U) ≫ U.ι` is an open immersion, hence an open embedding), so the neighbourhoods of `x`
  inside `π⁻¹U` and the neighbourhoods of `π x` inside `U` correspond and the germ maps match.
* `isIso_stalkMap_of_isIso_morphismRestrict`: `π^♯_x` is an isomorphism (`Scheme.Hom.stalkMap_comp` for
  `(π⁻¹U).ι ≫ π`, whose stalk maps and those of `(π⁻¹U).ι` are isomorphisms).
* `exists_basis_stalk_of_isLineBundle` / `nonempty_linearEquiv_stalk_of_isLineBundle`: `N_x ≃ₗ[O_{Z',x}] O_{Z',x}`
  (the proof of `free_stalk_of_restrict_iso_free` in `LineBundleStalkFree`, keeping the
  `PUnit`-indexed basis instead of `Module.Free`).
* Assembly as in `PushforwardClosedImmersionGenericStalk`: the `O_{Z,πx}`-linear equivalence
  `(π_*N)_{π x} ≃ N_x` (`pushforwardStalkModule`, `pushforwardStalkMap_smul`), `Module.length_eq_of_surjective`
  along the surjection `π^♯_x`, `LinearEquiv.length_eq`, and `Module.length_eq_one_iff` for the field `O_{Z',x}`
  (`MulEquiv.isField` along `π^♯_x`, `isSimpleModule_self_iff_isUnit`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

section IsoOnOpen

variable {Z Z' : AlgebraicGeometry.Scheme.{u}} (π : Z' ⟶ Z) (U : Z.Opens) [IsIso (π ∣_ U)]

/-- `(π⁻¹U).ι ≫ π = (π ∣_ U) ≫ U.ι` is an open immersion when `π ∣_ U` is an isomorphism. -/
theorem isOpenImmersion_ι_comp_of_isIso_morphismRestrict :
    IsOpenImmersion ((π ⁻¹ᵁ U).ι ≫ π) := by
  rw [← morphismRestrict_ι]
  infer_instance

omit [IsIso (π ∣_ U)] in
theorem base_ι_comp_apply (x : π ⁻¹ᵁ U) : ((π ⁻¹ᵁ U).ι ≫ π).base x = π.base x.1 := by
  rfl

/-- `π` is injective on `π⁻¹U`. -/
theorem base_injOn_preimage_of_isIso_morphismRestrict :
    Set.InjOn π.base (π ⁻¹ᵁ U : Set Z') := by
  have := isOpenImmersion_ι_comp_of_isIso_morphismRestrict π U
  intro x hx y hy hxy
  have h := ((π ⁻¹ᵁ U).ι ≫ π).isOpenEmbedding.injective
    (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (by
      rw [base_ι_comp_apply, base_ι_comp_apply]
      exact hxy)
  exact congrArg Subtype.val h

/-- The image under `π` of an open subset of `π⁻¹U` is open. -/
theorem isOpen_image_of_le_preimage_of_isIso_morphismRestrict (W' : Z'.Opens)
    (hW' : W' ≤ π ⁻¹ᵁ U) : IsOpen (π.base '' (W' : Set Z')) := by
  have := isOpenImmersion_ι_comp_of_isIso_morphismRestrict π U
  have h1 : π.base '' (W' : Set Z') =
      ((π ⁻¹ᵁ U).ι ≫ π).base '' (Subtype.val ⁻¹' (W' : Set Z')) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hW' hx⟩, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1, hx, rfl⟩
  rw [h1]
  exact ((π ⁻¹ᵁ U).ι ≫ π).isOpenEmbedding.isOpenMap _
    (W'.isOpen.preimage continuous_subtype_val)

/-- The image `π(W')` of an open `W' ⊆ π⁻¹U`, as an open of `Z`. -/
def imageOpens (W' : Z'.Opens) (hW' : W' ≤ π ⁻¹ᵁ U) : Z.Opens :=
  ⟨π.base '' (W' : Set Z'), isOpen_image_of_le_preimage_of_isIso_morphismRestrict π U W' hW'⟩

theorem le_preimage_imageOpens (W' : Z'.Opens) (hW' : W' ≤ π ⁻¹ᵁ U) :
    W' ≤ π ⁻¹ᵁ imageOpens π U W' hW' := fun x hx => ⟨x, hx, rfl⟩

theorem preimage_imageOpens_le (W' : Z'.Opens) (hW' : W' ≤ π ⁻¹ᵁ U) :
    π ⁻¹ᵁ imageOpens π U W' hW' ≤ W' := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hxU : x ∈ π ⁻¹ᵁ U := by
    change π.base x ∈ U
    rw [← hyx]
    exact hW' hy
  have := base_injOn_preimage_of_isIso_morphismRestrict π U (hW' hy) hxU hyx
  rw [← this]
  exact hy

theorem imageOpens_le {W' : Z'.Opens} (hW' : W' ≤ π ⁻¹ᵁ U) {W : Z.Opens}
    (h : W' ≤ π ⁻¹ᵁ W) : imageOpens π U W' hW' ≤ W := by
  rintro z ⟨x, hx, rfl⟩
  exact h hx

theorem mem_imageOpens {W' : Z'.Opens} (hW' : W' ≤ π ⁻¹ᵁ U) {x : Z'} (hx : x ∈ W') :
    π.base x ∈ imageOpens π U W' hW' := ⟨x, hx, rfl⟩

variable (N : Z'.Modules)

/-- **Stalk of the pushforward at a point where `π` is an isomorphism** (the topological part of
Stacks 02O5's "`G_η ≅ N_{η'}`"): for `x ∈ π⁻¹U`, the pushforward stalk map
`(π_* N)_{π x} → N_x` (Mathlib `stalkPushforward`) is bijective. -/
theorem pushforwardStalkMap_bijective_of_isIso_morphismRestrict (x : Z') (hx : x ∈ π ⁻¹ᵁ U) :
    Function.Bijective (pushforwardStalkMap π N x) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro m hm
    obtain ⟨W, hWU, hxW, s, rfl⟩ :=
      ((AlgebraicGeometry.Scheme.Modules.pushforward π).obj N).presheaf.exists_le_germ_eq m hx
    erw [pushforwardStalkMap_germ] at hm
    rw [← map_zero (ConcreteCategory.hom (N.presheaf.germ (π ⁻¹ᵁ W) x hxW))] at hm
    obtain ⟨W'', hxW'', iU, _, heq⟩ := N.presheaf.germ_eq x hxW hxW _ _ hm
    rw [map_zero] at heq
    have hW''V : W'' ≤ π ⁻¹ᵁ U := le_trans iU.le (fun z hz => hWU hz)
    let W₀ := imageOpens π U W'' hW''V
    have hxW₀ : π.base x ∈ W₀ := mem_imageOpens π U hW''V hxW''
    have hW₀W : W₀ ≤ W := imageOpens_le π U hW''V iU.le
    rw [← map_zero (ConcreteCategory.hom
      (((AlgebraicGeometry.Scheme.Modules.pushforward π).obj N).presheaf.germ W₀ (π.base x) hxW₀))]
    refine ((AlgebraicGeometry.Scheme.Modules.pushforward π).obj N).presheaf.germ_ext W₀ hxW₀
      (homOfLE hW₀W) (𝟙 W₀) ?_
    rw [op_id, CategoryTheory.Functor.map_id, map_zero]
    change N.presheaf.map (homOfLE (fun z hz => hW₀W hz : π ⁻¹ᵁ W₀ ≤ π ⁻¹ᵁ W)).op s = 0
    have hfac : (homOfLE (fun z hz => hW₀W hz : π ⁻¹ᵁ W₀ ≤ π ⁻¹ᵁ W)) =
        homOfLE (preimage_imageOpens_le π U W'' hW''V) ≫ iU := Subsingleton.elim _ _
    rw [hfac, op_comp, CategoryTheory.Functor.map_comp]
    erw [ConcreteCategory.comp_apply, heq, map_zero]
  · intro t
    obtain ⟨W', hW'V, hxW', s, rfl⟩ := N.presheaf.exists_le_germ_eq t hx
    let W := imageOpens π U W' hW'V
    have hxW : π.base x ∈ W := mem_imageOpens π U hW'V hxW'
    have hle : π ⁻¹ᵁ W ≤ W' := preimage_imageOpens_le π U W' hW'V
    refine ⟨((AlgebraicGeometry.Scheme.Modules.pushforward π).obj N).presheaf.germ W (π.base x) hxW
      (N.presheaf.map (homOfLE hle).op s), ?_⟩
    erw [pushforwardStalkMap_germ]
    exact N.presheaf.germ_res_apply (homOfLE hle) x hxW s

set_option backward.isDefEq.respectTransparency false in
/-- `π^♯_x : O_{Z, π x} → O_{Z', x}` is an isomorphism for `x ∈ π⁻¹U` (`(π⁻¹U).ι ≫ π` is an open
immersion, whose stalk maps are isomorphisms, and `Scheme.Hom.stalkMap_comp`). -/
theorem isIso_stalkMap_of_isIso_morphismRestrict (x : Z') (hx : x ∈ π ⁻¹ᵁ U) :
    IsIso (π.stalkMap x) := by
  have := isOpenImmersion_ι_comp_of_isIso_morphismRestrict π U
  have h := AlgebraicGeometry.Scheme.Hom.stalkMap_comp (π ⁻¹ᵁ U).ι π ⟨x, hx⟩
  have h1 : IsIso (((π ⁻¹ᵁ U).ι ≫ π).stalkMap ⟨x, hx⟩) := inferInstance
  rw [h] at h1
  exact IsIso.of_isIso_comp_right (π.stalkMap ((π ⁻¹ᵁ U).ι.base ⟨x, hx⟩))
    ((π ⁻¹ᵁ U).ι.stalkMap ⟨x, hx⟩)

end IsoOnOpen

section LineBundleStalkBasis

/-- The stalk of the free sheaf `O_Y^{(I)}` (`I` finite) at `y` has a basis indexed by `I`
(`FreeModuleStalkBasisSpan`; the same private lemma is in `LineBundleStalkFree`). -/
private theorem free_stalk_basis' {Y : AlgebraicGeometry.Scheme.{u}} (I : Type u) [Finite I]
    (y : Y) :
    Nonempty (Module.Basis I (Y.presheaf.stalk y)
      ((MiyaokaMori.FreeStalk.freeM Y I).presheaf.stalk y)) :=
  ⟨Module.Basis.mk (MiyaokaMori.FreeStalk.linearIndependent_b I y)
    (MiyaokaMori.FreeStalk.span_b_eq_top I y).ge⟩

/-- A module sheaf trivialized on `U ∋ x` as `O_U^{(I)}` (`I` finite) has a stalk at `x` with a basis
indexed by `I` (the proof of `free_stalk_of_restrict_iso_free`, keeping the basis). Private: the public,
more general version (arbitrary `I`, trivialization written with `pullback U.ι`) is
`exists_basis_stalk_of_restrict_iso_free` in `Stacks0ayt_ArtinianRankZero`, whose
import closure (Artinian schemes, Grothendieck vanishing, …) is not wanted in this leaf. -/
private theorem basis_stalk_of_restrict_iso_free_finite {X : AlgebraicGeometry.Scheme.{u}} (E : X.Modules)
    (U : X.Opens) (I : Type u) [Finite I]
    (e : E.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
    (x : X) (hx : x ∈ U) :
    Nonempty (Module.Basis I (X.presheaf.stalk x) (E.presheaf.stalk x)) := by
  let y : U := ⟨x, hx⟩
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (E.restrict U.ι) y
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (MiyaokaMori.FreeStalk.freeM U.toScheme I) y
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X E x
  let L := ((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme y).mapIso e).toLinearEquiv
  obtain ⟨b0⟩ := free_stalk_basis' (Y := U.toScheme) I y
  let b1 := b0.map L.symm
  let σ := (U.stalkIso y).commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  exact MiyaokaMori.basis_of_semilinearEquiv
    (AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleRestrictStalkEquiv X E U y) b1

/-- The stalk of a line bundle has a basis indexed by `PUnit`. -/
theorem exists_basis_stalk_of_isLineBundle {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    [M.IsLineBundle] (x : X) :
    Nonempty (Module.Basis PUnit.{u + 1} (X.presheaf.stalk x) (M.presheaf.stalk x)) := by
  obtain ⟨U, hx, ⟨e⟩⟩ := IsLineBundle.locally_trivial (M := M) x
  exact basis_stalk_of_restrict_iso_free_finite M U PUnit.{u + 1}
    (e ≪≫ (CategoryTheory.Limits.coproductUniqueIso
      (fun _ : PUnit.{u + 1} => SheafOfModules.unit U.toScheme.ringCatSheaf)).symm) x hx

/-- The stalk of a line bundle is isomorphic to the local ring: `M_x ≃ₗ[O_{X,x}] O_{X,x}`. -/
theorem nonempty_linearEquiv_stalk_of_isLineBundle {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    [M.IsLineBundle] (x : X) :
    Nonempty (M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x) := by
  obtain ⟨b⟩ := exists_basis_stalk_of_isLineBundle M x
  exact ⟨b.repr.trans (Finsupp.uniqueLinearEquiv (X.presheaf.stalk x) (X.presheaf.stalk x) PUnit.unit)⟩

end LineBundleStalkBasis

section Assembly

variable {Z Z' : AlgebraicGeometry.Scheme.{u}} (π : Z' ⟶ Z) (U : Z.Opens) [IsIso (π ∣_ U)]
  (N : Z'.Modules) [N.IsLineBundle]

/-- **General form.** `π ∣_ U` an isomorphism, `x ∈ π⁻¹U` with `y = π x` and `O_{Z, y}` a field, `N` a line
bundle on `Z'`. Then `length_{O_{Z, y}} (π_* N)_y = 1`: `(π_*N)_y ≃ N_x` `O_{Z,y}`-linearly
(`pushforwardStalkMap_bijective_of_isIso_morphismRestrict`, `pushforwardStalkMap_smul`), `π^♯_x` is surjective
(`Module.length_eq_of_surjective`), `N_x ≃ₗ O_{Z',x}` (line bundle), and `O_{Z',x} ≅ O_{Z,y}` is a field, a
simple module over itself (`Module.length_eq_one_iff`). -/
theorem length_stalk_pushforward_eq_one_of_isIso_morphismRestrict (x : Z') (hx : x ∈ π ⁻¹ᵁ U)
    {y : Z} (hy : π.base x = y) (hF : IsField (Z.presheaf.stalk y)) :
    Module.length (Z.presheaf.stalk y)
      (((AlgebraicGeometry.Scheme.Modules.pushforward π).obj N).stalk y) = 1 := by
  subst hy
  let _ := pushforwardStalkModule π N x
  let _ : Algebra (Z.presheaf.stalk (π.base x)) (Z'.presheaf.stalk x) := (π.stalkMap x).hom.toAlgebra
  have := pushforwardStalkModule_isScalarTower π N x
  have := isIso_stalkMap_of_isIso_morphismRestrict π U x hx
  have hbij : Function.Bijective (π.stalkMap x).hom := ConcreteCategory.bijective_of_isIso (π.stalkMap x)
  let e : ((AlgebraicGeometry.Scheme.Modules.pushforward π).obj N).presheaf.stalk (π.base x)
      ≃ₗ[Z.presheaf.stalk (π.base x)] N.presheaf.stalk x :=
    LinearEquiv.ofBijective
      ({ toFun := pushforwardStalkMap π N x
         map_add' := map_add _
         map_smul' := fun r m => pushforwardStalkMap_smul π N x r m } :
        ((AlgebraicGeometry.Scheme.Modules.pushforward π).obj N).presheaf.stalk (π.base x)
          →ₗ[Z.presheaf.stalk (π.base x)] N.presheaf.stalk x)
      (pushforwardStalkMap_bijective_of_isIso_morphismRestrict π U N x hx)
  obtain ⟨e2⟩ := nonempty_linearEquiv_stalk_of_isLineBundle N x
  have hS : IsField (Z'.presheaf.stalk x) :=
    (RingEquiv.ofBijective (π.stalkMap x).hom hbij).symm.toMulEquiv.isField hF
  have hsimple : IsSimpleModule (Z'.presheaf.stalk x) (Z'.presheaf.stalk x) :=
    isSimpleModule_self_iff_isUnit.mpr ⟨⟨hS.exists_pair_ne⟩, fun a ha =>
      isUnit_iff_exists_inv.mpr (hS.mul_inv_cancel ha)⟩
  have hlen : Module.length (Z.presheaf.stalk (π.base x))
      (((AlgebraicGeometry.Scheme.Modules.pushforward π).obj N).presheaf.stalk (π.base x)) = 1 := by
    rw [e.length_eq, Module.length_eq_of_surjective (S := Z.presheaf.stalk (π.base x))
      (R := Z'.presheaf.stalk x) (M := N.presheaf.stalk x) hbij.surjective, e2.length_eq,
      Module.length_eq_one_iff]
    exact hsimple
  exact hlen

end Assembly

/-- The generic stalk of `π_*N` has length one (Stacks 02O5 proof, generic-stalk
step; Stacks 00AE / Mathlib `stalkPushforward_iso_of_isInducing` for the stalk of a pushforward along a
homeomorphism onto an open). `Z` integral, `π : Z' → Z`, `U` a nonempty open of `Z` with `IsIso (π ∣_ U)`, `N` a
line bundle on `Z'`. Then `Module.length (O_{Z,η}) ((π_*N)_η) = 1` at the generic point `η` of `Z`.

**Natural-language proof.**
1. *`η ∈ U`.* `Z` is irreducible (`IsIntegral → IrreducibleSpace`) and `U` is a nonempty open, so the generic
   point lies in `U` (Mathlib `genericPoint_spec.mem_open_set_iff U.isOpen`, with `Set.univ ∩ U = U` nonempty).
   Since `π ∣_ U : π⁻¹U → U` is an isomorphism, its underlying map is bijective, so `η = π η'` for some
   `η' ∈ π⁻¹U` (`morphismRestrict_base_coe`).
2. *The stalk of the pushforward.* The pushforward stalk map `(π_*N)_η → N_{η'}` (Mathlib `stalkPushforward`;
   on germs `[s ∈ Γ(N, π⁻¹W)]_η ↦ [s]_{η'}`) is bijective: the opens `W' ⊆ π⁻¹U` containing `η'` and the opens
   `W ⊆ U` containing `η` correspond under `W' ↦ π(W')`, `W ↦ π⁻¹W` — `(π⁻¹U).ι ≫ π = (π ∣_ U) ≫ U.ι` is an open
   immersion, so `π(W')` is open and `π⁻¹(π(W')) = W'` — hence every germ at `η'` is represented on some `π⁻¹W`,
   and a section of `N(π⁻¹W)` vanishing near `η'` vanishes on some `π⁻¹W₀`, `W₀ ⊆ W` open around `η`
   (`pushforwardStalkMap_bijective_of_isIso_morphismRestrict`). The bijection is `O_{Z,η}`-linear when
   `O_{Z,η}` acts on `N_{η'}` through the stalk map `π^♯_{η'} : O_{Z,η} → O_{Z',η'}` (`pushforwardStalkMap_smul`,
   `pushforwardStalkModule`; the identification of `Scheme.Modules.stalk` with the `TopCat.Presheaf.stalk` of
   the underlying abelian sheaf is `ModuleSheafStalk`).
3. *`π^♯_{η'}` is a ring isomorphism.* `((π⁻¹U).ι ≫ π).stalkMap η' = π.stalkMap η' ≫ (π⁻¹U).ι.stalkMap η'`
   (Mathlib `Scheme.Hom.stalkMap_comp`); the outer two are isomorphisms (stalk maps of open immersions), so
   `π^♯_{η'}` is one (`isIso_stalkMap_of_isIso_morphismRestrict`). Hence `O_{Z,η} ≅ O_{Z',η'}` as rings, and
   lengths are unchanged under restriction of scalars along the surjection `π^♯_{η'}`
   (`Module.length_eq_of_surjective`).
4. *The stalk of a line bundle is free of rank one.* `N` is a line bundle, so there is an open `W' ∋ η'` with
   `N|_{W'} ≅ O_{W'}` (`IsLineBundle.locally_trivial`); the stalk of `O_{W'} = O^{(PUnit)}`
   at `η'` has a `PUnit`-indexed basis (`FreeModuleStalkBasisSpan`), transported to `N_{η'}` along
   the stalk functor and the semilinear equivalence `(N|_{W'})_{η'} ≃ N_{η'}` (`moduleRestrictStalkEquiv`,
   `basis_of_semilinearEquiv`), so `N_{η'} ≃ₗ[O_{Z',η'}] O_{Z',η'}` (`nonempty_linearEquiv_stalk_of_isLineBundle`).
5. *Length one.* `O_{Z,η}` is a field (Mathlib `Scheme.functionField`, `IsIntegral Z` ⇒ `Field Z.functionField`,
   and `Z.functionField` is an `abbrev` for `Z.presheaf.stalk (genericPoint Z)`), hence so is `O_{Z',η'}`
   (`MulEquiv.isField`); a field is a simple module over itself (`isSimpleModule_self_iff_isUnit`), so
   `Module.length O_{Z',η'} O_{Z',η'} = 1` (Mathlib `Module.length_eq_one_iff`), and lengths are invariant under
   linear equivalences (`LinearEquiv.length_eq`). Composing steps 2–4:
   `length_{O_{Z,η}} (π_*N)_η = length_{O_{Z,η}} N_{η'} = length_{O_{Z',η'}} N_{η'} = length_{O_{Z',η'}} O_{Z',η'} = 1`.

**Edge cases.** `U = ⊤`: `π` is an isomorphism, `π_*N` is a line bundle on `Z`, the statement is
"a line bundle has one-dimensional generic stalk". `Z` a point: `Z = Spec K`, `U = Z`, `Z' ≅ Z`, `N ≅ O`,
`length_K K = 1`. `Z'` disconnected or non-reduced away from `π⁻¹U`: irrelevant, only `π⁻¹U` matters.
`N = 0` is impossible for a line bundle on the nonempty `Z'` (`π⁻¹U ≠ ∅`). -/
theorem length_stalk_pushforward_genericPoint_eq_one_of_isIso_morphismRestrict
    {Z Z' : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral Z] (π : Z' ⟶ Z)
    (N : Z'.Modules) [N.IsLineBundle] (U : Z.Opens) (hU : (U : Set Z).Nonempty)
    [CategoryTheory.IsIso (π ∣_ U)] :
    Module.length (Z.presheaf.stalk (genericPoint Z))
      (((pushforward π).obj N).stalk (genericPoint Z)) = 1 := by
  have hη : genericPoint Z ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  obtain ⟨v, hv⟩ := (ConcreteCategory.bijective_of_isIso (π ∣_ U).base).2 ⟨genericPoint Z, hη⟩
  have hxη : π.base v.1 = genericPoint Z := by
    rw [← morphismRestrict_base_coe π U v, hv]
  exact length_stalk_pushforward_eq_one_of_isIso_morphismRestrict π U N v.1 v.2 hxη
    (Field.toIsField Z.functionField)

end AlgebraicGeometry.Scheme.Modules

end
