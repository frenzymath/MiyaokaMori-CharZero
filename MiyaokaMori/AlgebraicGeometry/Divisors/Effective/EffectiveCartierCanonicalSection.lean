import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrame

/-! # The canonical section of an effective Cartier divisor

Let `D` be an effective Cartier divisor on a scheme `X` and `1_D ∈ Γ(X, O_X(D))` its canonical section
(`EffectiveCartierDivisor.canonicalSection`). Then (a) `1_D` is a regular section: for every open `U`,
`r ↦ r·1_D|_U` is injective `Γ(X, U) → Γ(O(D), U)`; (b) `1_D ≠ 0` when `X` is nonempty; (c) the zero
scheme of `1_D` is `D`: `idealSheafOfSection O(D) 1_D = I_D`.

Proof sketch:
1. Local structure. `Γ(U, O(D)) = Γ(U, I_D^∨)` is by definition the module of compatible families of
   local functionals on `I_D|_U`; `1_D` is the family of components of the inclusion `ι = kernel.ι`
   (`canonicalSection_eq`, `restrict_canonicalSection`).
2. Local frames (`exists_local_frame`). A line bundle `M` has, at every point, an open `W` and
   `f ∈ Γ(M, W)` such that on every open `W' ≤ W` the map `r ↦ r·f|_{W'}` is bijective
   `Γ(X, W') → Γ(M, W')`: take a trivialization `φ : M|_V ≅ O_V`, `W = V`, `f = φ⁻¹(1)`.
3. For `M = I_D` and a frame `(W, f)`, put `g = ι(f) ∈ Γ(X, W)`. Since `ι` is injective on every open,
   (i) `s·g = 0` implies `s = 0` (`IsFrame.regular`); (ii) every `x ∈ Γ(I_D, W)` has a unique `t` with
   `ι(x) = t·g` (`IsFrame.quot`).
4. (a): if `r·1_D|_U = r'·1_D|_U`, then for `p ∈ U` take a frame `(W ≤ U, f)`; evaluating at `f` gives
   `(r|_W − r'|_W)·g = 0`, so `r|_W = r'|_W` by 3(i), and `r = r'` since `O_X` is a sheaf.
5. (b): take `U = ⊤` in (a); if `1_D = 0` then `1·1_D = 0·1_D`, so `1 = 0` in `Γ(X, ⊤)`, contradicting
   `X ≠ ∅`.
6. (c): affine opens with a frame cover `X`, so by `IdealSheafData.ext_of_iSup_eq_top` it suffices to
   compare on such an affine `W`. There `I_D(W) = range ι_W = (g)` by 3(ii). Conversely,
   `θ₀ := (x ↦ ι(x)/g)` (defined on each `V ≤ W` by the uniqueness in 3(ii)) is a compatible family of
   local functionals with `incl_W = g·θ₀`, so every linear `φ : Γ(O(D), W) → Γ(X, W)` has
   `φ(1_D|_W) = g·φ(θ₀) ∈ (g)`; and `φ = ev_f` gives `φ(1_D|_W) = ι(f) = g`. Hence
   `idealSheafOfSection` is `(g)` on `W` as well.
Sources: Stacks 01WX (regular sections and effective Cartier divisors; the zero scheme of `1_D` is
`D`), 01X0.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.EffectiveCartierCanonicalSection

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules MiyaokaMori.ModuleDualSectionEquiv
-- `IsFrame` is `AlgebraicGeometry.Scheme.Modules.IsFrame`; the helpers below are declared in its
-- namespace so that dot notation works.
open AlgebraicGeometry.Scheme.Modules (IsFrame)

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

/-- The inclusion `I ↪ O_X`. -/
abbrev incl (I : X.IdealSheafData) : I.toModules ⟶ SheafOfModules.unit X.ringCatSheaf :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)

/-- The component of the inclusion on an open `W`, as a `Γ(X, W)`-linear map `Γ(I, W) → Γ(X, W)`. -/
def iota (I : X.IdealSheafData) (W : X.Opens) : Γ(I.toModules, W) →ₗ[Γ(X, W)] Γ(X, W) where
  toFun := fun x => (incl I).val.app (op W) x
  map_add' := fun x y => map_add _ x y
  map_smul' := fun r x => ((incl I).val.app (op W)).hom.map_smul r x

theorem iota_map (I : X.IdealSheafData) {W' W : X.Opens} (i : W' ⟶ W) (x : Γ(I.toModules, W)) :
    iota I W' (I.toModules.presheaf.map i.op x) = X.presheaf.map i.op (iota I W x) :=
  PresheafOfModules.naturality_apply (incl I).val i.op x

theorem iota_injective (I : X.IdealSheafData) (W : X.Opens) : Function.Injective (iota I W) := by
  have : Mono ((SheafOfModules.evaluation X.ringCatSheaf (op W)).map (incl I)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).mp this

/-- The family of components of the inclusion on the opens inside `U`, as a compatible family of local
functionals. -/
def inclFamily (I : X.IdealSheafData) (U : X.Opens) : LocalDualSections X I.toModules U :=
  ⟨fun V => iota I V.left, fun _ _ i x => iota_map I i.left x⟩

/-- The internal Hom presheaf into `O_X` is the dual presheaf. -/
theorem internalHomPresheaf_unit_eq (M : X.Modules) :
    Scheme.Modules.internalHomPresheaf M (SheafOfModules.unit X.ringCatSheaf : X.Modules) =
      moduleDualPresheaf M := rfl

theorem unit_app_heq {P Q : X.PresheafOfModules} (h : P = Q) (x : P.obj (op ⊤)) (y : Q.obj (op ⊤))
    (hxy : HEq x y) :
    HEq (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P).app (op ⊤) x)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app Q).app (op ⊤) y) := by
  subst h
  rw [eq_of_heq hxy]

/-- Compatible families of local functionals are the sections `Γ(U, M^∨)` of `dualSheaf M`. Since
`dualSheaf` is not sheafified, `Γ(U, M^∨)` is by definition the module of compatible families, and this
equivalence is the identity. -/
def dualSecEquiv (M : X.Modules) (U : X.Opens) :
    LocalDualSections X M U ≃ₗ[Γ(X, U)] Γ(Scheme.Modules.dualSheaf M, U) :=
  (Scheme.Modules.dualSheafSections M U).symm

theorem dualSecEquiv_restrict (M : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (φ : LocalDualSections X M U) :
    (Scheme.Modules.dualSheaf M).presheaf.map i.op (dualSecEquiv M U φ) =
      dualSecEquiv M V (localDualRestrict M i φ) := rfl

/-- `1_D` is the family of inclusion maps. -/
theorem canonicalSection_eq (D : EffectiveCartierDivisor X) :
    D.canonicalSection = dualSecEquiv D.idealSheaf.toModules ⊤ (inclFamily D.idealSheaf ⊤) := by
  apply Subtype.ext; funext V; apply LinearMap.ext; intro x; with_unfolding_all rfl

/-- `1_D|_U` is the family of inclusion maps on the opens inside `U`. -/
theorem restrict_canonicalSection (D : EffectiveCartierDivisor X) (U : X.Opens) :
    ((D.lineBundle.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom D.canonicalSection :
        Γ(D.lineBundle, U)) =
      dualSecEquiv D.idealSheaf.toModules U (inclFamily D.idealSheaf U) := by
  apply Subtype.ext; funext V; apply LinearMap.ext; intro x; with_unfolding_all rfl

/-- Local frames of a line bundle: every point has an open neighbourhood `W` and `f ∈ Γ(M, W)` such that
for every open `W' ≤ W` the map `r ↦ r • f|_{W'}` is bijective. -/
theorem exists_local_frame (M : X.Modules) [M.IsLineBundle] (p : X) :
    ∃ (W : X.Opens) (_ : p ∈ W) (f : Γ(M, W)), ∀ (W' : X.Opens) (h : W' ≤ W),
      Function.Bijective (fun r : Γ(X, W') => r • (M.presheaf.map (homOfLE h).op f : Γ(M, W'))) := by
  obtain ⟨V, hp, ⟨φ⟩⟩ := SheafOfModules.IsLineBundle.locally_trivial (M := M) p
  refine ⟨V.ι ''ᵁ ⊤, by simpa using hp,
    (φ.inv.val.app (op ⊤) (1 : Γ(V.toScheme, ⊤)) : Γ(M, V.ι ''ᵁ ⊤)), ?_⟩
  intro W' h
  obtain ⟨O, rfl⟩ : ∃ O : V.toScheme.Opens, W' = V.ι ''ᵁ O :=
    ⟨V.ι ⁻¹ᵁ W', by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact (inf_eq_right.mpr (h.trans (by simp))).symm⟩
  have hnat : (M.presheaf.map (homOfLE h).op
        (φ.inv.val.app (op ⊤) (1 : Γ(V.toScheme, ⊤)) : Γ(M, V.ι ''ᵁ ⊤)) : Γ(M, V.ι ''ᵁ O)) =
      φ.inv.val.app (op O) (1 : Γ(V.toScheme, O)) := by
    have := PresheafOfModules.naturality_apply φ.inv.val (homOfLE (le_top : O ≤ ⊤)).op
      (1 : Γ(V.toScheme, ⊤))
    have h1 : (ConcreteCategory.hom ((SheafOfModules.unit V.toScheme.ringCatSheaf).val.map
        (homOfLE (le_top : O ≤ ⊤)).op)) (1 : Γ(V.toScheme, ⊤)) = (1 : Γ(V.toScheme, O)) :=
      map_one (V.toScheme.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom
    exact this.symm.trans (congrArg _ h1)
  have key : ∀ r : Γ(X, V.ι ''ᵁ O),
      r • (M.presheaf.map (homOfLE h).op
        (φ.inv.val.app (op ⊤) (1 : Γ(V.toScheme, ⊤)) : Γ(M, V.ι ''ᵁ ⊤)) : Γ(M, V.ι ''ᵁ O)) =
      φ.inv.val.app (op O) (show Γ(V.toScheme, O) from r) := by
    intro r
    rw [hnat]
    have := (φ.inv.val.app (op O)).hom.map_smul (show Γ(V.toScheme, O) from r) (1 : Γ(V.toScheme, O))
    have h2 : (show Γ(V.toScheme, O) from r) • (1 : Γ(V.toScheme, O)) = (show Γ(V.toScheme, O) from r) :=
      mul_one _
    refine Eq.trans ?_ (this.symm.trans (congrArg _ h2))
    have hs : ∀ y : Γ(M.restrict V.ι, O), (show Γ(V.toScheme, O) from r) • y =
        (((V.ι.appIso O).inv (show Γ(V.toScheme, O) from r) : Γ(X, V.ι ''ᵁ O)) •
          (show Γ(M, V.ι ''ᵁ O) from y) : Γ(M, V.ι ''ᵁ O)) := fun _ => rfl
    have hr : ((V.ι.appIso O).inv (show Γ(V.toScheme, O) from r) : Γ(X, V.ι ''ᵁ O)) = r := by
      rw [Scheme.Opens.ι_appIso]; rfl
    refine Eq.trans ?_ (hs _).symm
    rw [hr]
  have hbij : Function.Bijective (φ.inv.val.app (op O)) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨φ.hom.val.app (op O), fun x => ?_, fun x => ?_⟩
    · exact ConcreteCategory.congr_hom
        (congrArg (fun k : SheafOfModules.unit V.toScheme.ringCatSheaf ⟶ _ => k.val.app (op O))
          φ.inv_hom_id) x
    · exact ConcreteCategory.congr_hom
        (congrArg (fun k : M.restrict V.ι ⟶ _ => k.val.app (op O)) φ.hom_inv_id) x
  rw [funext key]
  exact hbij

-- (`IsFrame` and `IsFrame.restrict`: see `AlgebraicGeometry.Scheme.Modules.IsFrame`, `IsFrame.restrict`.)

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsFrame.regular {I : X.IdealSheafData} {W : X.Opens}
    {f : Γ(I.toModules, W)}
    (hf : IsFrame I.toModules W f) (s : Γ(X, W)) (hs : s * iota I W f = 0) : s = 0 := by
  have h1 : iota I W (s • f) = iota I W 0 := by
    rw [_root_.map_smul, map_zero]; exact hs
  have h2 := iota_injective I W h1
  have hb := (hf W le_rfl).1
  apply hb
  show s • _ = (0 : Γ(X, W)) • _
  rw [Scheme.Modules.res_self, h2, zero_smul]

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsFrame.exists_mul {I : X.IdealSheafData} {W : X.Opens}
    {f : Γ(I.toModules, W)}
    (hf : IsFrame I.toModules W f) (x : Γ(I.toModules, W)) : ∃ t : Γ(X, W), iota I W x = t * iota I W f := by
  obtain ⟨t, ht⟩ := (hf W le_rfl).2 x
  refine ⟨t, ?_⟩
  have ht' : t • f = x := by simpa only [Scheme.Modules.res_self] using ht
  rw [← ht', _root_.map_smul]; rfl

theorem exists_frame_le (M : X.Modules) [M.IsLineBundle] {U : X.Opens} {p : X} (hp : p ∈ U) :
    ∃ (W : X.Opens) (_ : W ≤ U) (_ : p ∈ W) (f : Γ(M, W)), IsFrame M W f := by
  obtain ⟨W, hpW, f, hf⟩ := exists_local_frame M p
  exact ⟨W ⊓ U, inf_le_right, ⟨hpW, hp⟩, _, IsFrame.restrict (M := M) (W := W) (e := f) hf inf_le_left⟩

theorem smul_family_apply {M : X.Modules} {U : X.Opens} (r : Γ(X, U))
    (θ : LocalDualSections X M U) (V : Over U) (x : Γ(M, V.left)) :
    (r • θ).1 V x = X.presheaf.map V.hom.op r * θ.1 V x := rfl

theorem regular_core (I : X.IdealSheafData) [I.toModules.IsLineBundle] (U : X.Opens)
    (r r' : Γ(X, U)) (h : r • inclFamily I U = r' • inclFamily I U) : r = r' := by
  have key : ∀ p : U, ∃ (W : X.Opens) (i : W ⟶ U), p.1 ∈ W ∧
      X.presheaf.map i.op r = X.presheaf.map i.op r' := by
    rintro ⟨p, hp⟩
    obtain ⟨W, hWU, hpW, f, hf⟩ := exists_frame_le I.toModules hp
    refine ⟨W, homOfLE hWU, hpW, ?_⟩
    have h1 : (r • inclFamily I U).1 (Over.mk (homOfLE hWU)) f =
        (r' • inclFamily I U).1 (Over.mk (homOfLE hWU)) f := by rw [h]
    rw [smul_family_apply, smul_family_apply] at h1
    have h2 : (X.presheaf.map (homOfLE hWU).op r - X.presheaf.map (homOfLE hWU).op r') *
        iota I W f = 0 := by
      rw [sub_mul]; exact sub_eq_zero.mpr h1
    exact sub_eq_zero.mp (hf.regular _ h2)
  choose W i hpW hW using key
  exact X.sheaf.eq_of_locally_eq' W U i
    (fun p hp => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hpW _⟩) r r' hW

section Quot

variable {I : X.IdealSheafData} {W : X.Opens} {f : Γ(I.toModules, W)}

/-- The coordinate of `x` in the frame: `ι(x) = quot x * ι(f)`. This is the coordinate `IsFrame.coord`
(at `W ≤ W`). -/
def _root_.AlgebraicGeometry.Scheme.Modules.IsFrame.quot (hf : IsFrame I.toModules W f)
    (x : Γ(I.toModules, W)) : Γ(X, W) :=
  hf.coord le_rfl x

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsFrame.quot_spec (hf : IsFrame I.toModules W f)
    (x : Γ(I.toModules, W)) :
    iota I W x = hf.quot x * iota I W f := by
  have h := hf.coord_smul_frame le_rfl x
  simp only [Scheme.Modules.res_self] at h
  conv_lhs => rw [← h]
  rw [_root_.map_smul]; rfl

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsFrame.quot_unique (hf : IsFrame I.toModules W f) (x : Γ(I.toModules, W)) (t : Γ(X, W))
    (h : iota I W x = t * iota I W f) : hf.quot x = t := by
  have h2 : (hf.quot x - t) * iota I W f = 0 := by
    rw [sub_mul, ← hf.quot_spec x, h, sub_self]
  exact sub_eq_zero.mp (hf.regular _ h2)

/-- The compatible family of local functionals `θ₀`, "division by `ι(f)`". -/
def _root_.AlgebraicGeometry.Scheme.Modules.IsFrame.invFamily (hf : IsFrame I.toModules W f) : LocalDualSections X I.toModules W :=
  ⟨fun V =>
    { toFun := fun x => (hf.restrict V.hom.le).quot x
      map_add' := fun x y => by
        apply IsFrame.quot_unique
        rw [map_add, add_mul, ← IsFrame.quot_spec, ← IsFrame.quot_spec]
      map_smul' := fun r x => by
        apply IsFrame.quot_unique
        rw [_root_.map_smul, RingHom.id_apply, smul_eq_mul, smul_eq_mul, mul_assoc, ← IsFrame.quot_spec] },
   by
    intro V V' i x
    refine IsFrame.quot_unique (hf.restrict V.hom.le) _ _ ?_
    rw [iota_map, (hf.restrict V'.hom.le).quot_spec x, map_mul, ← iota_map]
    congr 2
    rw [← ConcreteCategory.comp_apply, ← I.toModules.presheaf.map_comp]
    rfl⟩

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsFrame.inclFamily_eq (hf : IsFrame I.toModules W f) :
    inclFamily I W = iota I W f • hf.invFamily := by
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro x
  rw [smul_family_apply]
  show iota I V.left x = _
  rw [(hf.restrict V.hom.le).quot_spec x, ← iota_map, mul_comm]
  rfl

/-- Evaluation at `f` on `Over.mk (𝟙 W)`. -/
def evalAt (M : X.Modules) (W : X.Opens) (f : Γ(M, W)) :
    LocalDualSections X M W →ₗ[Γ(X, W)] Γ(X, W) where
  toFun := fun θ => θ.1 (Over.mk (𝟙 W)) f
  map_add' := fun _ _ => rfl
  map_smul' := fun r θ => by
    rw [smul_family_apply]
    show X.presheaf.map (𝟙 W).op r * _ = _
    rw [op_id, X.presheaf.map_id]
    rfl

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsFrame.ideal_eq (hf : IsFrame I.toModules W f) (hW : IsAffineOpen W) :
    I.ideal ⟨W, hW⟩ = Ideal.span {iota I W f} := by
  have hr := I.range_toModules_ι_app ⟨W, hW⟩
  ext a
  rw [Ideal.mem_span_singleton', ← SetLike.mem_coe, ← hr]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨t, ht⟩ := hf.exists_mul x
    exact ⟨t, ht.symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t • f, (_root_.map_smul (iota I W) t f)⟩

end Quot

theorem ideal_ofSection_eq (D : EffectiveCartierDivisor X) {W : X.Opens} (hW : IsAffineOpen W)
    {f : Γ(D.idealSheaf.toModules, W)} (hf : IsFrame D.idealSheaf.toModules W f) :
    (Scheme.idealSheafOfSection D.lineBundle D.canonicalSection).ideal ⟨W, hW⟩ =
      D.idealSheaf.ideal ⟨W, hW⟩ := by
  rw [hf.ideal_eq hW]
  let e : LocalDualSections X D.idealSheaf.toModules W ≃ₗ[Γ(X, W)] Γ(D.lineBundle, W) :=
    dualSecEquiv D.idealSheaf.toModules W
  have hres : ((D.lineBundle.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom D.canonicalSection :
      Γ(D.lineBundle, W)) = e (inclFamily D.idealSheaf W) := restrict_canonicalSection D W
  show Ideal.span (Set.range fun φ : Γ(D.lineBundle, W) →ₗ[Γ(X, W)] Γ(X, W) =>
    φ ((D.lineBundle.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom D.canonicalSection)) = _
  rw [hres]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨φ, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_span_singleton']
    refine ⟨φ (e hf.invFamily), ?_⟩
    show _ = φ (e (inclFamily D.idealSheaf W))
    rw [hf.inclFamily_eq, _root_.map_smul, _root_.map_smul, smul_eq_mul, mul_comm]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    apply Ideal.subset_span
    refine ⟨(evalAt D.idealSheaf.toModules W f).comp e.symm.toLinearMap, ?_⟩
    show evalAt D.idealSheaf.toModules W f (e.symm (e (inclFamily D.idealSheaf W))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl

end MiyaokaMori.EffectiveCartierCanonicalSection

open AlgebraicGeometry in

/-- (a) The canonical section `1_D` is a regular section. Valid on any scheme, without integrality. -/
theorem AlgebraicGeometry.EffectiveCartierDivisor.canonicalSection_regular
    {X : AlgebraicGeometry.Scheme.{u}} (D : AlgebraicGeometry.EffectiveCartierDivisor X) :
    ∀ U : X.Opens, Function.Injective (fun r : Γ(X, U) =>
        r • ((D.lineBundle.presheaf.map (CategoryTheory.homOfLE (le_top : U ≤ ⊤)).op).hom
          D.canonicalSection : Γ(D.lineBundle, U))) := by
  intro U r r' h
  have := D.isLineBundle
  dsimp only at h
  rw [MiyaokaMori.EffectiveCartierCanonicalSection.restrict_canonicalSection] at h
  erw [← map_smul, ← map_smul] at h
  exact MiyaokaMori.EffectiveCartierCanonicalSection.regular_core _ U r r'
    ((MiyaokaMori.EffectiveCartierCanonicalSection.dualSecEquiv _ U).injective h)

open AlgebraicGeometry in

/-- (b) `1_D ≠ 0` when `X` is nonempty. -/
theorem AlgebraicGeometry.EffectiveCartierDivisor.canonicalSection_ne_zero
    {X : AlgebraicGeometry.Scheme.{u}} [Nonempty X]
    (D : AlgebraicGeometry.EffectiveCartierDivisor X) :
    D.canonicalSection ≠ 0 := by
  intro h0
  have hinj := D.canonicalSection_regular ⊤
  have hm : ((D.lineBundle.presheaf.map (CategoryTheory.homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op).hom
      D.canonicalSection : Γ(D.lineBundle, ⊤)) = 0 := by
    rw [h0]; exact map_zero _
  have h10 : (1 : Γ(X, ⊤)) = 0 := by
    apply hinj
    show (1 : Γ(X, ⊤)) • _ = (0 : Γ(X, ⊤)) • _
    rw [hm, smul_zero, smul_zero]
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  have : Nontrivial Γ(X, ⊤) := X.component_nontrivial ⊤
  exact one_ne_zero h10

/-- (c) The zero scheme of `1_D` is `D`: `idealSheafOfSection O(D) 1_D = I_D`. -/
theorem AlgebraicGeometry.EffectiveCartierDivisor.idealSheafOfSection_canonicalSection
    {X : AlgebraicGeometry.Scheme.{u}} (D : AlgebraicGeometry.EffectiveCartierDivisor X) :
    AlgebraicGeometry.Scheme.idealSheafOfSection D.lineBundle D.canonicalSection = D.idealSheaf := by
  have := D.isLineBundle
  refine AlgebraicGeometry.Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := {A : X.affineOpens // ∃ f : Γ(D.idealSheaf.toModules, A.1),
      AlgebraicGeometry.Scheme.Modules.IsFrame D.idealSheaf.toModules A.1 f})
    (fun A => A.1) ?_ ?_
  · rw [eq_top_iff]
    intro p _
    obtain ⟨W, -, hpW, f, hf⟩ :=
      MiyaokaMori.EffectiveCartierCanonicalSection.exists_frame_le D.idealSheaf.toModules
        (U := ⊤) (p := p) trivial
    obtain ⟨A, hA, hpA, hAW⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hpW
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨A, hA⟩, _, hf.restrict hAW⟩, hpA⟩
  · rintro ⟨⟨A, hA⟩, f, hf⟩
    exact MiyaokaMori.EffectiveCartierCanonicalSection.ideal_ofSection_eq D hA hf

end
