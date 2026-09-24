import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualRestrictOpen
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeTangentLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualPullbackCommute
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.SheafDualLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaFiniteType
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaOpenImmersionSquare
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualFunctor

/-! # `E^∨ ≅ s^*Ω_{Z/C}` on the smooth locus

`E := coneTangentBundle p s hs = s^*T_{Z/C} = s^*(Ω_{Z/C}^∨)`. If the section `s : C → Z`
lands in an open `Zx ⊆ Z` that is smooth over `C`, then the dual of `E` is the pullback of the relative
differentials: `E^∨ ≅ s^*Ω_{Z/C}`. This identifies the linear pieces of the jet algebra (jet coordinates
are the coefficients of functions, i.e. differentials at `s`) with `E^∨`, and it is the second half of
the identification `I/I² ≅ E^∨` of the conormal module (whose first half `I/I² ≅ s^*Ω` is Stacks 0474).

Source: §2.2 of the paper (`I/I² = E^∨|_U`); Stacks 01US (Ω and open subschemes),
01CM/01CN (dual commutes with pullback for finite locally free modules, double dual).

**Proof** (the same steps as `coneTangentBundle_exists_affine_frame`,
`ConeTangentBundleLocalFrame.lean`). Write `p : Z → C`, `q := Zx.ι ≫ p : Zx → C` (smooth).
1. `s` factors through `Zx`: `s = s' ≫ Zx.ι` (`IsOpenImmersion.lift`).
2. `Zx.ι^*Ω_{Z/C} ≅ Ω_{Zx/C}` (Stacks 01US, `Omega.restrictIso` with `restrictFunctorIsoPullback`), hence
   `Zx.ι^*T_{Z/C} ≅ T_{Zx/C}` (`dual_restrict`, functoriality of the dual), and
   `E = s^*T_{Z/C} ≅ s'^*Zx.ι^*T_{Z/C} ≅ s'^*T_{Zx/C}` (`pullbackCongr`, `pullbackComp`).
3. `Ω_{Zx/C}` is locally free of finite type (`isLocallyFree_omega_of_smooth`, `Omega_isFiniteType`), so its dual
   `T_{Zx/C}` is too (`isLocallyFree_dual'`, `isFiniteType_dual`), and
   `E^∨ ≅ (s'^*T_{Zx/C})^∨ ≅ s'^*(T_{Zx/C}^∨) = s'^*(Ω_{Zx/C}^∨∨) ≅ s'^*Ω_{Zx/C}` (`dual_pullback`, `dual_dual`).
4. Back along step 2: `s'^*Ω_{Zx/C} ≅ s'^*Zx.ι^*Ω_{Z/C} ≅ s^*Ω_{Z/C}`.
Only `Smooth (Zx.ι ≫ p)` is used (no relative dimension, no closed-immersion hypothesis on `s`).
Edge cases: `Zx = ⊤` (then `hsZx` is trivial and the lemma says `E^∨ ≅ s^*Ω` for `Z` smooth over `C`); `C` empty (both
sides `0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **`E^∨ ≅ s^*Ω_{Z/C}` on the smooth locus.** If the section `s` of `p : Z → C` lands in an open `Zx ⊆ Z` smooth over
`C`, then the dual of `E = coneTangentBundle p s hs = s^*(Ω_{Z/C}^∨)` is `s^*Ω_{Z/C}`. See the module docstring for the
proof (Stacks 01US + dual/pullback commutation for finite locally free modules + double dual). -/
theorem dual_coneTangentBundle_iso_pullback_omega
    {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    {Z : AlgebraicGeometry.Scheme.{u}} (p : Z ⟶ C.toScheme) (s : C.toScheme ⟶ Z)
    (hs : s ≫ p = CategoryTheory.CategoryStruct.id C.toScheme)
    (Zx : Z.Opens) (hsZx : ∀ c, s.base c ∈ Zx) [AlgebraicGeometry.Smooth (Zx.ι ≫ p)] :
    Nonempty (AlgebraicGeometry.Scheme.Modules.dual (coneTangentBundle p s hs) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback s).obj (AlgebraicGeometry.Omega p)) := by
  -- Step 1: factor `s` through the open `Zx`.
  have hrange : Set.range s.base ⊆ Set.range Zx.ι.base := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    rintro _ ⟨c, rfl⟩
    exact hsZx c
  obtain ⟨s', hfac⟩ : ∃ s' : C.toScheme ⟶ Zx.toScheme, s' ≫ Zx.ι = s :=
    ⟨_, AlgebraicGeometry.IsOpenImmersion.lift_fac Zx.ι s hrange⟩
  let q : Zx.toScheme ⟶ C.toScheme := Zx.ι ≫ p
  -- Step 2: `Ω_{Z/C}|_{Zx} ≅ Ω_{Zx/C}` (Stacks 01US) and `T_{Z/C}|_{Zx} ≅ T_{Zx/C}`.
  have eΩ : (AlgebraicGeometry.Scheme.Modules.pullback Zx.ι).obj (AlgebraicGeometry.Omega p) ≅
      AlgebraicGeometry.Omega q :=
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback Zx.ι).symm.app _ ≪≫
      AlgebraicGeometry.Omega.restrictIso p q Zx.ι (𝟙 C.toScheme) (Category.comp_id q)
  obtain ⟨eD⟩ := AlgebraicGeometry.Scheme.Modules.dual_restrict (AlgebraicGeometry.Omega p) Zx
  have eT : (AlgebraicGeometry.Scheme.Modules.pullback Zx.ι).obj (AlgebraicGeometry.relativeTangent p) ≅
      AlgebraicGeometry.relativeTangent q :=
    eD ≪≫ AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso eΩ.symm
  -- `E ≅ s'^* T_{Zx/C}`.
  have eE : coneTangentBundle p s hs ≅
      (AlgebraicGeometry.Scheme.Modules.pullback s').obj (AlgebraicGeometry.relativeTangent q) :=
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr hfac.symm).app _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp s' Zx.ι).symm.app _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback s').mapIso eT
  -- Step 3: `Ω_{Zx/C}` and `T_{Zx/C}` are finite locally free.
  have hΩlf : (AlgebraicGeometry.Omega q).IsLocallyFree := AlgebraicGeometry.isLocallyFree_omega_of_smooth q
  have hΩft : (AlgebraicGeometry.Omega q).IsFiniteType := AlgebraicGeometry.Omega_isFiniteType q
  have hTlf : (AlgebraicGeometry.relativeTangent q).IsLocallyFree :=
    AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual' (AlgebraicGeometry.Omega q)
  have hTft : (AlgebraicGeometry.relativeTangent q).IsFiniteType :=
    AlgebraicGeometry.Scheme.Modules.isFiniteType_dual (AlgebraicGeometry.Omega q) hΩlf
  obtain ⟨e1⟩ := AlgebraicGeometry.Scheme.Modules.dual_pullback s' (AlgebraicGeometry.relativeTangent q)
  obtain ⟨e2⟩ := AlgebraicGeometry.Scheme.Modules.dual_dual (AlgebraicGeometry.Omega q)
  -- Assemble: `E^∨ ≅ (s'^*T)^∨ ≅ s'^*(T^∨) = s'^*(Ω^∨∨) ≅ s'^*Ω_{Zx/C} ≅ s'^*Zx.ι^*Ω_{Z/C} ≅ s^*Ω_{Z/C}`.
  refine ⟨AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso eE.symm ≪≫ e1 ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback s').mapIso e2 ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback s').mapIso eΩ.symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp s' Zx.ι).app _ ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr hfac).app _⟩

end
