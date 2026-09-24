import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialFrameLocalSections
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialFramePureTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialFrameCoefficient
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialFrameSymPower
import MiyaokaMori.Paper.S3PositiveLine.Realization.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialFrameTautological

/-! # Restriction of the monomials `c·ξ^q` to a fibre, in frame trivializations

In frame trivializations of `L` and `M` near a point `y`, the monomial `c·ξ^q ∈ Γ(Tot(L), p^*M)`
(`xiMonomial L M q c`, `c ∈ Γ(C, M ⊗ L^{-q})`) restricts to the fiber `Tot(L)_y` as
`const(c(y)) · (ξ|_{Tot(L)_y})^q`, with `c(y) ∈ κ(y)` and `const : κ(y) → Γ(Tot(L)_y, O)` the constants
(`Scheme.Hom.fiberResidueConstants`). (In the paper: the expansion `P = Σ_q c_q ξ^q` and its restriction
to the fiber.)

The statement is over `κ(y)` for an arbitrary point `y` and chooses its own trivializations (the module
`…FrameCoordinateMonomial` reconciles them with the coordinate of `…MonomialRingEquiv` by a unit).

`totalSpace_fiber_exists_trivializations_xiMonomial` is assembled from:
* glue (modules `…MonomialFrameLocalSections`, `…MonomialFramePureTensor`, `…MonomialFrameCoefficient`):
  pullback of local sections to the fiber and its linearity, pulled-back frames and their trivializations, the
  constants `(i ≫ p)^♯(r) = const(r(y))`; the projection formula on pure tensors over an open and the monomial
  map on pure tensors; the restriction of `xiMonomial` to `p⁻¹V`; frames of tensor products (`η ⊗ t^{⊗q}` is a
  frame of `M ⊗ (L^∨)^{⊗q}`);
* `totalSpace.monomialUnit_app_moduleTensorPowerSection` (module `…MonomialFrameSymPower`): `σ(t^{⊗q}) = σ(t)^q`;
* `exists_dualFrame_tautologicalSection_res` (module `…MonomialFrameTautological`): `ξ|_{p⁻¹V} = σ(ε^∨) · p^*ε`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-- **In frame trivializations, the monomial `c·ξ^q` restricts to the fiber as `c(y) · ξ^q`.**

Setting: `L`, `M` line bundles on the smooth projective curve `C` over `k`, `p : Tot(L) → C`, `y ∈ C` *any*
point, `κ := κ(y)`, `F := p.fiber y`, `i := p.fiberι y`, `π_F := p.fiberToSpecResidueField y`,
`g := C.fromSpecResidueField y`, `i ≫ p = π_F ≫ g` (`Scheme.Hom.fiber_fac`),
`const := fiberResidueConstants p y : κ → Γ(F, O_F)`.
Claim: there are trivializations `τ_L : i^*(p^*L) ≅ O_F` and `τ_M : i^*(p^*M) ≅ O_F` such that for every `q`
and every `c ∈ Γ(C, M ⊗ L^{-q})` there is `a ∈ κ` with
`τ_M(i^*(xiMonomial L M q c)) = const a · τ_L(i^*ξ)^q` (`ξ = tautologicalSection L`; sections of `O_F` are
read as functions through `unitSectionAsFunction`, definitionally the identity). (In fact `a = c(y)`,
the value of `c` at `y` in the frames; the user does not need this.)

Proof (as formalized below):
1. Frames. An open `V ∋ y` with frames `ε` of `L` and `η` of `M` on `V` (`exists_frame`, `exists_frame_le`,
   `IsFrame.restrict`); the dual frame `t` of `L^∨` with `ξ|_{p⁻¹V} = x • p^*ε`, `x := frameCoordinate L V t = σ(t)`
   (`exists_dualFrame_tautologicalSection_res`). `F → C` lands in `V` (`fiber_fac`,
   `fromSpecResidueField_apply`), so `⊤ ≤ i⁻¹(p⁻¹V)`.
2. Trivializations. `p^*ε`, `p^*η` are frames of `p^*L`, `p^*M` on `W := p⁻¹V` (`isFrame_unitSec_pullback`); their
   pullbacks `e_F`, `e'_F` to `F` (`pullbackTopSection`) are global frames (`isFrame_pullbackTopSection`);
   `τ_L := (topTrivialization e_F)⁻¹`, `τ_M := (topTrivialization e'_F)⁻¹`, which read off the coordinate:
   `τ(r • e) = r` (`IsFrame.topTrivialization_inv_app_smul`).
3. The monomial on `W`. With `c' := (coefficientModuleIso q)⁻¹ c` and the frame `η ⊗ t^{⊗q}` of `M ⊗ (L^∨)^{⊗q}`
   on `V` (`IsFrame.coefficientLineModule`), `c'|_V = r • (η ⊗ t^{⊗q})` for `r := coord(c'|_V) ∈ Γ(V, O)`.
   `xiMonomial q c |_W = ρ(θ((M ◁ u_q)(τ_⊗(c'|_V))))` (`xiMonomial_res`, `monomialHom_eq`), and on the pure tensor
   `r • (η ⊗ t^{⊗q}) = (r • η) ⊗ t^{⊗q}` this is `u_q(t^{⊗q}) • p^*(r • η)`
   (`rightUnitor_projectionFormulaHom_whiskerLeft_tensorSections`) `= (x^q * p^♯r) • p^*η`
   (`monomialUnit_app_moduleTensorPowerSection`, `unitSec_smul`).
4. Restriction to the fiber. `i^*s = pullbackTopSection(s|_W)` (`pullbackTopSection_res_top`) and
   `pullbackTopSection(f • e) = i^♯f • pullbackTopSection(e)` (`pullbackTopSection_smul`), so
   `τ_M(i^*(xiMonomial q c)) = i^♯(x^q * p^♯r) = (i^♯x)^q * (i ≫ p)^♯r` and `τ_L(i^*ξ) = i^♯x`; finally
   `(i ≫ p)^♯r = const(a)` with `a := ΓSpecIso(g^♯r) ∈ κ` (`appLE_comp_fiber_eq_fiberResidueConstants`). ∎
Edge cases: `q = 0` (`x^0 = 1`, `a = c(y)`); `c = 0` (`r = 0`, `a = 0`); `y` non-closed (fine, `κ(y)` arbitrary).
Nothing here uses `IsAlgClosed k`. -/
theorem totalSpace_fiber_exists_trivializations_xiMonomial {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (y : C.toScheme) :
    ∃ (τL : (AlgebraicGeometry.Scheme.Modules.pullback
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y)).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback
              (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj L.toModules) ≅
          SheafOfModules.unit ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y).ringCatSheaf)
      (τM : (AlgebraicGeometry.Scheme.Modules.pullback
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y)).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback
              (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules) ≅
          SheafOfModules.unit ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y).ringCatSheaf),
      ∀ (q : ℕ) (c : ((((M.zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)),
        ∃ a : (C.toScheme.residueField y : Type u),
          AlgebraicGeometry.Scheme.Modules.unitSectionAsFunction (τM.hom.app ⊤ (sectionPullbackAlong
              ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y) (xiMonomial L M q c))) =
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberResidueConstants y a *
              (AlgebraicGeometry.Scheme.Modules.unitSectionAsFunction (τL.hom.app ⊤ (sectionPullbackAlong
                ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y) (tautologicalSection L)))) ^ q := by
  -- notation
  set p := (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom with hp
  set i := p.fiberι y with hi
  set g := C.toScheme.fromSpecResidueField y with hg
  set πF := p.fiberToSpecResidueField y with hπF
  -- 1. frames near `y`
  obtain ⟨V₁, hyV₁, ε₁, hε₁⟩ := AlgebraicGeometry.Scheme.Modules.exists_frame L.toModules y
  obtain ⟨V, hVV₁, hyV, η, hη⟩ := AlgebraicGeometry.Scheme.Modules.exists_frame_le M.toModules hyV₁
  set ε : Γ(L.toModules, V) := L.toModules.res hVV₁ ε₁ with hεdef
  have hε : AlgebraicGeometry.Scheme.Modules.IsFrame L.toModules V ε := hε₁.restrict hVV₁
  obtain ⟨t, ht, hξ⟩ := exists_dualFrame_tautologicalSection_res L V hε
  set x := AlgebraicGeometry.Scheme.totalSpace.frameCoordinate L.toModules V t with hx
  -- the fiber lands in `V`
  have hgV : ⊤ ≤ g ⁻¹ᵁ V :=
    AlgebraicGeometry.Scheme.Modules.top_le_preimage_fromSpecResidueField y hyV
  have hipV : ⊤ ≤ (i ≫ p) ⁻¹ᵁ V := by
    have hgV' := SetLike.le_def.mp hgV
    rw [hi, hp, AlgebraicGeometry.Scheme.Hom.fiber_fac]
    intro z _
    exact hgV' (show πF.base z ∈ (⊤ : (AlgebraicGeometry.Spec (C.toScheme.residueField y)).Opens) from trivial)
  have hiW : ⊤ ≤ i ⁻¹ᵁ (p ⁻¹ᵁ V) := hipV
  -- 2. frames on `W = p⁻¹V` and on the fiber; trivializations
  let PL := (AlgebraicGeometry.Scheme.Modules.pullback p).obj L.toModules
  let PM := (AlgebraicGeometry.Scheme.Modules.pullback p).obj M.toModules
  let eW : Γ(PL, p ⁻¹ᵁ V) := ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction p).unit.app L.toModules).app V ε
  let eW' : Γ(PM, p ⁻¹ᵁ V) := ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M.toModules).app V η
  have heW : AlgebraicGeometry.Scheme.Modules.IsFrame PL (p ⁻¹ᵁ V) eW :=
    MiyaokaMori.DualPullback.isFrame_unitSec_pullback p L.toModules hε
  have heW' : AlgebraicGeometry.Scheme.Modules.IsFrame PM (p ⁻¹ᵁ V) eW' :=
    MiyaokaMori.DualPullback.isFrame_unitSec_pullback p M.toModules hη
  have heF := AlgebraicGeometry.Scheme.Modules.isFrame_pullbackTopSection i PL hiW heW
  have heF' := AlgebraicGeometry.Scheme.Modules.isFrame_pullbackTopSection i PM hiW heW'
  refine ⟨heF.topTrivialization.symm, heF'.topTrivialization.symm, fun q c => ?_⟩
  -- 3. the coefficient in the frame `η ⊗ t^{⊗q}`
  let c' : Γ(AlgebraicGeometry.Scheme.Modules.coefficientLineModule M.toModules L.toModules q, ⊤) := (L.coefficientModuleIso M q).inv.app ⊤ c
  have hfr : AlgebraicGeometry.Scheme.Modules.IsFrame (AlgebraicGeometry.Scheme.Modules.coefficientLineModule M.toModules L.toModules q) V
      (AlgebraicGeometry.Scheme.Modules.moduleTensorSection η (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t q)) :=
    AlgebraicGeometry.Scheme.Modules.IsFrame.coefficientLineModule hη ht q
  set r : Γ(C.toScheme, V) := hfr.coord le_rfl ((AlgebraicGeometry.Scheme.Modules.coefficientLineModule M.toModules L.toModules q).res le_top c')
    with hr
  have hc' : (AlgebraicGeometry.Scheme.Modules.coefficientLineModule M.toModules L.toModules q).res (le_top : V ≤ ⊤) c' =
      r • AlgebraicGeometry.Scheme.Modules.moduleTensorSection η (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t q) := by
    have h1 := hfr.coord_smul_frame le_rfl ((AlgebraicGeometry.Scheme.Modules.coefficientLineModule M.toModules L.toModules q).res le_top c')
    have h0 : (AlgebraicGeometry.Scheme.Modules.coefficientLineModule M.toModules L.toModules q).res le_rfl
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection η (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t q)) =
        AlgebraicGeometry.Scheme.Modules.moduleTensorSection η (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t q) :=
      AlgebraicGeometry.Scheme.Modules.res_self _ _
    exact h1.symm.trans (congrArg (fun z => r • z) h0)
  -- the monomial on `W`
  let u := AlgebraicGeometry.Scheme.totalSpace.monomialUnit L.toModules q
  let τ := AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t q
  have hmono : PM.res (le_top : p ⁻¹ᵁ V ≤ ⊤) (xiMonomial L M q c) = (x ^ q * p.app V r) • eW' := by
    rw [xiMonomial_res L M q c V]
    have e1 : (AlgebraicGeometry.Scheme.totalSpace.monomialHom L.toModules M.toModules q).app V
        ((AlgebraicGeometry.Scheme.Modules.coefficientLineModule M.toModules L.toModules q).res (le_top : V ≤ ⊤) c') =
        (M.toModules ◁ u).app V (AlgebraicGeometry.Scheme.Modules.tensorSections M.toModules
          (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q) V (r • η) τ) := by
      let μ := AlgebraicGeometry.Scheme.totalSpace.monomialHom L.toModules M.toModules q
      let s₀ : Γ(AlgebraicGeometry.Scheme.Modules.coefficientLineModule M.toModules L.toModules q, V) := AlgebraicGeometry.Scheme.Modules.moduleTensorSection η τ
      have s1 : μ.app V ((AlgebraicGeometry.Scheme.Modules.coefficientLineModule M.toModules L.toModules q).res (le_top : V ≤ ⊤) c') =
          μ.app V (r • s₀) := congrArg (μ.app V) hc'
      have s2 : μ.app V (r • s₀) = r • μ.app V s₀ := AlgebraicGeometry.Scheme.Modules.Hom.app_smul μ r s₀
      have e11 : μ.app V s₀ = (M.toModules ◁ u).app V (AlgebraicGeometry.Scheme.Modules.tensorSections M.toModules
          (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q) V η τ) := rfl
      let w : Γ(M.toModules ⊗ AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q, V) :=
        AlgebraicGeometry.Scheme.Modules.tensorSections M.toModules
          (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q) V η τ
      have s3 : r • (M.toModules ◁ u).app V w = (M.toModules ◁ u).app V (r • w) :=
        (AlgebraicGeometry.Scheme.Modules.Hom.app_smul (M.toModules ◁ u) r w).symm
      have s4 : AlgebraicGeometry.Scheme.Modules.tensorSections M.toModules
          (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q) V (r • η) τ =
          r • w :=
        AlgebraicGeometry.Scheme.Modules.tensorSections_smul_left M.toModules _ V r η τ w rfl
      exact s1.trans (s2.trans ((congrArg (fun z => r • z) e11).trans
        (s3.trans (congrArg ((M.toModules ◁ u).app V) s4.symm))))
    have e2 := AlgebraicGeometry.Scheme.Modules.rightUnitor_projectionFormulaHom_whiskerLeft_tensorSections p
      M.toModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q) u V (r • η) τ
    have : (AlgebraicGeometry.Scheme.Modules.dual L.toModules).IsLineBundle :=
      AlgebraicGeometry.Scheme.Modules.moduleSheafDual_isLineBundle L.toModules
    have e3 := AlgebraicGeometry.Scheme.totalSpace.monomialUnit_app_moduleTensorPowerSection L.toModules V t q
    have e4 := MiyaokaMori.DualPullback.unitSec_smul p M.toModules r η
    refine (congrArg (fun z => (ρ_ PM).hom.app (p ⁻¹ᵁ V)
      (show Γ(PM ⊗ SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf, p ⁻¹ᵁ V) from
        (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom p M.toModules
          (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).app V z)) e1).trans ?_
    refine e2.trans ?_
    change (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left, p ⁻¹ᵁ V) from u.app V τ) •
      MiyaokaMori.DualPullback.unitSec p M.toModules (r • η) = _
    rw [e3, e4, smul_smul]
    rfl
  -- 4. restriction to the fiber
  refine ⟨(AlgebraicGeometry.Scheme.ΓSpecIso (C.toScheme.residueField y)).hom (g.appLE V ⊤ hgV r), ?_⟩
  have hM : sectionPullbackAlong i (xiMonomial L M q c) =
      i.appLE (p ⁻¹ᵁ V) ⊤ hiW (x ^ q * p.app V r) • AlgebraicGeometry.Scheme.Modules.pullbackTopSection i PM hiW eW' := by
    have s1 := AlgebraicGeometry.Scheme.Modules.pullbackTopSection_res_top i PM hiW (xiMonomial L M q c)
    have s2 := congrArg (AlgebraicGeometry.Scheme.Modules.pullbackTopSection i PM hiW) hmono
    have s3 := AlgebraicGeometry.Scheme.Modules.pullbackTopSection_smul i PM hiW (x ^ q * p.app V r) eW'
    exact s1.symm.trans (s2.trans s3)
  have hL : sectionPullbackAlong i (tautologicalSection L) =
      i.appLE (p ⁻¹ᵁ V) ⊤ hiW x • AlgebraicGeometry.Scheme.Modules.pullbackTopSection i PL hiW eW := by
    have s1 := AlgebraicGeometry.Scheme.Modules.pullbackTopSection_res_top i PL hiW (tautologicalSection L)
    have s2 := congrArg (AlgebraicGeometry.Scheme.Modules.pullbackTopSection i PL hiW) hξ
    have s3 := AlgebraicGeometry.Scheme.Modules.pullbackTopSection_smul i PL hiW x eW
    exact s1.symm.trans (s2.trans s3)
  have hτM : AlgebraicGeometry.Scheme.Modules.unitSectionAsFunction
      (AlgebraicGeometry.Scheme.Modules.Hom.app heF'.topTrivialization.symm.hom ⊤
        (sectionPullbackAlong i (xiMonomial L M q c))) = i.appLE (p ⁻¹ᵁ V) ⊤ hiW (x ^ q * p.app V r) := by
    rw [hM]
    exact heF'.topTrivialization_inv_app_smul _
  have hτL : AlgebraicGeometry.Scheme.Modules.unitSectionAsFunction
      (AlgebraicGeometry.Scheme.Modules.Hom.app heF.topTrivialization.symm.hom ⊤
        (sectionPullbackAlong i (tautologicalSection L))) = i.appLE (p ⁻¹ᵁ V) ⊤ hiW x := by
    rw [hL]
    exact heF.topTrivialization_inv_app_smul _
  have hconst : i.appLE (p ⁻¹ᵁ V) ⊤ hiW (p.app V r) =
      p.fiberResidueConstants y ((AlgebraicGeometry.Scheme.ΓSpecIso (C.toScheme.residueField y)).hom
        (g.appLE V ⊤ hgV r)) := by
    rw [← AlgebraicGeometry.Scheme.Modules.appLE_comp_fiber_eq_fiberResidueConstants p y hipV hgV r]
    exact (congrArg (fun φ => φ.hom r) (AlgebraicGeometry.Scheme.Hom.comp_appLE i p V ⊤ hipV)).symm
  change AlgebraicGeometry.Scheme.Modules.unitSectionAsFunction
      (AlgebraicGeometry.Scheme.Modules.Hom.app heF'.topTrivialization.symm.hom ⊤
        (sectionPullbackAlong i (xiMonomial L M q c))) =
    p.fiberResidueConstants y ((AlgebraicGeometry.Scheme.ΓSpecIso (C.toScheme.residueField y)).hom
        (g.appLE V ⊤ hgV r)) *
      (AlgebraicGeometry.Scheme.Modules.unitSectionAsFunction
        (AlgebraicGeometry.Scheme.Modules.Hom.app heF.topTrivialization.symm.hom ⊤
          (sectionPullbackAlong i (tautologicalSection L)))) ^ q
  rw [hτM, hτL, map_mul, map_pow, hconst, mul_comm]

end
