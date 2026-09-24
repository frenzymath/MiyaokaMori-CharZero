import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.LocalJetGluing
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.FrameJetCoefficientMap
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization_Frames
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.TruncatedJetAlgebraSectionsGermExt
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.LocalJetOfConstantIsSeedJet
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.FramedLocalJetGenericPoint

/-! # Independence of the local jet from the chart and the frame
(step 2 of the proof of Lemma 3.1 of the paper)

> Replacing `ε` by `uε` replaces `γ` by `u^{-1}γ`, multiplies `a_{α,i,q}` by `u^q`, and changes the fibre
> coordinate from `t` to `u^{-1}t`. Thus the expressions … agree under changes of both the jet chart and
> the frame of `L`.

Two local jets `g_{Ψ₁} : p_L⁻¹(U₁) → 𝒵`, `g_{Ψ₂} : p_L⁻¹(U₂) → 𝒵` built over charts `V₁`, `V₂` and frames
`μ₁`, `μ₂` agree on `p_L⁻¹(W)` for every affine `W ≤ U₁ ⊓ U₂` containing `η_{C̃}`, provided their pieces
have the prescribed generic values (`localJet_eq_of_generic`): on the integral `C̃` a section of the
line bundle `L^{-n}` over `W` is determined by its germ at `η`, so `Ψ₁`, `Ψ₂` are determined by their
generic values, which are the coordinates of the single affine jet `ĵ` rescaled by `γ` — independent of
the chart (the chart enters only through the *presentation* of the same value) — and the frame enters
only through the generic germs `γ_i^{-n} μ_i^{⊗n}(η)`, which are frame-independent
(`frameChange_zpow_smul_germ_framePow`, the paper's `u`-computation).

-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace truncatedJetAlgebra

open AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k} (L' : LineBundle Ct.toVariety)

/-- `framePow` commutes with restriction: `(μ^{⊗n})|_W = (μ|_W)^{⊗n}` (`tensorSections_restrict`). -/
theorem res_framePow {U W : Ct.toScheme.Opens} (h : W ≤ U) (μ : Γ((L'.zpow (-1)).toModules, U)) :
    ∀ n : ℕ, (truncatedJetAlgebra.piece L' n).res h (framePow L' U μ n) =
      framePow L' W ((L'.zpow (-1)).toModules.res h μ) n
  | 0 => map_one (Ct.toScheme.presheaf.map (homOfLE h).op).hom
  | n + 1 => by
    show ((CategoryTheory.MonoidalCategoryStruct.tensorObj (C := Ct.toScheme.Modules)
        (truncatedJetAlgebra.piece L' n) (L'.zpow (-1)).toModules).val.map (homOfLE h).op)
        (tensorSections (truncatedJetAlgebra.piece L' n) (L'.zpow (-1)).toModules U (framePow L' U μ n) μ) =
      tensorSections (truncatedJetAlgebra.piece L' n) (L'.zpow (-1)).toModules W
        (framePow L' W ((L'.zpow (-1)).toModules.res h μ) n) ((L'.zpow (-1)).toModules.res h μ)
    rw [tensorSections_restrict (truncatedJetAlgebra.piece L' n) (L'.zpow (-1)).toModules (homOfLE h)
      (framePow L' U μ n) μ]
    exact congrArg (fun z => tensorSections (truncatedJetAlgebra.piece L' n) (L'.zpow (-1)).toModules W z
      ((L'.zpow (-1)).toModules.res h μ)) (res_framePow h μ n)

/-- `framePow` of a rescaled section: `(r • μ)^{⊗n} = r^n • μ^{⊗n}` (`tensorSections` is bilinear). -/
theorem framePow_smul_section (W : Ct.toScheme.Opens) (r : Γ(Ct.toScheme, W))
    (μ : Γ((L'.zpow (-1)).toModules, W)) :
    ∀ n : ℕ, framePow L' W (r • μ) n = r ^ n • framePow L' W μ n
  | 0 => by rw [pow_zero, one_smul]; rfl
  | n + 1 => by
    have key : ∀ z : Γ(truncatedJetAlgebra.piece L' n ⊗ (L'.zpow (-1)).toModules, W),
        z = tensorSections (truncatedJetAlgebra.piece L' n) (L'.zpow (-1)).toModules W (framePow L' W μ n) μ →
        tensorSections (truncatedJetAlgebra.piece L' n) (L'.zpow (-1)).toModules W (framePow L' W (r • μ) n) (r • μ) =
          r ^ (n + 1) • z := by
      intro z hz
      rw [framePow_smul_section W r μ n,
        tensorSections_smul_left (truncatedJetAlgebra.piece L' n) (L'.zpow (-1)).toModules W (r ^ n)
          (framePow L' W μ n) (r • μ) _ rfl,
        tensorSections_smul_right (truncatedJetAlgebra.piece L' n) (L'.zpow (-1)).toModules W r
          (framePow L' W μ n) μ z hz, smul_smul, pow_succ]
    exact key _ rfl

end truncatedJetAlgebra

namespace jetNeighborhood

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
  (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (ρ : FiniteCover k C)
  (L : LineBundle ρ.source.toVariety)

set_option linter.unusedVariables false in
/-- **Frame change at the generic point** (Lemma 3.1 of the paper;
in stalk form). Let `e, e'` be frames of `L` on the opens `U, U' ∋ η := η_{C̃}`, `δ, δ'` their dual frames
(`⟨δ, e⟩ = 1`, `⟨δ', e'⟩ = 1`), `μ := zpowNegOneIso⁻¹ δ`, `μ' := zpowNegOneIso⁻¹ δ'` the corresponding
frames of `L^{-1}`, and `s ∈ L_η` a stalk element with `s = γ • e_η = γ' • e'_η`. Then for every `n`,
`γ'^{-n} • (μ'^{⊗n})_η = γ^{-n} • (μ^{⊗n})_η` in the stalk of `L^{-n}` at `η`
(`truncatedJetAlgebra.framePow`).

Proof. On `W := U ⊓ U' ∋ η`, `e'|_W = u • e|_W` with `u ∈ 𝒪(W)ˣ` (`IsFrame.isUnit_coord`, both are
frames), so at `η`: `e'_η = u_η e_η`, hence `γ e_η = γ' u_η e_η` and `γ = γ' u_η` (`e_η ≠ 0` generates the
stalk `L_η`, a free module of rank one). Pairing: `1 = ⟨δ', e'⟩ = u ⟨δ', e⟩`, and since `δ|_W` is a frame
of `L^∨` (`IsFrame.dual_of_pairing_eq_one`) with `⟨δ, e⟩ = 1`, the coordinate of `δ'|_W` in `δ|_W` is
`⟨δ', e⟩ = u^{-1}`, i.e. `δ'|_W = u^{-1} • δ|_W`, so `μ'|_W = u^{-1} • μ|_W` (`zpowNegOneIso` is `𝒪`-linear)
and `μ'^{⊗n}|_W = u^{-n} • μ^{⊗n}|_W` (`framePow_succ`, `tensorSections` is bilinear). Taking germs
(`germ_res_apply`, `germ_smul'`): `γ'^{-n} (μ'^{⊗n})_η = γ'^{-n} u_η^{-n} (μ^{⊗n})_η = (γ' u_η)^{-n} (μ^{⊗n})_η
= γ^{-n} (μ^{⊗n})_η`. If `γ = 0` then `s = 0`, so `γ' = 0` as well (`e'_η ≠ 0`), and both sides are `0`
for `n ≥ 1` and `(1)_η` for `n = 0` (`zpow_neg`, `zero_zpow`). ∎
The hypothesis `he'`
(that `e'` is a frame) is not needed by the proof (only `⟨δ', e'⟩ = 1` is used); it is kept because the
parent `LocalDatum.compat` supplies it. -/
theorem frameChange_zpow_smul_germ_framePow
    {U U' : ρ.source.toScheme.Opens} (hηU : genericPoint ρ.source.toScheme ∈ U)
    (hηU' : genericPoint ρ.source.toScheme ∈ U')
    (e : Γ(L.toModules, U)) (he : AlgebraicGeometry.Scheme.Modules.IsFrame L.toModules U e)
    (e' : Γ(L.toModules, U')) (he' : AlgebraicGeometry.Scheme.Modules.IsFrame L.toModules U' e')
    (δ : Γ(AlgebraicGeometry.Scheme.Modules.dual L.toModules, U))
    (hδ : (AlgebraicGeometry.Scheme.Modules.dualEv L.toModules).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
        L.toModules U δ e) = (1 : Γ(ρ.source.toScheme, U)))
    (δ' : Γ(AlgebraicGeometry.Scheme.Modules.dual L.toModules, U'))
    (hδ' : (AlgebraicGeometry.Scheme.Modules.dualEv L.toModules).app U'
      (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
        L.toModules U' δ' e') = (1 : Γ(ρ.source.toScheme, U')))
    (s : L.toModules.stalk (genericPoint ρ.source.toScheme)) (γ γ' : ρ.source.toScheme.functionField)
    (hγ : s = γ • (L.toModules.presheaf.germ U (genericPoint ρ.source.toScheme) hηU e :
      L.toModules.stalk (genericPoint ρ.source.toScheme)))
    (hγ' : s = γ' • (L.toModules.presheaf.germ U' (genericPoint ρ.source.toScheme) hηU' e' :
      L.toModules.stalk (genericPoint ρ.source.toScheme)))
    (n : ℕ) :
    γ' ^ (-(n : ℤ)) • ((truncatedJetAlgebra.piece L n).presheaf.germ U' (genericPoint ρ.source.toScheme) hηU'
        (truncatedJetAlgebra.framePow L U' (L.zpowNegOneIso.inv.app U' δ') n) :
      (truncatedJetAlgebra.piece L n).stalk (genericPoint ρ.source.toScheme)) =
    γ ^ (-(n : ℤ)) • ((truncatedJetAlgebra.piece L n).presheaf.germ U (genericPoint ρ.source.toScheme) hηU
        (truncatedJetAlgebra.framePow L U (L.zpowNegOneIso.inv.app U δ) n) :
      (truncatedJetAlgebra.piece L n).stalk (genericPoint ρ.source.toScheme)) := by
  haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  set W : ρ.source.toScheme.Opens := U ⊓ U' with hWdef
  have hηW : genericPoint ρ.source.toScheme ∈ W := ⟨hηU, hηU'⟩
  have hWU : W ≤ U := inf_le_left
  have hWU' : W ≤ U' := inf_le_right
  -- restricted frames of `L` and of `L^∨`
  have heW : AlgebraicGeometry.Scheme.Modules.IsFrame L.toModules W (L.toModules.res hWU e) := he.restrict hWU
  have hδfr : AlgebraicGeometry.Scheme.Modules.IsFrame (AlgebraicGeometry.Scheme.Modules.dual L.toModules) U δ :=
    AlgebraicGeometry.Scheme.Modules.IsFrame.dual_of_pairing_eq_one hδ
  have hδW := hδfr.restrict hWU
  -- `e'|_W = u • e|_W`, `δ'|_W = v • δ|_W`
  set u := heW.coord le_rfl (L.toModules.res hWU' e') with hu_def
  have hu : u • L.toModules.res hWU e = L.toModules.res hWU' e' := by
    have h := heW.coord_smul_frame le_rfl (L.toModules.res hWU' e')
    rwa [AlgebraicGeometry.Scheme.Modules.res_self] at h
  set v := hδW.coord le_rfl ((AlgebraicGeometry.Scheme.Modules.dual L.toModules).res hWU' δ') with hv_def
  have hv : v • (AlgebraicGeometry.Scheme.Modules.dual L.toModules).res hWU δ =
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules).res hWU' δ' := by
    have h := hδW.coord_smul_frame le_rfl ((AlgebraicGeometry.Scheme.Modules.dual L.toModules).res hWU' δ')
    rwa [AlgebraicGeometry.Scheme.Modules.res_self] at h
  -- the pairings restricted to `W`
  have hpair : ∀ (V : ρ.source.toScheme.Opens) (hV : W ≤ V) (d : Γ(AlgebraicGeometry.Scheme.Modules.dual L.toModules, V))
      (x : Γ(L.toModules, V)),
      (AlgebraicGeometry.Scheme.Modules.dualEv L.toModules).app V
        (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
          L.toModules V d x) = (1 : Γ(ρ.source.toScheme, V)) →
      (AlgebraicGeometry.Scheme.Modules.dualEv L.toModules).app W
        (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
          L.toModules W ((AlgebraicGeometry.Scheme.Modules.dual L.toModules).res hV d) (L.toModules.res hV x)) =
        (1 : Γ(ρ.source.toScheme, W)) := by
    intro V hV d x h
    have h2 := (AlgebraicGeometry.Scheme.Modules.Hom.app_res (AlgebraicGeometry.Scheme.Modules.dualEv L.toModules) hV
      (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
        L.toModules V d x)).trans (by rw [h])
    have h3 : (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := ρ.source.toScheme.Modules)
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules) L.toModules).res hV
        (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
          L.toModules V d x) =
        AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
          L.toModules W ((AlgebraicGeometry.Scheme.Modules.dual L.toModules).res hV d) (L.toModules.res hV x) :=
      AlgebraicGeometry.Scheme.Modules.tensorSections_restrict (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
        L.toModules (homOfLE hV) d x
    rw [h3] at h2
    exact h2.trans (map_one (ρ.source.toScheme.presheaf.map (homOfLE hV).op).hom)
  have h1 := hpair U hWU δ e hδ
  have h1' := hpair U' hWU' δ' e' hδ'
  -- `u * v = 1`
  have huv : u * v = 1 := by
    rw [← hu, ← hv, AlgebraicGeometry.Scheme.Modules.tensorSections_smul_left
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules) L.toModules W v _ _ _ rfl,
      AlgebraicGeometry.Scheme.Modules.tensorSections_smul_right
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules) L.toModules W u _ _ _ rfl] at h1'
    set T : Γ(AlgebraicGeometry.Scheme.Modules.dual L.toModules ⊗ L.toModules, W) :=
      AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
        L.toModules W ((AlgebraicGeometry.Scheme.Modules.dual L.toModules).res hWU δ) (L.toModules.res hWU e)
      with hT
    have h4 := AlgebraicGeometry.Scheme.Modules.Hom.app_smul (AlgebraicGeometry.Scheme.Modules.dualEv L.toModules) v (u • T)
    have h5 := AlgebraicGeometry.Scheme.Modules.Hom.app_smul (AlgebraicGeometry.Scheme.Modules.dualEv L.toModules) u T
    rw [h5] at h4
    rw [h4, h1] at h1'
    have h8 : v * (u * (1 : Γ(ρ.source.toVariety.carrier, W))) = 1 := h1'
    rw [mul_one, mul_comm] at h8
    exact h8
  -- `μ'|_W = v • μ|_W`
  have hμ : (L.zpow (-1)).toModules.res hWU' (L.zpowNegOneIso.inv.app U' δ') =
      v • (L.zpow (-1)).toModules.res hWU (L.zpowNegOneIso.inv.app U δ) := by
    rw [← AlgebraicGeometry.Scheme.Modules.Hom.app_res, ← AlgebraicGeometry.Scheme.Modules.Hom.app_res, ← hv,
      AlgebraicGeometry.Scheme.Modules.Hom.app_smul]
  -- germs of the scalars
  set uη : ρ.source.toScheme.functionField :=
    ρ.source.toScheme.presheaf.germ W (genericPoint ρ.source.toScheme) hηW u with huη
  set vη : ρ.source.toScheme.functionField :=
    ρ.source.toScheme.presheaf.germ W (genericPoint ρ.source.toScheme) hηW v with hvη
  have huvη : uη * vη = 1 := by
    rw [huη, hvη, ← map_mul, huv, map_one]
  -- `γ = γ' * uη` (the germ of `e` is a basis of the stalk)
  have hγγ' : γ = γ' * uη := by
    have hu' : L.toModules.presheaf.map (homOfLE hWU').op e' = u • L.toModules.presheaf.map (homOfLE hWU).op e :=
      hu.symm
    have hgerm : (L.toModules.presheaf.germ U' (genericPoint ρ.source.toScheme) hηU' e' :
        L.toModules.stalk (genericPoint ρ.source.toScheme)) =
        uη • (L.toModules.presheaf.germ U (genericPoint ρ.source.toScheme) hηU e :
          L.toModules.stalk (genericPoint ρ.source.toScheme)) := by
      rw [← TopCat.Presheaf.germ_res_apply L.toModules.presheaf (homOfLE hWU') (genericPoint ρ.source.toScheme) hηW e',
        hu', AlgebraicGeometry.Scheme.Modules.germ_smul', TopCat.Presheaf.germ_res_apply]
    have h0 : (γ - γ' * uη) • (L.toModules.presheaf.germ U (genericPoint ρ.source.toScheme) hηU e :
        L.toModules.stalk (genericPoint ρ.source.toScheme)) = 0 := by
      rw [sub_smul, mul_smul, ← hgerm, ← hγ, ← hγ']
      exact sub_self s
    exact sub_eq_zero.mp (he.germ_smul_eq_zero hηU _ h0)
  -- the germ of `μ'^{⊗n}` in terms of the germ of `μ^{⊗n}`
  have hgermPow : ((truncatedJetAlgebra.piece L n).presheaf.germ U' (genericPoint ρ.source.toScheme) hηU'
      (truncatedJetAlgebra.framePow L U' (L.zpowNegOneIso.inv.app U' δ') n) :
        (truncatedJetAlgebra.piece L n).stalk (genericPoint ρ.source.toScheme)) =
      vη ^ n • ((truncatedJetAlgebra.piece L n).presheaf.germ U (genericPoint ρ.source.toScheme) hηU
        (truncatedJetAlgebra.framePow L U (L.zpowNegOneIso.inv.app U δ) n) :
        (truncatedJetAlgebra.piece L n).stalk (genericPoint ρ.source.toScheme)) := by
    rw [← TopCat.Presheaf.germ_res_apply (truncatedJetAlgebra.piece L n).presheaf (homOfLE hWU')
        (genericPoint ρ.source.toScheme) hηW,
      ← TopCat.Presheaf.germ_res_apply (truncatedJetAlgebra.piece L n).presheaf (homOfLE hWU)
        (genericPoint ρ.source.toScheme) hηW]
    show (truncatedJetAlgebra.piece L n).presheaf.germ W (genericPoint ρ.source.toScheme) hηW
        ((truncatedJetAlgebra.piece L n).res hWU' (truncatedJetAlgebra.framePow L U' (L.zpowNegOneIso.inv.app U' δ') n)) =
      vη ^ n • (truncatedJetAlgebra.piece L n).presheaf.germ W (genericPoint ρ.source.toScheme) hηW
        ((truncatedJetAlgebra.piece L n).res hWU (truncatedJetAlgebra.framePow L U (L.zpowNegOneIso.inv.app U δ) n))
    rw [truncatedJetAlgebra.res_framePow, truncatedJetAlgebra.res_framePow, hμ,
      truncatedJetAlgebra.framePow_smul_section, AlgebraicGeometry.Scheme.Modules.germ_smul', map_pow]
  rw [hgermPow, smul_smul, hγγ']
  congr 1
  have hvinv : vη = uη⁻¹ := eq_inv_of_mul_eq_one_right huvη
  rw [hvinv, mul_zpow, zpow_neg γ', zpow_neg uη, zpow_natCast, zpow_natCast, inv_pow]

set_option linter.unusedVariables false in
/-- **Independence of the local jet from chart and frame** (Lemma 3.1 of the paper;
§3 of the paper). Data: the affine jet `ĵ` over `η_{C̃} ≫ ρ` (`hĵ`); two affine opens
`V₁, V₂` of `C` over which `ĵ` lies (`hĵV₁`, `hĵV₂`); two affine opens `U₁, U₂ ∋ η_{C̃}` of `C̃` with
`Uᵢ ≤ ρ⁻¹Vᵢ`; frames `μᵢ` of `L^{-1}` on `Uᵢ` and scalars `γᵢ ∈ K(C̃)` whose generic germs agree,
`γ₁^{-n} • (μ₁^{⊗n})_η = γ₂^{-n} • (μ₂^{⊗n})_η` (`hframe`; provided by `frameChange_zpow_smul_germ_framePow`);
ring maps `Ψᵢ : B_{Vᵢ} → 𝒜(Uᵢ)` compatible with the structure maps (`hover`), with constant term `s^♯`
(`hzero`) and whose positive-weight pieces have the generic values of the rescaled affine jet:
`(π_{q+1}(Ψᵢ c))_η = (γᵢ^{-(q+1)} · (d_q c)(ĵ)) • (μᵢ^{⊗(q+1)})_η` (`hgen`; `affineJetCoeff`). Then on every
affine open `W ≤ U₁ ⊓ U₂` containing `η_{C̃}`, the two local jets agree:
`homOfLE ≫ localJet Ψ₁ = homOfLE ≫ localJet Ψ₂` as morphisms `p_L⁻¹(W) → 𝒵`.

Natural-language proof. Restrict everything to `W` (`localJet_restrict`: both sides are
`localJet (Ψᵢ ≫ res)`; the hypotheses restrict because germs of restrictions are germs,
`germ_res_apply`, and `π_n`, `framePow` commute with restriction). So assume `U₁ = U₂ = W`.
1. **Both `Ψᵢ` are determined by generic germs.** `𝒜(W) = ⊕_{n ≤ κ} L^{-n}(W)` (`biproduct` sections,
   `AlgebraicGeometry.Scheme.Modules.biproduct_section_eq_sum`), and a section of the line bundle
   `L^{-n}` on the integral `C̃` with zero germ at `η` is zero
   (`lineBundle_section_eq_zero_of_germ_genericPoint_eq_zero` on the integral open subscheme `W`, or
   the stalk-injectivity of a frame: `π_n(Ψ c) = r • μ^{⊗n}` with `r ∈ 𝒪(W)` by `IsFrame.coord`, and
   `𝒪(W) → K(C̃)` is injective, `germToFunctionField_injective`). Hence `π₀(Ψᵢ c) = ρ^♯ (s^♯ c)` (`hzero`)
   and, for `q : Fin κ`, `π_{q+1}(Ψᵢ c) = aᵢ_{q}(c) • μᵢ^{⊗(q+1)}` with `aᵢ_q(c) ∈ 𝒪(W)` of germ
   `γᵢ^{-(q+1)} (d_q c)(ĵ)`.
2. **The generic based jet.** Let `K := K(C̃)`, `T := Spec K` with `η_T : T → C̃` (`fromSpecResidueField`
   composed with `functionFieldIsoResidueField`), and let `θᵢ : Spec (K[t]/(t^{κ+1})) → Spec 𝒜(W)` be
   `Spec` of the ring map `θᵢ^♯ : 𝒜(W) → K[t]/(t^{κ+1})`, `r • μᵢ^{⊗n} ↦ germ(r) γᵢ^{n} t^n`
   (`quotToSections μᵢ` is bijective, `truncatedJetAlgebra.quotToSections_bijective`; `θᵢ^♯` is the
   composite of its inverse with coefficientwise `germ` and the substitution `t ↦ γᵢ t`). Then
   `θᵢ^♯ (Ψᵢ c) = Σ_n (d_{n-1} c)(ĵ) t^n` — **independent of `i`** by `hgen`, `hzero` and step 1 — and this
   is the based affine jet `B_{Vᵢ} → K[t]/(t^{κ+1})` of `ĵ` on `Vᵢ`: the ring map on `B_{Vᵢ}` of
   `Θ := (Spec K[t]/(t^{κ+1}) ≅ jetThickening κ (Spec K)) ≫ (toBasedJet ĵ).1 : Spec K[t]/(t^{κ+1}) → 𝒵`
   (`relativeJetScheme.toBasedJet`, `relativeJetScheme.ofBasedJet_appLE_coeffClass` read through
   `representableBy` for `W := Spec K` over `C`, `hĵ`; `jetThickening.sectionsHom_bijective` identifies
   `Γ(jetThickening κ (Spec K), ⊤)` with `K[t]/(t^{κ+1})`). By `localJet_hom_ext` at level `Vᵢ`
   (both `θᵢ ≫ affineIso⁻¹ ≫ localJet Ψᵢ` and `Θ` land in `π⁻¹Vᵢ` and have the same ring map on `B_{Vᵢ}`,
   `localJet_appLE`, `IsAffineOpen.appLE_SpecMap_fromSpec`): `θᵢ ≫ affineIso.inv ≫ localJet Ψᵢ = Θ` for `i = 1, 2`.
3. **Comparison.** `hframe` says `θ₁^♯ = θ₂^♯` (both send `μ₁^{⊗n}` and `μ₂^{⊗n}` to the same element:
   `γ₁^{-n} μ₁^{⊗n}` and `γ₂^{-n} μ₂^{⊗n}` have the same germ, and `θᵢ^♯ (γᵢ^{-n} μᵢ^{⊗n}) = t^n`), so
   `θ₁ = θ₂ =: θ`, and `θ ≫ affineIso.inv ≫ localJet Ψ₁ = θ ≫ affineIso.inv ≫ localJet Ψ₂`. Both
   `affineIso.inv ≫ localJet Ψᵢ : Spec 𝒜(W) → 𝒵` land in `π⁻¹V₁` (by `hover`, `W ≤ ρ⁻¹V₁`), so they are
   `Spec.map (χᵢ) ≫ fromSpec_{π⁻¹V₁}` for ring maps `χᵢ : B_{V₁} → 𝒜(W)` (`eq_SpecMap_appLE_fromSpec`),
   and the equation reads `Spec.map (χ₁ ≫ θ^♯) ≫ fromSpec = Spec.map (χ₂ ≫ θ^♯) ≫ fromSpec`; `fromSpec` is
   a monomorphism (open immersion) and `Spec` is fully faithful, so `χ₁ ≫ θ^♯ = χ₂ ≫ θ^♯`. If `γ₁ ≠ 0`
   (equivalently `γ₂ ≠ 0`, by `hframe` at `n = 1`), `θ^♯` is injective (`𝒪(W) → K` is, and `t ↦ γt` is
   bijective), so `χ₁ = χ₂` and `localJet Ψ₁ = localJet Ψ₂`. If `γ₁ = 0` then by `hgen` all positive-weight
   pieces of `Ψᵢ c` have zero germ, hence vanish (step 1), so `Ψᵢ = ι₀ ∘ ρ^♯ ∘ s^♯` for both `i` (`hzero`)
   and the two local jets are both `affineIso.hom ≫ Spec.map (sectionsUnit) ≫ fromSpec_W ≫ ρ ≫ s`
   (`localJet_over`-type computation with `Spec.map (s^♯ ∘ ρ^♯)`), hence equal. ∎

Estimated 350–500 lines, hard (the generic based jet of `ĵ` and its ring maps on `B_{V₁}`, `B_{V₂}`;
the injectivity argument). Edge cases: `κ = 0` (`𝒜 = 𝒪`, both local jets are `ρ ≫ s` by `hzero`);
`γᵢ = 0` handled in step 3; `W` must contain `η` (nonempty).

The proof follows the route above with the helper modules `TruncatedJetAlgebraSectionsGermExt`
(sections determined by generic germs), `LocalJetOfConstantIsSeedJet` (the case `γ = 0`), `LocalJetGenericEvaluation`
(`θ^♯` in a frame), `AffineJetGenericPointCoefficients` (the based jet `Θ` of `ĵ` and its coefficients),
`JetNeighborhoodPointOfRingHom` and `FramedLocalJetGenericPoint`
(`θ ≫ g_Ψ = Θ`). The reduction to `W` uses `localJet_restrict` (`LocalJetGluing`). Only `hover₂` is used (the
two local jets are compared at level `V₁`, where `g_{Ψ₂}` lands because it lies over `ρ`); `hover₁` is kept
because the parent `LocalDatum.compat` supplies it. -/
theorem localJet_eq_of_generic
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    (hĵ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
      ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)
    {V₁ V₂ : C.toScheme.Opens} (hV₁ : AlgebraicGeometry.IsAffineOpen V₁) (hV₂ : AlgebraicGeometry.IsAffineOpen V₂)
    (hĵV₁ : (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V₁))
    (hĵV₂ : (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V₂))
    {U₁ U₂ : ρ.source.toScheme.Opens} (hU₁ : AlgebraicGeometry.IsAffineOpen U₁)
    (hU₂ : AlgebraicGeometry.IsAffineOpen U₂)
    (hηU₁ : genericPoint ρ.source.toScheme ∈ U₁) (hηU₂ : genericPoint ρ.source.toScheme ∈ U₂)
    (hUV₁ : U₁ ≤ ρ.hom ⁻¹ᵁ V₁) (hUV₂ : U₂ ≤ ρ.hom ⁻¹ᵁ V₂)
    (μ₁ : Γ((L.zpow (-1)).toModules, U₁)) (hμ₁ : AlgebraicGeometry.Scheme.Modules.IsFrame (L.zpow (-1)).toModules U₁ μ₁)
    (μ₂ : Γ((L.zpow (-1)).toModules, U₂)) (hμ₂ : AlgebraicGeometry.Scheme.Modules.IsFrame (L.zpow (-1)).toModules U₂ μ₂)
    (γ₁ γ₂ : ρ.source.toScheme.functionField)
    (hframe : ∀ n : ℕ,
      γ₁ ^ (-(n : ℤ)) • ((truncatedJetAlgebra.piece L n).presheaf.germ U₁ (genericPoint ρ.source.toScheme) hηU₁
          (truncatedJetAlgebra.framePow L U₁ μ₁ n) : (truncatedJetAlgebra.piece L n).stalk (genericPoint ρ.source.toScheme)) =
      γ₂ ^ (-(n : ℤ)) • ((truncatedJetAlgebra.piece L n).presheaf.germ U₂ (genericPoint ρ.source.toScheme) hηU₂
          (truncatedJetAlgebra.framePow L U₂ μ₂ n) : (truncatedJetAlgebra.piece L n).stalk (genericPoint ρ.source.toScheme)))
    (Ψ₁ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V₁) ⟶
      CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U₁))
    (Ψ₂ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V₂) ⟶
      CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U₂))
    (hover₁ : ∀ r : Γ(C.toScheme, V₁),
      Ψ₁.hom (((MMSetup.cone f).hom.appLE V₁ ((MMSetup.cone f).hom ⁻¹ᵁ V₁) le_rfl).hom r) =
        (truncatedJetAlgebra L κ).sectionsUnit U₁ ((ρ.hom.appLE V₁ U₁ hUV₁).hom r))
    (hover₂ : ∀ r : Γ(C.toScheme, V₂),
      Ψ₂.hom (((MMSetup.cone f).hom.appLE V₂ ((MMSetup.cone f).hom ⁻¹ᵁ V₂) le_rfl).hom r) =
        (truncatedJetAlgebra L κ).sectionsUnit U₂ ((ρ.hom.appLE V₂ U₂ hUV₂).hom r))
    (hzero₁ : ∀ c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V₁),
      (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨0, Nat.succ_pos κ⟩).app U₁ (Ψ₁.hom c) =
        (ρ.hom.appLE V₁ U₁ hUV₁).hom
          (((MMSetup.seed f).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V₁) V₁
            (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V₁)).hom c))
    (hzero₂ : ∀ c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V₂),
      (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨0, Nat.succ_pos κ⟩).app U₂ (Ψ₂.hom c) =
        (ρ.hom.appLE V₂ U₂ hUV₂).hom
          (((MMSetup.seed f).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V₂) V₂
            (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V₂)).hom c))
    (hgen₁ : ∀ (q : Fin κ) (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V₁)),
      ((truncatedJetAlgebra.piece L ((q : ℕ) + 1)).presheaf.germ U₁ (genericPoint ρ.source.toScheme) hηU₁
          ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
            ⟨(q : ℕ) + 1, Nat.succ_lt_succ q.2⟩).app U₁ (Ψ₁.hom c)) :
        (truncatedJetAlgebra.piece L ((q : ℕ) + 1)).stalk (genericPoint ρ.source.toScheme)) =
      (γ₁ ^ (-((q : ℕ) + 1 : ℤ)) * affineJetCoeff f κ ρ ĵ hV₁ hĵV₁ ((q : ℕ) + 1) c) •
        ((truncatedJetAlgebra.piece L ((q : ℕ) + 1)).presheaf.germ U₁ (genericPoint ρ.source.toScheme) hηU₁
          (truncatedJetAlgebra.framePow L U₁ μ₁ ((q : ℕ) + 1)) :
        (truncatedJetAlgebra.piece L ((q : ℕ) + 1)).stalk (genericPoint ρ.source.toScheme)))
    (hgen₂ : ∀ (q : Fin κ) (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V₂)),
      ((truncatedJetAlgebra.piece L ((q : ℕ) + 1)).presheaf.germ U₂ (genericPoint ρ.source.toScheme) hηU₂
          ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
            ⟨(q : ℕ) + 1, Nat.succ_lt_succ q.2⟩).app U₂ (Ψ₂.hom c)) :
        (truncatedJetAlgebra.piece L ((q : ℕ) + 1)).stalk (genericPoint ρ.source.toScheme)) =
      (γ₂ ^ (-((q : ℕ) + 1 : ℤ)) * affineJetCoeff f κ ρ ĵ hV₂ hĵV₂ ((q : ℕ) + 1) c) •
        ((truncatedJetAlgebra.piece L ((q : ℕ) + 1)).presheaf.germ U₂ (genericPoint ρ.source.toScheme) hηU₂
          (truncatedJetAlgebra.framePow L U₂ μ₂ ((q : ℕ) + 1)) :
        (truncatedJetAlgebra.piece L ((q : ℕ) + 1)).stalk (genericPoint ρ.source.toScheme)))
    {W : ρ.source.toScheme.Opens} (hW : AlgebraicGeometry.IsAffineOpen W)
    (hηW : genericPoint ρ.source.toScheme ∈ W) (hW₁ : W ≤ U₁) (hW₂ : W ≤ U₂) :
    (jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L hW₁) ≫ localJet f κ ρ L hV₁ hU₁ Ψ₁ =
      (jetNeighborhood L κ).left.homOfLE (proj_preimage_mono κ ρ L hW₂) ≫ localJet f κ ρ L hV₂ hU₂ Ψ₂ := by
  classical
  haveI hInt : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  have hWV₁ : W ≤ ρ.hom ⁻¹ᵁ V₁ := hW₁.trans hUV₁
  have hWV₂ : W ≤ ρ.hom ⁻¹ᵁ V₂ := hW₂.trans hUV₂
  rw [localJet_restrict f κ ρ L hV₁ hU₁ hW hW₁ Ψ₁, localJet_restrict f κ ρ L hV₂ hU₂ hW hW₂ Ψ₂]
  have hμ₁' := hμ₁.restrict hW₁
  have hμ₂' := hμ₂.restrict hW₂
  -- the pieces of a restricted section are the restricted pieces
  have hres : ∀ {U : ρ.source.toScheme.Opens} (hWU : W ≤ U) (x : (truncatedJetAlgebra L κ).sectionsRing U)
      (q : Fin (κ + 1)),
      (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app W
          ((truncatedJetAlgebra L κ).sectionsRestrict hWU x) =
        (truncatedJetAlgebra.piece L q).res hWU
          ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app U x) :=
    fun hWU x q => AlgebraicGeometry.Scheme.Modules.Hom.app_res
      (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q) hWU x
  -- the restricted hypotheses: structure maps, constant term, generic values, frame relation
  have hover' : ∀ {V : C.toScheme.Opens} {U : ρ.source.toScheme.Opens} (hUV : U ≤ ρ.hom ⁻¹ᵁ V) (hWU : W ≤ U)
      (Ψ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
        CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U))
      (ho : ∀ r : Γ(C.toScheme, V),
        Ψ.hom (((MMSetup.cone f).hom.appLE V ((MMSetup.cone f).hom ⁻¹ᵁ V) le_rfl).hom r) =
          (truncatedJetAlgebra L κ).sectionsUnit U ((ρ.hom.appLE V U hUV).hom r))
      (r : Γ(C.toScheme, V)),
      (Ψ ≫ CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsRestrict hWU)).hom
          (((MMSetup.cone f).hom.appLE V ((MMSetup.cone f).hom ⁻¹ᵁ V) le_rfl).hom r) =
        (truncatedJetAlgebra L κ).sectionsUnit W ((ρ.hom.appLE V W (hWU.trans hUV)).hom r) := by
    intro V U hUV hWU Ψ ho r
    show (truncatedJetAlgebra L κ).sectionsRestrict hWU
      (Ψ.hom (((MMSetup.cone f).hom.appLE V ((MMSetup.cone f).hom ⁻¹ᵁ V) le_rfl).hom r)) = _
    rw [ho r]
    have h1 := PresheafOfModules.naturality_apply (truncatedJetAlgebra L κ).one.val (homOfLE hWU).op
      ((ρ.hom.appLE V U hUV).hom r)
    refine h1.symm.trans ?_
    show (truncatedJetAlgebra L κ).sectionsUnit W
      ((ρ.source.toScheme.presheaf.map (homOfLE hWU).op).hom ((ρ.hom.appLE V U hUV).hom r)) = _
    exact congrArg ((truncatedJetAlgebra L κ).sectionsUnit W)
      (congrArg (fun φ : Γ(C.toScheme, V) ⟶ Γ(ρ.source.toScheme, W) => φ.hom r)
        (AlgebraicGeometry.Scheme.Hom.appLE_map ρ.hom hUV (homOfLE hWU).op))
  have hzero' : ∀ {V : C.toScheme.Opens} {U : ρ.source.toScheme.Opens} (hUV : U ≤ ρ.hom ⁻¹ᵁ V) (hWU : W ≤ U)
      (Ψ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
        CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U))
      (hz : ∀ c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V),
        (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
            ⟨0, Nat.succ_pos κ⟩).app U (Ψ.hom c) =
          (ρ.hom.appLE V U hUV).hom
            (((MMSetup.seed f).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) V
              (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V)).hom c))
      (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V)),
      (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨0, Nat.succ_pos κ⟩).app W ((Ψ ≫ CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsRestrict hWU)).hom c) =
        (ρ.hom.appLE V W (hWU.trans hUV)).hom
          (((MMSetup.seed f).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) V
            (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V)).hom c) := by
    intro V U hUV hWU Ψ hz c
    show (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨0, Nat.succ_pos κ⟩).app W ((truncatedJetAlgebra L κ).sectionsRestrict hWU (Ψ.hom c)) = _
    rw [hres hWU, hz c]
    exact congrArg (fun φ : Γ(C.toScheme, V) ⟶ Γ(ρ.source.toScheme, W) => φ.hom _)
      (AlgebraicGeometry.Scheme.Hom.appLE_map ρ.hom hUV (homOfLE hWU).op)
  have hgen' : ∀ {V : C.toScheme.Opens} {U : ρ.source.toScheme.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
      (hĵV : (⊤ : (AlgebraicGeometry.Spec
          (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
        ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V))
      (hWU : W ≤ U) (hηU : genericPoint ρ.source.toScheme ∈ U) (μ : Γ((L.zpow (-1)).toModules, U))
      (γ : ρ.source.toScheme.functionField)
      (Ψ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
        CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U))
      (hg : ∀ (q : Fin κ) (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V)),
        ((truncatedJetAlgebra.piece L ((q : ℕ) + 1)).presheaf.germ U (genericPoint ρ.source.toScheme) hηU
            ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
              ⟨(q : ℕ) + 1, Nat.succ_lt_succ q.2⟩).app U (Ψ.hom c)) :
          (truncatedJetAlgebra.piece L ((q : ℕ) + 1)).stalk (genericPoint ρ.source.toScheme)) =
        (γ ^ (-((q : ℕ) + 1 : ℤ)) * affineJetCoeff f κ ρ ĵ hV hĵV ((q : ℕ) + 1) c) •
          ((truncatedJetAlgebra.piece L ((q : ℕ) + 1)).presheaf.germ U (genericPoint ρ.source.toScheme) hηU
            (truncatedJetAlgebra.framePow L U μ ((q : ℕ) + 1)) :
          (truncatedJetAlgebra.piece L ((q : ℕ) + 1)).stalk (genericPoint ρ.source.toScheme)))
      (q : Fin κ) (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V)),
      ((truncatedJetAlgebra.piece L ((q : ℕ) + 1)).presheaf.germ W (genericPoint ρ.source.toScheme) hηW
          ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
            ⟨(q : ℕ) + 1, Nat.succ_lt_succ q.2⟩).app W
              ((Ψ ≫ CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsRestrict hWU)).hom c)) :
        (truncatedJetAlgebra.piece L ((q : ℕ) + 1)).stalk (genericPoint ρ.source.toScheme)) =
      (γ ^ (-((q : ℕ) + 1 : ℤ)) * affineJetCoeff f κ ρ ĵ hV hĵV ((q : ℕ) + 1) c) •
        ((truncatedJetAlgebra.piece L ((q : ℕ) + 1)).presheaf.germ W (genericPoint ρ.source.toScheme) hηW
          (truncatedJetAlgebra.framePow L W ((L.zpow (-1)).toModules.res hWU μ) ((q : ℕ) + 1)) :
        (truncatedJetAlgebra.piece L ((q : ℕ) + 1)).stalk (genericPoint ρ.source.toScheme)) := by
    intro V U hV hĵV hWU hηU μ γ Ψ hg q c
    show (truncatedJetAlgebra.piece L ((q : ℕ) + 1)).presheaf.germ W (genericPoint ρ.source.toScheme) hηW
      ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨(q : ℕ) + 1, Nat.succ_lt_succ q.2⟩).app W ((truncatedJetAlgebra L κ).sectionsRestrict hWU (Ψ.hom c))) = _
    rw [hres hWU, TopCat.Presheaf.germ_res_apply, hg q c, ← truncatedJetAlgebra.res_framePow,
      TopCat.Presheaf.germ_res_apply]
  have hframe' : ∀ n : ℕ,
      γ₁ ^ (-(n : ℤ)) • ((truncatedJetAlgebra.piece L n).presheaf.germ W (genericPoint ρ.source.toScheme) hηW
          (truncatedJetAlgebra.framePow L W ((L.zpow (-1)).toModules.res hW₁ μ₁) n) :
        (truncatedJetAlgebra.piece L n).stalk (genericPoint ρ.source.toScheme)) =
      γ₂ ^ (-(n : ℤ)) • ((truncatedJetAlgebra.piece L n).presheaf.germ W (genericPoint ρ.source.toScheme) hηW
          (truncatedJetAlgebra.framePow L W ((L.zpow (-1)).toModules.res hW₂ μ₂) n) :
        (truncatedJetAlgebra.piece L n).stalk (genericPoint ρ.source.toScheme)) := by
    intro n
    rw [← truncatedJetAlgebra.res_framePow, ← truncatedJetAlgebra.res_framePow, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply]
    exact hframe n
  -- `γ = 0` for one frame forces `γ' = 0` for the other
  have hzero_of : ∀ (μ μ' : Γ((L.zpow (-1)).toModules, W))
      (hμ' : AlgebraicGeometry.Scheme.Modules.IsFrame (L.zpow (-1)).toModules W μ') (γ γ' : ρ.source.toScheme.functionField),
      (∀ n : ℕ, γ ^ (-(n : ℤ)) • ((truncatedJetAlgebra.piece L n).presheaf.germ W (genericPoint ρ.source.toScheme) hηW
          (truncatedJetAlgebra.framePow L W μ n) : (truncatedJetAlgebra.piece L n).stalk (genericPoint ρ.source.toScheme)) =
        γ' ^ (-(n : ℤ)) • ((truncatedJetAlgebra.piece L n).presheaf.germ W (genericPoint ρ.source.toScheme) hηW
          (truncatedJetAlgebra.framePow L W μ' n) : (truncatedJetAlgebra.piece L n).stalk (genericPoint ρ.source.toScheme))) →
      γ = 0 → γ' = 0 := by
    intro μ μ' hμ' γ γ' hfr hγ
    have h := hfr 1
    rw [hγ, zero_zpow _ (by norm_num), zero_smul] at h
    have h2 := (truncatedJetAlgebra.framePow_isFrame L W μ' hμ' 1).germ_smul_eq_zero hηW _ h.symm
    rwa [zpow_neg, Nat.cast_one, zpow_one, inv_eq_zero] at h2
  by_cases hγ₁ : γ₁ = 0
  · -- degenerate case: both local jets are the seed jet
    have hγ₂ : γ₂ = 0 := hzero_of _ _ hμ₂' γ₁ γ₂ hframe' hγ₁
    have hc : ∀ {V : C.toScheme.Opens} {U : ρ.source.toScheme.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
        (hĵV : (⊤ : (AlgebraicGeometry.Spec
            (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
          ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V))
        (hUV : U ≤ ρ.hom ⁻¹ᵁ V) (hWU : W ≤ U) (hηU : genericPoint ρ.source.toScheme ∈ U)
        (μ : Γ((L.zpow (-1)).toModules, U)) (hμ : AlgebraicGeometry.Scheme.Modules.IsFrame (L.zpow (-1)).toModules U μ)
        (γ : ρ.source.toScheme.functionField) (hγ : γ = 0)
        (Ψ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
          CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing U))
        (hz : ∀ c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V),
          (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
              ⟨0, Nat.succ_pos κ⟩).app U (Ψ.hom c) =
            (ρ.hom.appLE V U hUV).hom
              (((MMSetup.seed f).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) V
                (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V)).hom c))
        (hg : ∀ (q : Fin κ) (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V)),
          ((truncatedJetAlgebra.piece L ((q : ℕ) + 1)).presheaf.germ U (genericPoint ρ.source.toScheme) hηU
              ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
                ⟨(q : ℕ) + 1, Nat.succ_lt_succ q.2⟩).app U (Ψ.hom c)) :
            (truncatedJetAlgebra.piece L ((q : ℕ) + 1)).stalk (genericPoint ρ.source.toScheme)) =
          (γ ^ (-((q : ℕ) + 1 : ℤ)) * affineJetCoeff f κ ρ ĵ hV hĵV ((q : ℕ) + 1) c) •
            ((truncatedJetAlgebra.piece L ((q : ℕ) + 1)).presheaf.germ U (genericPoint ρ.source.toScheme) hηU
              (truncatedJetAlgebra.framePow L U μ ((q : ℕ) + 1)) :
            (truncatedJetAlgebra.piece L ((q : ℕ) + 1)).stalk (genericPoint ρ.source.toScheme)))
        (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V)),
        (Ψ ≫ CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsRestrict hWU)).hom c =
          (truncatedJetAlgebra L κ).sectionsUnit W ((ρ.hom.appLE V W (hWU.trans hUV)).hom
            (((MMSetup.seed f).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) V
              (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V)).hom c)) := by
      intro V U hV hĵV hUV hWU hηU μ hμ γ hγ Ψ hz hg c
      apply truncatedJetAlgebra.eq_sectionsUnit_of_pieces L κ _ _ (hzero' hUV hWU Ψ hz c)
      intro q
      apply truncatedJetAlgebra.piece_section_ext_of_germ L hηW (hμ.restrict hWU) ((q : ℕ) + 1)
      rw [hgen' hV hĵV hWU hηU μ γ Ψ hg q c, hγ, zero_zpow _ (by omega), zero_mul, zero_smul, map_zero]
    rw [localJet_eq_seed f κ ρ L hV₁ hW hWV₁ _ (hc hV₁ hĵV₁ hUV₁ hW₁ hηU₁ μ₁ hμ₁ γ₁ hγ₁ Ψ₁ hzero₁ hgen₁),
      localJet_eq_seed f κ ρ L hV₂ hW hWV₂ _ (hc hV₂ hĵV₂ hUV₂ hW₂ hηU₂ μ₂ hμ₂ γ₂ hγ₂ Ψ₂ hzero₂ hgen₂)]
  · -- main case: compare through the generic point `θ : D → p_L⁻¹(W)`
    have hγ₂ : γ₂ ≠ 0 := fun h => hγ₁ (hzero_of _ _ hμ₁' γ₂ γ₁ (fun n => (hframe' n).symm) h)
    letI := genericOverInst ρ
    have h₁ := pointOfRingHom_localJet_eq_genericBasedJet f κ ρ L hηW hμ₁' γ₁ ĵ hĵ hγ₁ hW hV₁ hĵV₁ hWV₁ γ₁
      (fun _ => rfl) _ (hzero' hUV₁ hW₁ Ψ₁ hzero₁) (hgen' hV₁ hĵV₁ hW₁ hηU₁ μ₁ γ₁ Ψ₁ hgen₁)
    have h₂ := pointOfRingHom_localJet_eq_genericBasedJet f κ ρ L hηW hμ₁' γ₁ ĵ hĵ hγ₁ hW hV₂ hĵV₂ hWV₂ γ₂
      hframe' _ (hzero' hUV₂ hW₂ Ψ₂ hzero₂) (hgen' hV₂ hĵV₂ hW₂ hηU₂ μ₂ γ₂ Ψ₂ hgen₂)
    have hθg := h₁.trans h₂.symm
    set θ := pointOfRingHom κ ρ L hW (genericPointRingHom κ ρ L hηW hμ₁' γ₁) with hθ
    set g₁ := localJet f κ ρ L hV₁ hW (Ψ₁ ≫ CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsRestrict hW₁)) with hg₁def
    set g₂ := localJet f κ ρ L hV₂ hW (Ψ₂ ≫ CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsRestrict hW₂)) with hg₂def
    -- both local jets land in `π⁻¹V₁`
    have hg₁ : (⊤ : (jetNeighborhood.proj L κ ⁻¹ᵁ W).toScheme.Opens) ≤ g₁ ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ V₁) :=
      top_le_localJet_preimage f κ ρ L hV₁ hW _
    have hg₂ : (⊤ : (jetNeighborhood.proj L κ ⁻¹ᵁ W).toScheme.Opens) ≤ g₂ ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ V₁) := by
      have hover := localJet_over f κ ρ L hV₂ hW _ hWV₂ (hover' hUV₂ hW₂ Ψ₂ hover₂)
      rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, hover]
      intro x _
      exact hWV₁ x.2
    apply localJet_hom_ext f κ ρ L hV₁ hW hg₁ hg₂
    -- the ring maps agree after composing with the injective `θ^♯`
    have e₂ : (⊤ : (jetThickening (k := k) κ (genericOver ρ).left).Opens) ≤ θ ⁻¹ᵁ ⊤ := fun _ _ => trivial
    have hA : (θ ≫ g₁).appLE ((MMSetup.cone f).hom ⁻¹ᵁ V₁) ⊤ (fun x _ => hg₁ (x := θ.base x) trivial) =
        (θ ≫ g₂).appLE ((MMSetup.cone f).hom ⁻¹ᵁ V₁) ⊤ (fun x _ => hg₂ (x := θ.base x) trivial) :=
      appLE_eq_of_eq hθg _ _ _ _
    rw [← AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE θ g₁ ((MMSetup.cone f).hom ⁻¹ᵁ V₁) ⊤ ⊤ hg₁ e₂,
      ← AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE θ g₂ ((MMSetup.cone f).hom ⁻¹ᵁ V₁) ⊤ ⊤ hg₂ e₂] at hA
    have hθtop : θ.appLE ⊤ ⊤ e₂ = θ.appTop := by
      rw [AlgebraicGeometry.Scheme.Hom.appTop, AlgebraicGeometry.Scheme.Hom.app_eq_appLE]
      rfl
    rw [hθtop, hθ, pointOfRingHom_appTop] at hA
    set e := AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨W, hW⟩ with he
    have hinj : Function.Injective (e.inv.appTop ≫ (AlgebraicGeometry.Scheme.ΓSpecIso _).hom ≫
        genericPointRingHom κ ρ L hηW hμ₁' γ₁).hom := by
      have hΓ : Function.Injective (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing W))).hom.hom := by
        intro a b h
        have := congrArg (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing W))).inv.hom h
        rwa [CategoryTheory.Iso.hom_inv_id_apply, CategoryTheory.Iso.hom_inv_id_apply] at this
      have he' : Function.Injective e.inv.appTop.hom := by
        intro a b h
        have h2 : ∀ y, e.hom.appTop.hom (e.inv.appTop.hom y) = y := fun y => by
          have := congrArg (fun φ : Γ((jetNeighborhood.proj L κ ⁻¹ᵁ W).toScheme, ⊤) ⟶
              Γ((jetNeighborhood.proj L κ ⁻¹ᵁ W).toScheme, ⊤) => φ.hom y)
            ((AlgebraicGeometry.Scheme.Hom.comp_appTop e.hom e.inv).symm.trans
              (by rw [Iso.hom_inv_id, AlgebraicGeometry.Scheme.Hom.id_appTop]))
          exact this
        rw [← h2 a, ← h2 b, h]
      show Function.Injective ((genericPointRingHom κ ρ L hηW hμ₁' γ₁).hom ∘
        ((AlgebraicGeometry.Scheme.ΓSpecIso _).hom.hom ∘ e.inv.appTop.hom))
      exact (genericPointRingHom_injective κ ρ L hηW hμ₁' γ₁ hγ₁).comp (hΓ.comp he')
    ext c
    apply hinj
    have := congrArg (fun m : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V₁) ⟶
      Γ(jetThickening (k := k) κ (genericOver ρ).left, ⊤) => m.hom c) hA
    exact this

end jetNeighborhood

end
