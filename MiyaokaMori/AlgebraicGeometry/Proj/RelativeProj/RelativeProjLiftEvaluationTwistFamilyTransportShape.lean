import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.RestrictToLambdaBundleFamilyTransition_PullbackSections
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyTransportEval

/-! # The two transport isomorphisms of the dictionary, at the variable level

Helper module for `RelativeProjLiftEvaluationTwistFamilyTransport.lean`. The two isomorphisms of the dictionary,
`chartTwistIso : ρ^*O(n) ≅ O_{Proj A(W)}(n)` and `twistTransport : (τ^*O(n))|_V ≅ φ_V^*O_{Proj A(W)}(n)`, are
composites of the comparison isomorphisms of the pseudofunctor `Modules.pullback` (`pullbackComp`, `pullbackCongr`,
`pullbackId`, `restrictFunctorIsoPullback`) with one geometric input each (`twistAffineIso`, Stacks 01NR, resp. the
chart isomorphism). Here the composites are defined **with all inputs as variables** (`chartIsoShape`,
`transportIsoShape`), and the section-tracking lemmas — what the composite does to a pulled-back section
`pullbackSectionsOn … s` — are proved once at this level (`chartIsoShape_hom_app_pullbackSectionsOn`,
`transportIsoShape_hom_app_pullbackSectionsOn`).

**Why (kernel performance).** The same rewrite chains, written directly on the concrete
objects, elaborate but cost 13–16 s of *kernel* time per
step: every unit-tracking lemma has source/target types that agree only after unfolding `Modules.pullback`
(`(pullback g ⋙ pullback f).obj M` vs nested `.obj`) or `restrictFunctor` (`M.restrict j` vs `Γ(M, j ''ᵁ ·)`), and on a
concrete goal the kernel re-normalises the whole `SheafOfModules.pullback` construction at each such spot. At the
variable level the normalisation is cheap, and the concrete statements are then *first-order instances* of the
general lemmas (the concrete isomorphisms are **defined** as `chartIsoShape …` / `transportIsoShape …` applied to
atomic arguments, so `unfold` produces exactly the instance), which the kernel checks by structural comparison.

Sources: Stacks 01NQ (the chart `π⁻¹W ≅ Proj A(W)`), 01NR (`O(n)` on the chart), 01MN. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

section Chart

variable {P R Q : AlgebraicGeometry.Scheme.{u}}

/-- **The chart isomorphism shape** `ρ^*N ≅ G` for `ρ = e⁻¹ ≫ ι` with `ι : R ⟶ P` an open immersion,
`e : R ≅ Q`, and a chart comparison `a : N|_R ≅ e^*G`:
`ρ^*N ≅ (e⁻¹ ≫ ι)^*N ≅ e⁻¹^*(ι^*N) ≅ e⁻¹^*(N|_R) ≅ e⁻¹^*(e^*G) ≅ (e⁻¹ ≫ e)^*G ≅ 𝟙^*G ≅ G`.
`relativeProj.chartTwistIso S W n` is this shape with `ι := (π⁻¹W).ι`, `e := affineIso S W`,
`ρ := chartEmbedding S W`, `N := twist S n`, `G := Proj.twist 𝒜 n`, `a := twistAffineIso S W n`. -/
def chartIsoShape (ι : R ⟶ P) [AlgebraicGeometry.IsOpenImmersion ι] (e : R ≅ Q) (ρ : Q ⟶ P)
    (hρ : e.inv ≫ ι = ρ) (N : P.Modules) (G : Q.Modules)
    (a : N.restrict ι ≅ (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj G) :
    (AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N ≅ G :=
  (AlgebraicGeometry.Scheme.Modules.pullbackCongr hρ.symm).app N ≪≫
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp e.inv ι).app N).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback e.inv).mapIso
      (((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback ι).app N).symm ≪≫ a) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp e.inv e.hom).app G ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr e.inv_hom_id).app G ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackId Q).app G

/-- **The chart shape on a pulled-back section.** If the chart comparison `a` sends `(rFIP ι)⁻¹(η_ι s)` to
`(η_e t)|_{ι⁻¹B}` (`ha`; the form of `twistAffineIso_hom_app_unit_evaluationLocal`), then for every open
`U ≤ ρ⁻¹B` the chart shape sends `(ρ^*s)|_U` to `t|_U`.

Proof: factor by factor (`Iso.trans_hom`, `comp_app_apply_tfam`): `pullbackCongr` keeps a pulled-back section
(`pullbackCongr_hom_app_pullbackSectionsOn`), `pullbackComp⁻¹` splits `(e⁻¹ ≫ ι)^*` into two pullbacks
(`pullbackComp_inv_app_pullbackSectionsOn`), the middle factor acts inside the pulled-back section
(`pullback_map_app_pullbackSectionsOn_bc`) where `ha` applies, then `pullbackSectionsOn_res`,
`pullbackComp_hom_app_pullbackSectionsOn`, `pullbackCongr_hom_app_pullbackSectionsOn` and
`pullbackId_hom_app_pullbackSectionsOn_tfam` collapse the remaining factors. -/
theorem chartIsoShape_hom_app_pullbackSectionsOn (ι : R ⟶ P) [AlgebraicGeometry.IsOpenImmersion ι] (e : R ≅ Q)
    (ρ : Q ⟶ P) (hρ : e.inv ≫ ι = ρ) (N : P.Modules) (G : Q.Modules)
    (a : N.restrict ι ≅ (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj G)
    (B : P.Opens) (s : Γ(N, B)) (t : Γ(G, ⊤))
    (ha : a.hom.app (ι ⁻¹ᵁ B)
        (((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback ι).app N).inv.app (ι ⁻¹ᵁ B)
          (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom ι N B s)) =
      ((AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj G).presheaf.map
        (homOfLE (le_top : ι ⁻¹ᵁ B ≤ e.hom ⁻¹ᵁ ⊤)).op
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom e.hom G ⊤ t))
    (U : Q.Opens) (k : U ≤ ρ ⁻¹ᵁ B) :
    (AlgebraicGeometry.Scheme.Modules.chartIsoShape ι e ρ hρ N G a).hom.app U
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn ρ N B U k s) =
      G.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t := by
  subst hρ
  have k₁ : U ≤ e.inv ⁻¹ᵁ (ι ⁻¹ᵁ B) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage]
    exact k
  have k₄ : U ≤ e.inv ⁻¹ᵁ (e.hom ⁻¹ᵁ ⊤) := le_top
  have k₅ : U ≤ (e.inv ≫ e.hom) ⁻¹ᵁ ⊤ := le_top
  have k₆ : U ≤ (𝟙 Q) ⁻¹ᵁ ⊤ := le_top
  unfold AlgebraicGeometry.Scheme.Modules.chartIsoShape
  rw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
    AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam, AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam,
    AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam, AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam,
    AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam]
  rw [AlgebraicGeometry.Scheme.Modules.pullbackCongr_hom_app_pullbackSectionsOn _ N B U k k s]
  erw [AlgebraicGeometry.Scheme.Modules.pullbackComp_inv_app_pullbackSectionsOn e.inv ι N B U k₁ k s]
  erw [AlgebraicGeometry.Scheme.Modules.pullback_map_app_pullbackSectionsOn_bc e.inv
    (((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback ι).app N).inv ≫ a.hom) (ι ⁻¹ᵁ B) U k₁
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom ι N B s)]
  erw [AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback ι).app N).inv a.hom (ι ⁻¹ᵁ B)
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom ι N B s)]
  erw [ha]
  erw [← AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_res e.inv
    ((AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj G) k₄ k₁ le_top
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom e.hom G ⊤ t)]
  erw [AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_pullbackSectionsOn e.inv e.hom G ⊤ U k₄ k₅ t]
  erw [AlgebraicGeometry.Scheme.Modules.pullbackCongr_hom_app_pullbackSectionsOn e.inv_hom_id G ⊤ U k₅ k₆]
  erw [AlgebraicGeometry.Scheme.Modules.pullbackId_hom_app_pullbackSectionsOn_tfam G ⊤ U k₆ t]
  rfl

end Chart

section Transport

variable {V T P Q : AlgebraicGeometry.Scheme.{u}}

/-- **The transport isomorphism shape** `(τ^*N)|_V ≅ φ^*G` for a commutative square `j ≫ τ = φ ≫ ρ`
(`j : V ⟶ T` an open immersion) and a chart isomorphism `c : ρ^*N ≅ G`:
`(τ^*N)|_V ≅ j^*τ^*N ≅ (j ≫ τ)^*N = (φ ≫ ρ)^*N ≅ φ^*(ρ^*N) ≅ φ^*G`.
`relativeProj.LiftData.twistTransport` is this shape with `j := V.ι`, `τ := lift S f M D`, `φ := φ_V`,
`ρ := chartEmbedding S W`, `N := twist S n`, `G := Proj.twist 𝒜 n`, `c := chartTwistIso S W n`. -/
def transportIsoShape (j : V ⟶ T) [AlgebraicGeometry.IsOpenImmersion j] (τ : T ⟶ P) (φ : V ⟶ Q) (ρ : Q ⟶ P)
    (hτ : j ≫ τ = φ ≫ ρ) (N : P.Modules) (G : Q.Modules)
    (c : (AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N ≅ G) :
    ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N).restrict j ≅
      (AlgebraicGeometry.Scheme.Modules.pullback φ).obj G :=
  (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback j).app
      ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp j τ).app N ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr hτ).app N ≪≫
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp φ ρ).app N).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback φ).mapIso c

set_option backward.isDefEq.respectTransparency.types false in
/-- **The transport shape on a pulled-back section.** If the chart isomorphism `c` sends `(ρ^*s)|_U` to `t|_U`
for every `U ≤ ρ⁻¹B` (`hc`; the form of `chartIsoShape_hom_app_pullbackSectionsOn`), then the transport shape
sends `(τ^*s)|_{j''A'}` (read as a section of `(τ^*N)|_V` over `A'`) to `(φ^*t)|_{A'}`.

Proof: factor by factor. `rFIP` gives `(j^*(η_τ s))|_{A'}` (`restrictFunctorIsoPullback_hom_app_apply`,
`pullbackSectionsOn_res`); `pullbackComp j τ` gives `((j ≫ τ)^*s)|_{A'}`; `pullbackCongr hτ` gives
`((φ ≫ ρ)^*s)|_{A'}`; `pullbackComp⁻¹` gives `(φ^*(η_ρ s))|_{A'}`; `φ^*c` acts inside
(`pullback_map_app_pullbackSectionsOn_bc`), where `hc` at `U := ρ⁻¹B` (`pullbackSectionsOn_self`) gives
`t|_{ρ⁻¹B}`, and `pullbackSectionsOn_res` moves the restriction out. -/
theorem transportIsoShape_hom_app_pullbackSectionsOn (j : V ⟶ T) [AlgebraicGeometry.IsOpenImmersion j]
    (τ : T ⟶ P) (φ : V ⟶ Q) (ρ : Q ⟶ P) (hτ : j ≫ τ = φ ≫ ρ) (N : P.Modules) (G : Q.Modules)
    (c : (AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N ≅ G)
    (B : P.Opens) (s : Γ(N, B)) (t : Γ(G, ⊤))
    (hc : ∀ (U : Q.Opens) (k : U ≤ ρ ⁻¹ᵁ B),
      c.hom.app U (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn ρ N B U k s) =
        G.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t)
    (A' : V.Opens) (h : j ''ᵁ A' ≤ τ ⁻¹ᵁ B) (h' : A' ≤ φ ⁻¹ᵁ ⊤) :
    (AlgebraicGeometry.Scheme.Modules.transportIsoShape j τ φ ρ hτ N G c).hom.app A'
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn τ N B (j ''ᵁ A') h s) =
      AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn φ G ⊤ A' h' t := by
  have hA' : A' ≤ j ⁻¹ᵁ (j ''ᵁ A') := le_of_eq (j.preimage_image_eq A').symm
  have h₂ : A' ≤ j ⁻¹ᵁ (τ ⁻¹ᵁ B) := hA'.trans (j.preimage_mono h)
  have h₃ : A' ≤ (j ≫ τ) ⁻¹ᵁ B := by
    rw [AlgebraicGeometry.Scheme.Hom.comp_preimage]
    exact h₂
  have h₄ : A' ≤ (φ ≫ ρ) ⁻¹ᵁ B := by
    rw [← hτ]
    exact h₃
  have h₅ : A' ≤ φ ⁻¹ᵁ (ρ ⁻¹ᵁ B) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage]
    exact h₄
  unfold AlgebraicGeometry.Scheme.Modules.transportIsoShape
  rw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam, AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam,
    AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam, AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam]
  erw [AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_hom_app_apply j
    ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N) A'
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn τ N B (j ''ᵁ A') h s)]
  rw [AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_apply τ N B (j ''ᵁ A') h s,
    ← AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_res j
      ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N) h₂ hA' h
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom τ N B s)]
  erw [AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_pullbackSectionsOn j τ N B A' h₂ h₃ s]
  erw [AlgebraicGeometry.Scheme.Modules.pullbackCongr_hom_app_pullbackSectionsOn hτ N B A' h₃ h₄ s]
  erw [AlgebraicGeometry.Scheme.Modules.pullbackComp_inv_app_pullbackSectionsOn φ ρ N B A' h₅ h₄ s]
  erw [AlgebraicGeometry.Scheme.Modules.pullback_map_app_pullbackSectionsOn_bc φ c.hom (ρ ⁻¹ᵁ B) A' h₅
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom ρ N B s)]
  rw [← AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_self ρ N B s, hc (ρ ⁻¹ᵁ B) le_rfl,
    ← AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_res φ G h' h₅ le_top t]

end Transport

end AlgebraicGeometry.Scheme.Modules

end
