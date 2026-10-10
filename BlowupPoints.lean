import BlowupScheme
import BlowupStrict

/-!
# ブローアップ(層8: `k` 点の対応)

集合論的モデルの点 `z = ((P), L) ∈ blowupSet k` から、`Proj B` の点(斉次素イデアル)
`𝔭(z) = homogeneousCore (ker (B → k : g ↦ g(P, rep L)))` を作る(`blowupPoint`)。
これは単射(`blowupPoint_injective`)。

* `ev z : B →+* k`:`(x, y, t, u) ↦ (P₀, P₁, v₀, v₁)`(`v = rep L`)での値。
  `x u − t y` は `z ∈ X` で消えるので `B` に降りる。
* `𝔭(z)` は素イデアル(`Ideal.IsPrime.homogeneousCore`)で、`t` か `u` を含まない
  (`rep L ≠ 0`)ので `Proj` の点になる。
-/

open MvPolynomial Projectivization AlgebraicGeometry

namespace Blowup

section points

variable (k : Type*) [Field k]

/-- 点 `z ∈ X` での評価 `B → k`。 -/
noncomputable def blowEv (z : blowupSet k) : BlowRing k →+* k :=
  Ideal.Quotient.lift (blowIdeal k) (MvPolynomial.eval ![z.1.1 0, z.1.1 1, z.1.2.rep 0, z.1.2.rep 1])
    (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      have h0 : MvPolynomial.eval ![z.1.1 0, z.1.1 1, z.1.2.rep 0, z.1.2.rep 1] (blowEq k) = 0 := by
        have := evalPair_blowEq z.1.1 z.1.2.rep
        have hz : z.1.1 0 * z.1.2.rep 1 = z.1.2.rep 0 * z.1.1 1 := z.2
        change evalPair z.1.1 z.1.2.rep (blowEq k) = 0
        rw [this, hz, sub_self]
      rw [map_mul, h0, mul_zero])

lemma blowEv_mk (z : blowupSet k) (g : MvPolynomial (Fin 4) k) :
    blowEv k z (Ideal.Quotient.mk (blowIdeal k) g) = evalPair z.1.1 z.1.2.rep g :=
  Ideal.Quotient.lift_mk _ _ _

/-- 点 `z` に対応する斉次イデアル `homogeneousCore (ker ev)`。 -/
noncomputable def pointIdeal (z : blowupSet k) : HomogeneousIdeal (blowGrading k) :=
  (RingHom.ker (blowEv k z)).homogeneousCore (blowGrading k)

lemma mem_pointIdeal_iff (z : blowupSet k) {b : BlowRing k}
    (hb : SetLike.IsHomogeneousElem (blowGrading k) b) :
    b ∈ pointIdeal k z ↔ blowEv k z b = 0 := by
  constructor
  · intro h
    exact (RingHom.mem_ker).mp (Ideal.toIdeal_homogeneousCore_le _ _ h)
  · intro h
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem hb (RingHom.mem_ker.mpr h)

lemma mk_mem_blowGrading {g : MvPolynomial (Fin 4) k} {i : ℕ} (hg : g ∈ bigrading k i) :
    Ideal.Quotient.mk (blowIdeal k) g ∈ blowGrading k i :=
  GradedQuotient.mem_grading hg

lemma X2_mem : (X 2 : MvPolynomial (Fin 4) k) ∈ bigrading k 1 :=
  (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (isWeightedHomogeneous_X k wt 2 : IsWeightedHomogeneous wt (X 2 : MvPolynomial (Fin 4) k) 1)

lemma X3_mem : (X 3 : MvPolynomial (Fin 4) k) ∈ bigrading k 1 :=
  (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (isWeightedHomogeneous_X k wt 3 : IsWeightedHomogeneous wt (X 3 : MvPolynomial (Fin 4) k) 1)

lemma C_mem (c : k) : (C c : MvPolynomial (Fin 4) k) ∈ bigrading k 0 :=
  (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWeightedHomogeneous_C wt c)

lemma X0_mem : (X 0 : MvPolynomial (Fin 4) k) ∈ bigrading k 0 :=
  (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (isWeightedHomogeneous_X k wt 0 : IsWeightedHomogeneous wt (X 0 : MvPolynomial (Fin 4) k) 0)

lemma X1_mem : (X 1 : MvPolynomial (Fin 4) k) ∈ bigrading k 0 :=
  (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (isWeightedHomogeneous_X k wt 1 : IsWeightedHomogeneous wt (X 1 : MvPolynomial (Fin 4) k) 0)

/-- **`z ∈ X` から `Proj B` の点**。 -/
noncomputable def blowupPoint (z : blowupSet k) : ProjectiveSpectrum (blowGrading k) where
  asHomogeneousIdeal := pointIdeal k z
  isPrime := (RingHom.ker_isPrime (blowEv k z)).homogeneousCore
  not_irrelevant_le := by
    intro hle
    have hmem : ∀ (g : MvPolynomial (Fin 4) k), g ∈ bigrading k 1 →
        Ideal.Quotient.mk (blowIdeal k) g ∈ pointIdeal k z := by
      intro g hg
      refine hle ?_
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne (blowGrading k) (mk_mem_blowGrading k hg) (by norm_num)]
    have h2 := (mem_pointIdeal_iff k z ⟨1, mk_mem_blowGrading k (X2_mem k)⟩).mp
      (hmem _ (X2_mem k))
    have h3 := (mem_pointIdeal_iff k z ⟨1, mk_mem_blowGrading k (X3_mem k)⟩).mp
      (hmem _ (X3_mem k))
    rw [blowEv_mk, evalPair_X2] at h2
    rw [blowEv_mk, evalPair_X3] at h3
    apply z.1.2.rep_nonzero
    ext i
    fin_cases i
    · exact h2
    · exact h3

lemma blowupPoint_key (z z' : blowupSet k) (h : blowupPoint k z = blowupPoint k z')
    (g : MvPolynomial (Fin 4) k) (i : ℕ) (hg : g ∈ bigrading k i)
    (h0 : evalPair z.1.1 z.1.2.rep g = 0) : evalPair z'.1.1 z'.1.2.rep g = 0 := by
  have hI : pointIdeal k z = pointIdeal k z' := congrArg ProjectiveSpectrum.asHomogeneousIdeal h
  have hh : SetLike.IsHomogeneousElem (blowGrading k) (Ideal.Quotient.mk (blowIdeal k) g) :=
    ⟨i, mk_mem_blowGrading k hg⟩
  have h1 : Ideal.Quotient.mk (blowIdeal k) g ∈ pointIdeal k z :=
    (mem_pointIdeal_iff k z hh).mpr (by rw [blowEv_mk]; exact h0)
  rw [hI] at h1
  have := (mem_pointIdeal_iff k z' hh).mp h1
  rwa [blowEv_mk] at this

/-- **`blowupSet k → Proj B` の点は単射**。 -/
theorem blowupPoint_injective : Function.Injective (blowupPoint k) := by
  rintro ⟨⟨P, L⟩, hz⟩ ⟨⟨P', L'⟩, hz'⟩ h
  have key := blowupPoint_key k ⟨(P, L), hz⟩ ⟨(P', L'), hz'⟩ h
  have hx : P 0 = P' 0 := by
    have := key (X 0 - C (P 0)) 0 (Submodule.sub_mem _ (X0_mem k) (C_mem k _)) (by
      rw [evalPair_sub, evalPair_X0, evalPair_C]
      exact sub_self _)
    rw [evalPair_sub, evalPair_X0, evalPair_C] at this
    exact (sub_eq_zero.mp this).symm
  have hy : P 1 = P' 1 := by
    have := key (X 1 - C (P 1)) 0 (Submodule.sub_mem _ (X1_mem k) (C_mem k _)) (by
      rw [evalPair_sub, evalPair_X1, evalPair_C]
      exact sub_self _)
    rw [evalPair_sub, evalPair_X1, evalPair_C] at this
    exact (sub_eq_zero.mp this).symm
  have hP : P = P' := by
    ext i
    fin_cases i
    · exact hx
    · exact hy
  have hL : L = L' := by
    have hlin : (C (L.rep 1) * X 2 - C (L.rep 0) * X 3 : MvPolynomial (Fin 4) k) ∈ bigrading k 1 := by
      have h2 : (C (L.rep 1) * X 2 : MvPolynomial (Fin 4) k) ∈ bigrading k 1 := by
        have := SetLike.mul_mem_graded (C_mem k (L.rep 1)) (X2_mem k)
        simpa using this
      have h3 : (C (L.rep 0) * X 3 : MvPolynomial (Fin 4) k) ∈ bigrading k 1 := by
        have := SetLike.mul_mem_graded (C_mem k (L.rep 0)) (X3_mem k)
        simpa using this
      exact Submodule.sub_mem _ h2 h3
    have := key _ 1 hlin (by
      rw [evalPair_sub, evalPair_mul, evalPair_mul, evalPair_C, evalPair_C, evalPair_X2,
        evalPair_X3]
      exact sub_eq_zero.mpr (mul_comm _ _))
    rw [evalPair_sub, evalPair_mul, evalPair_mul, evalPair_C, evalPair_C, evalPair_X2,
      evalPair_X3] at this
    have hpar : L'.rep 0 * L.rep 1 = L.rep 0 * L'.rep 1 := by
      linear_combination this
    have := mk_eq_of_parallel L'.rep_nonzero L.rep_nonzero hpar
    rwa [mk_rep, mk_rep] at this
  exact Subtype.ext (Prod.ext hP hL)

end points

end Blowup
