import GradedQuotient
import BlowupProjective

/-!
# ブローアップ(層7: `Scheme` としての構成)

体 `k` 上、`𝔸² × ℙ¹` の座標環 `k[x, y, t, u]`(`(t, u)` に次数 1、`x, y` に次数 0 の重み付き次数)を
斉次イデアル `(x u − t y)` で割った次数付き環 `B` を作り、`Proj B` を `Scheme` として
ブローアップ `Bl₀ 𝔸²` とみなす。構造射 `Proj B ⟶ Spec (B₀)` は `Proj.toSpecZero`。

ここでは構成と、`B₀` の元としての `x, y`、斉次イデアルの証明を与える。
-/

open MvPolynomial AlgebraicGeometry

universe u

namespace Blowup

section scheme

variable (k : Type u) [Field k]

/-- 重み `x, y ↦ 0`、`t, u ↦ 1`。 -/
def wt : Fin 4 → ℕ := ![0, 0, 1, 1]

/-- `k[x, y, t, u]` の `(t, u)` についての次数付け。 -/
noncomputable def bigrading : ℕ → Submodule k (MvPolynomial (Fin 4) k) :=
  weightedHomogeneousSubmodule k wt

noncomputable instance : GradedAlgebra (bigrading k) := weightedGradedAlgebra k wt

/-- ブローアップを定めるイデアル `(x u − t y)`。 -/
noncomputable def blowIdeal : Ideal (MvPolynomial (Fin 4) k) := Ideal.span {blowEq k}

lemma blowEq_mem_bigrading : blowEq k ∈ bigrading k 1 := by
  have h03 : wt 0 + wt 3 = 1 := rfl
  have h21 : wt 2 + wt 1 = 1 := rfl
  have h1 := (isWeightedHomogeneous_X k wt 0).mul (isWeightedHomogeneous_X k wt 3)
  have h2 := (isWeightedHomogeneous_X k wt 2).mul (isWeightedHomogeneous_X k wt 1)
  rw [h03] at h1
  rw [h21] at h2
  exact Submodule.sub_mem _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h1)
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2)

lemma blowIdeal_homogeneous (i : ℕ) (r : MvPolynomial (Fin 4) k) (hr : r ∈ blowIdeal k) :
    (DirectSum.decompose (bigrading k) r i : MvPolynomial (Fin 4) k) ∈ blowIdeal k := by
  classical
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  rw [DirectSum.coe_decompose_mul_of_right_mem (bigrading k) i (blowEq_mem_bigrading k)]
  split_ifs
  · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · exact Ideal.zero_mem _

/-- 座標環 `B = k[x, y, t, u] / (x u − t y)`。 -/
abbrev BlowRing : Type u := MvPolynomial (Fin 4) k ⧸ blowIdeal k

/-- `B` の次数付け。 -/
noncomputable abbrev blowGrading : ℕ → Submodule k (BlowRing k) :=
  GradedQuotient.grading (bigrading k) (blowIdeal k)

noncomputable instance : GradedRing (blowGrading k) :=
  GradedQuotient.gradedRing (blowIdeal_homogeneous k)

/-- **`Scheme` としてのブローアップ `Proj B`**。 -/
noncomputable def blowupScheme : Scheme.{u} := Proj (blowGrading k)

/-- 構造射 `Proj B ⟶ Spec B₀`(`B₀` は次数 0 の部分環で、`k[x, y]` に当たる)。 -/
noncomputable def blowupMap : blowupScheme k ⟶ Spec (CommRingCat.of (blowGrading k 0)) :=
  Proj.toSpecZero (blowGrading k)

end scheme

end Blowup
