# Blowup.lean — 主定理の数学的な意味

対象は尖点型の曲線 `C : y^a = x^b`(`a, b ≥ 1`)を原点でブローアップし続けたとき、
**何回で原点の特異性(重複度 ≥ 2)が消えるか**。

## 用語の対応

| Lean | 数学 |
|---|---|
| `Poly R = MvPolynomial (Fin 2) R` | `R[x, y]`(`x = X 0`, `y = X 1`) |
| `binom a b = X 1 ^ a - X 0 ^ b` | `y^a − x^b` |
| `mult f` | 原点での重複度(`f` の単項式の全次数の最小値) |
| `step (a, b)` | `a ≤ b` なら `(a, b−a)`、そうでなければ `(a−b, b)`。引き算版ユークリッド互除法の1手 |
| `blowCount a b` | `step` を、`a = 0 ∨ b = 0 ∨ a = 1 ∨ b = 1` になるまで繰り返した回数 |
| `step^[k] (a, b)` | `k` 回ブローアップした後の strict transform の指数ペア |

## `binom_resolution`

仮定: `a, b : ℕ` だけ(係数環 `R` は可換環。`Nontrivial` は内部で使う)。

結論は2つ。

1. **各段 `k < blowCount a b` で**
   * その段の曲線 `y^a' = x^b'`(`(a', b') = step^[k] (a, b)`)の重複度は `≥ 2`(まだ特異)。
   * 適切なチャートへの代入 `σ`(`y = x u` または `x = y v` に当たる `R`-代数準同型)と座標 `i` が存在して
     `σ(f) = X_i ^ (mult f) * f̃`、`f̃ = binom (step^[k+1] ..)`。
     つまり「全 transform = 例外因子の `mult` 倍 + strict transform」で、
     strict transform が再び同じ形の二項式になる。
2. **`N = blowCount a b` 段目では重複度 `≤ 1`**(非特異、または原点を通らない)。

つまり「`N` 回ブローアップすれば原点で非特異になる」という上界。

## `blowCount_isLeast`

`{k | mult (binom (step^[k] (a,b))) ≤ 1}` の **最小元が `blowCount a b`**。
`binom_resolution` が「`N` 回で足りる」、各段 `k < N` で重複度 `≥ 2` が「`N` 回未満では足りない」を与えるので、
この `N` はこのモデルの下で最小。

## `theoremA`(`p, q`、曲線 `y^p = x^q`)

`blocks q p` は `q/p` の連分数 `[a_0; a_1, …, a_r]` の互除法ブロック `(r_i, a_i)`
(余り `r_i`、商 `a_i`、余りが `≤ 1` で停止)。結論は3つ。

1. `blowCount p q = a_0 + a_1 + … + a_{r−1}`(部分商の総和)。
2. 各ブローアップで潰す点の重複度の列は、`r_0` が `a_0` 個、`r_1` が `a_1` 個、… の順(`expand (blocks q p)`)。
3. `blowCount p q` は重複度が `≤ 1` になる最初の段(= `blowCount_isLeast`)。

例: `y^2 = x^3`(`p=2, q=3`): `3 = 1·2 + 1`、ブロックは `[(2,1)]`、`N = 1`、重複度列 `[2]`。
1回のブローアップで非特異(ただし例外因子と接するので正規交差ではない — 下記)。

## 注意(このモデルが言っていないこと)

* 追っているのは **原点の strict transform だけ**。別のチャートに現れる他の特異点や、
  例外因子との交わり(正規交差かどうか)は扱っていない。「正規交差化までの回数」ではなく
  「原点での重複度が 1 以下になるまでの回数」。
* 幾何的な主張(`X ⊂ 𝔸² × ℙ¹`)は `Blowup.lean` 後半の集合論的モデルで別に与えており、
  上の代数的な定理とは `σ` を介して対応する形になっている(接続の厳密化は次の課題)。
* **ビルド**:手元(RAM 8GB)では `import Mathlib` だけで極端に遅いので、検証は GitHub Actions の
  `lake build` で行っている(`Blowup`・`BlowupGeometry` とも成功)。
* **ファイル構成**:`Blowup.lean`(多項式・`binom_resolution`・`theoremA`)と、
  それを `import` する `BlowupGeometry.lean`(集合論的モデル `X ⊂ 𝔸² × ℙ¹`、全単射・稠密性・既約性・
  strict transform = 閉包・接線の重複度の総和)。
* `BlowupProjective.lean`:`X`・`E`・`φ⁻¹(Y)` を `(t,u)` に斉次な多項式の零点集合
  (`projZeroSet`、`IsProjClosed`)として記述。
* `BlowupStrict.lean`:strict transform の斉次方程式 `strictEq f`(`(t,u)` について `mult f` 次斉次)。
  チャート `t`・`u` でそれぞれ `f̃`・`f̃'` に一致し、`X ∩ Z(strictEq f)` は各チャートで
  `closure(φ⁻¹(Y∖0))` に一致する(`strictEq_mem_iff_chart_t/u`、`k` 代数閉体)。
* `BlowupClosure.lean`:二つのチャートの統合。`strict_eq_projClosure`:`k` 代数閉体・`f ≠ 0` で `X ∩ Z(strictEq f) = projClosure (φ⁻¹(Y∖0) ∩ X)`(𝔸² × ℙ¹ での射影的な閉包)。
* `GradedQuotient.lean`:斉次イデアルによる商は次数付き環(Mathlib に未収録の一般的な構成)。
* `BlowupScheme.lean`:`Scheme` としてのブローアップ `blowupScheme k = Proj (k[x,y,t,u]/(xu-ty))`(`(t,u)` に重み 1)、構造射 `blowupMap`。`IsProper (blowupMap k)`(Mathlib の `Proj` の固有性から)と、`k[x,y] → B` の単射性 `xyToBlow_injective`。さらに `B₀ ≃+* k[x,y]`(`blowB0Equiv`)、`Spec B₀ ≅ Spec k[x,y]`(`blowBaseIso`)、ブローアップ射 `blowupToAffine : Proj B ⟶ Spec k[x,y]`(固有)。未着手:`Proj` の閉点と集合論的モデル `blowupSet` の対応。
