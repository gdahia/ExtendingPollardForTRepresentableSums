# Pollard's theorem for $t$-representable sums

A Lean 4 formalization of D. J. Grynkiewicz,
[On extending Pollard's theorem for $t$-representable sums](https://doi.org/10.1007/s11856-010-0053-6),
Israel J. Math. 177 (2010), 413–439 ([arXiv:0803.2601](https://arxiv.org/abs/0803.2601)).

For finite subsets $A$, $B$ of an abelian group $G$, let $r_{A,B}(x)$ be the number of pairs
$(a, b) \in A \times B$ with $a + b = x$, and let $A +_i B = \{x : r_{A,B}(x) \ge i\}$ be the set of
$i$-representable sums (`representableSums i A B`). Pollard's theorem bounds
$\sum_{i=1}^t |A +_i B|$ from below in cyclic groups of prime order. The paper proves a Kneser-type
version in every abelian group.

## Results

In the statements below, $H$ is the stabilizer $\{x \in G : x + (A +_t B) = A +_t B\}$ of
$A +_t B$ and $\rho = |A' + H| - |A'| + |B' + H| - |B'|$ is the number of $H$-holes of $A'$ and $B'$
(`numHoles`).

**Theorem 1.1** (`ExtendingPollard.mul_card_add_mul_card_le_or_exists_add_eq_representableSums`).
Let $|A|, |B| \ge t \ge 1$. Then either
$$\sum_{i=1}^t |A +_i B| \ge t|A| + t|B| - 2t^2 + 1,$$
or there are $A' \subseteq A$ and $B' \subseteq B$ with
$l = |A \setminus A'| + |B \setminus B'| \le t - 1$, $A' +_t B' = A' + B' = A +_t B$, $H$ nontrivial,
and
$$\sum_{i=1}^t |A +_i B| \ge t|A| + t|B| - (t - l)(|H| - \rho) - tl \ge t|A| + t|B| - t|H|.$$

**Theorem 1.2** (`ExtendingPollard.mul_card_add_mul_card_le_or_exists_add_eq_representableSums_two`).
Let $|A|, |B| \ge 2$. Then either $|A + B| + |A +_2 B| \ge 2|A| + 2|B| - 4$, or there are
$A' \subseteq A$ and $B' \subseteq B$ with $l = |A \setminus A'| + |B \setminus B'| \le 1$,
$A' +_2 B' = A' + B' = A +_2 B$, $H$ nontrivial, and
$$|A + B| + |A +_2 B| \ge 2|A| + 2|B| - (2 - l)(|H| - \rho) - 2l \ge 2|A| + 2|B| - 2|H|.$$

**Corollary 1.3**
(`ExtendingPollard.mul_card_add_mul_card_le_or_exists_vadd_subset_representableSums_two`).
Let $|A|, |B| \ge 2$. Then either $|A + B| + |A +_2 B| \ge 2|A| + 2|B| - 4$, or $A +_2 B$ contains a
coset $x + K$ of a subgroup $K$ with $|K| \ge 3$.

**Remark ending Section 1**
(`ExtendingPollard.mul_card_add_mul_card_le_or_exists_add_eq_representableSums_two_mul`). Let
$|A|, |B| \ge t \ge 1$. Then either $\sum_{i=1}^t |A +_i B| \ge t|A| + t|B| - 2t^2 + 1$, or there
are $A' \subseteq A$ and $B' \subseteq B$ with $|A \setminus A'| + |B \setminus B'| \le t - 1$,
$$A' +_{2t} B' = A' + B' = A +_{2t} B = A +_t B \quad\text{and}\quad |H| \ge 2t + \rho.$$
For $t = 2$, `ExtendingPollard.mul_card_add_mul_card_le_or_exists_add_eq_representableSums_three`
states that either $|A + B| + |A +_2 B| \ge 2|A| + 2|B| - 4$, or there are such $A'$, $B'$ with
$A' +_3 B' = A' + B' = A +_3 B = A +_2 B$ and $|H| \ge 3 + \rho$.

**Lemma 2.1** (`ExtendingPollard.mul_min_le_sumCardRepresentableSums`). Let $k \le |B|$ and
$t \ge 1$. If $r_{A,-B}(x) \le k$ for every $x \notin T$, then
$$\sum_{i=1}^t |A +_i B| \ge t \min\left(\frac{|A||B|}{t + \sqrt{t(t-1)}},
\frac{|A|^2|B|}{|T|(|B| - k) + k|A|}\right) \ge \min\left(\frac{|A||B|}{2},
t \frac{|A|^2|B|}{|T|(|B| - k) + k|A|}\right).$$

**Lemma 2.2** (`ExtendingPollard.card_add_lt_card_add_insert`). Let $A$, $B$ be nonempty with
$|A + B| = |A| + |B| - 1$ and $A + B$ aperiodic. Then $|A + (B \cup \{b\})| > |A + B|$ for every
$b \notin B$.

[Solution.lean](Solution.lean) proves each statement of [Challenge.lean](Challenge.lean), which
uses the library names with a prime, by the corresponding library theorem.

| Declaration | Statement |
| --- | --- |
| `sumLowerBound_or_subsetSumsetEq` | The main dichotomy: `SumLowerBound t A B ∨ SubsetSumsetEq t A B` for $\lvert A\rvert, \lvert B\rvert \ge t \ge 1$. |
| `SumLowerBound` | $t\lvert A\rvert + t\lvert B\rvert \le \sum_{i=1}^t \lvert A +_i B\rvert + d_t$ with $d_t = 2t^2 - 1$, or $d_2 = 4$ (`deficit`). |
| `SubsetSumsetEq` | Conditions (7) and (8): $A +_t B = A' + B'$ for large subsets with $A' +_t B' = A' + B'$. |
| `SaturatedWitness` | Subsets as in (7) and (8) that are unions of the cosets they meet inside $A$ and $B$. |
| `SubsetSumsetEq.exists_saturatedWitness` | Step 1: a saturated witness with $\lvert H\rvert - \rho \ge t + 1$. |
| `InductionHypothesis` | The theorem for all smaller pairs, in the order used by the induction. |
| `sumLowerBound_or_subsetSumsetEq_of_erase` | Step 2: removing an element that loses at least $t$ representations. |
| `le_card_inter` | Step 3: the Dyson transform keeps at least $t$ elements. |
| `false_of_le_card_inter` | Step 4: the theorem for the Dyson transform $(A \cup B, A \cap B)$ gives a contradiction. |
| `le_addConvolution_of_card_add_le` | Proposition E(i): if $\lvert A + B\rvert + k \le \lvert A\rvert + \lvert B\rvert$, every sum has at least $k$ representations. |
| `card_add_sub_card_addStab_add_holes_le` | Kneser's theorem in the form $\lvert A + B\rvert \ge \lvert A\rvert + \lvert B\rvert - \lvert H\rvert + \rho$. |
| `Finset.add_kneser` | Kneser's theorem. |

## Files

| Files in `ExtendingPollardForTRepresentableSums/` | Contents |
| --- | --- |
| `RepresentableSums.lean` | The sets $A +_i B$ and the sum $\sum_{i=1}^t \lvert A +_i B\rvert$. |
| `Kneser/MulStab.lean`, `Kneser/Kneser.lean` | The stabilizer of a finset and Kneser's theorem. |
| `KneserConsequences.lean` | Consequences of Kneser's theorem, Proposition E(i) and Lemma 2.2. |
| `EnergyBound.lean` | Lemma 2.1, through the additive energy. |
| `SubsetSumset.lean` | The two alternatives of the theorem, holes, and Step 1. |
| `InductionHypothesis.lean` | The induction hypothesis, Step 2, the bound (33), and the choice of the Dyson transform. |
| `IntersectionLowerBound.lean` | Step 3. |
| `DysonTransform.lean` | Step 4. |
| `Induction.lean` | The induction proving the main dichotomy. |
| `MainTheorems.lean` | Theorems 1.1 and 1.2, Corollary 1.3 and the remark, in terms of the Mathlib stabilizer. |

[formalization.yaml](formalization.yaml) records the sources, the differences from them, the
scope, and the use of AI coding agents.

## Verification

`Challenge.lean` imports only Mathlib. It defines `representableSums` and `numHoles` and states
Theorems 1.1 and 1.2, Corollary 1.3, the remark ending Section 1 in two theorems, and Lemmas 2.1
and 2.2. `comparator.json` names these seven theorems and the two definitions, `Challenge` and
`Solution` as the modules to compare, and `propext`, `Classical.choice` and `Quot.sound` as the
permitted axioms.

## Build

The Lean and Mathlib versions are pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes the library, challenge, and solution. The `sorry` warnings from
`Challenge.lean` are expected.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
