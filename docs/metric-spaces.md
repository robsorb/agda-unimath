# Metric spaces

## Idea

Metric spaces are types [structured](foundation.structure.md) with a concept of
distance on its elements.

Since we operate in a constructive setting, the concept of distance is captured
by considering upper bounds on the distance between points, rather than by a
distance function as in the classical approach. Thus, a metric space `A` is
defined by a family of _neighborhood_
[relations](foundation.binary-relations.md) on it indexed by the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
`ℚ⁺`,

```text
  N : ℚ⁺ → A → A → Prop l
```

that satisfies certain axioms. Constructing a proof of `N d x y` amounts to
saying that _`d` is an upper bound on the distance from `x` to `y`_.

The neighborhood relation on a metric space must satisfy the following axioms:

- **Reflexivity.** Every positive rational `d` is an upper bound on the distance
  from `x` to itself.
- **Symmetry.** If `d` is an upper bound on the distance from `x` to `y`, then
  `d` is an upper bound on the distance from `y` to `x`.
- **Triangularity.** If `d` is an upper bound on the distance from `x` to `y`,
  and `d'` is an upper bound on the distance from `y` to `z`, then `d + d'` is
  an upper bound on the distance from `x` to `z`.

Finally, we ask that our metric spaces are **extensional**, which amounts to the
property of **indistinguishability of identicals**

- If every positive rational `d` is an upper bound on the distance from `x` to
  `y`, then `x` and `y` are [equal](foundation-core.identity-types.md).

## Instances of metric spaces

{{#include tables/metric-spaces.md}}

## Modules in the metric spaces namespace

<pre class="Agda"><a id="1678" class="Keyword">module</a> <a id="1685" href="metric-spaces.html" class="Module">metric-spaces</a> <a id="1699" class="Keyword">where</a>

<a id="1706" class="Keyword">open</a> <a id="1711" class="Keyword">import</a> <a id="1718" href="metric-spaces.approximations-located-metric-spaces.html" class="Module">metric-spaces.approximations-located-metric-spaces</a> <a id="1769" class="Keyword">public</a>
<a id="1776" class="Keyword">open</a> <a id="1781" class="Keyword">import</a> <a id="1788" href="metric-spaces.approximations-metric-spaces.html" class="Module">metric-spaces.approximations-metric-spaces</a> <a id="1831" class="Keyword">public</a>
<a id="1838" class="Keyword">open</a> <a id="1843" class="Keyword">import</a> <a id="1850" href="metric-spaces.bounded-distance-decompositions-of-metric-spaces.html" class="Module">metric-spaces.bounded-distance-decompositions-of-metric-spaces</a> <a id="1913" class="Keyword">public</a>
<a id="1920" class="Keyword">open</a> <a id="1925" class="Keyword">import</a> <a id="1932" href="metric-spaces.cartesian-products-metric-spaces.html" class="Module">metric-spaces.cartesian-products-metric-spaces</a> <a id="1979" class="Keyword">public</a>
<a id="1986" class="Keyword">open</a> <a id="1991" class="Keyword">import</a> <a id="1998" href="metric-spaces.category-of-metric-spaces-and-isometries.html" class="Module">metric-spaces.category-of-metric-spaces-and-isometries</a> <a id="2053" class="Keyword">public</a>
<a id="2060" class="Keyword">open</a> <a id="2065" class="Keyword">import</a> <a id="2072" href="metric-spaces.category-of-metric-spaces-and-short-functions.html" class="Module">metric-spaces.category-of-metric-spaces-and-short-functions</a> <a id="2132" class="Keyword">public</a>
<a id="2139" class="Keyword">open</a> <a id="2144" class="Keyword">import</a> <a id="2151" href="metric-spaces.cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.cauchy-approximations-metric-spaces</a> <a id="2201" class="Keyword">public</a>
<a id="2208" class="Keyword">open</a> <a id="2213" class="Keyword">import</a> <a id="2220" href="metric-spaces.cauchy-approximations-pseudometric-spaces.html" class="Module">metric-spaces.cauchy-approximations-pseudometric-spaces</a> <a id="2276" class="Keyword">public</a>
<a id="2283" class="Keyword">open</a> <a id="2288" class="Keyword">import</a> <a id="2295" href="metric-spaces.cauchy-sequences-complete-metric-spaces.html" class="Module">metric-spaces.cauchy-sequences-complete-metric-spaces</a> <a id="2349" class="Keyword">public</a>
<a id="2356" class="Keyword">open</a> <a id="2361" class="Keyword">import</a> <a id="2368" href="metric-spaces.cauchy-sequences-metric-spaces.html" class="Module">metric-spaces.cauchy-sequences-metric-spaces</a> <a id="2413" class="Keyword">public</a>
<a id="2420" class="Keyword">open</a> <a id="2425" class="Keyword">import</a> <a id="2432" href="metric-spaces.closed-subsets-located-metric-spaces.html" class="Module">metric-spaces.closed-subsets-located-metric-spaces</a> <a id="2483" class="Keyword">public</a>
<a id="2490" class="Keyword">open</a> <a id="2495" class="Keyword">import</a> <a id="2502" href="metric-spaces.closed-subsets-metric-spaces.html" class="Module">metric-spaces.closed-subsets-metric-spaces</a> <a id="2545" class="Keyword">public</a>
<a id="2552" class="Keyword">open</a> <a id="2557" class="Keyword">import</a> <a id="2564" href="metric-spaces.closure-subsets-metric-spaces.html" class="Module">metric-spaces.closure-subsets-metric-spaces</a> <a id="2608" class="Keyword">public</a>
<a id="2615" class="Keyword">open</a> <a id="2620" class="Keyword">import</a> <a id="2627" href="metric-spaces.compact-metric-spaces.html" class="Module">metric-spaces.compact-metric-spaces</a> <a id="2663" class="Keyword">public</a>
<a id="2670" class="Keyword">open</a> <a id="2675" class="Keyword">import</a> <a id="2682" href="metric-spaces.complete-metric-spaces.html" class="Module">metric-spaces.complete-metric-spaces</a> <a id="2719" class="Keyword">public</a>
<a id="2726" class="Keyword">open</a> <a id="2731" class="Keyword">import</a> <a id="2738" href="metric-spaces.continuous-functions-metric-spaces.html" class="Module">metric-spaces.continuous-functions-metric-spaces</a> <a id="2787" class="Keyword">public</a>
<a id="2794" class="Keyword">open</a> <a id="2799" class="Keyword">import</a> <a id="2806" href="metric-spaces.convergent-cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.convergent-cauchy-approximations-metric-spaces</a> <a id="2867" class="Keyword">public</a>
<a id="2874" class="Keyword">open</a> <a id="2879" class="Keyword">import</a> <a id="2886" href="metric-spaces.convergent-sequences-metric-spaces.html" class="Module">metric-spaces.convergent-sequences-metric-spaces</a> <a id="2935" class="Keyword">public</a>
<a id="2942" class="Keyword">open</a> <a id="2947" class="Keyword">import</a> <a id="2954" href="metric-spaces.dense-subsets-metric-spaces.html" class="Module">metric-spaces.dense-subsets-metric-spaces</a> <a id="2996" class="Keyword">public</a>
<a id="3003" class="Keyword">open</a> <a id="3008" class="Keyword">import</a> <a id="3015" href="metric-spaces.dependent-products-metric-spaces.html" class="Module">metric-spaces.dependent-products-metric-spaces</a> <a id="3062" class="Keyword">public</a>
<a id="3069" class="Keyword">open</a> <a id="3074" class="Keyword">import</a> <a id="3081" href="metric-spaces.discrete-metric-spaces.html" class="Module">metric-spaces.discrete-metric-spaces</a> <a id="3118" class="Keyword">public</a>
<a id="3125" class="Keyword">open</a> <a id="3130" class="Keyword">import</a> <a id="3137" href="metric-spaces.elements-at-bounded-distance-metric-spaces.html" class="Module">metric-spaces.elements-at-bounded-distance-metric-spaces</a> <a id="3194" class="Keyword">public</a>
<a id="3201" class="Keyword">open</a> <a id="3206" class="Keyword">import</a> <a id="3213" href="metric-spaces.equality-of-metric-spaces.html" class="Module">metric-spaces.equality-of-metric-spaces</a> <a id="3253" class="Keyword">public</a>
<a id="3260" class="Keyword">open</a> <a id="3265" class="Keyword">import</a> <a id="3272" href="metric-spaces.equality-of-pseudometric-spaces.html" class="Module">metric-spaces.equality-of-pseudometric-spaces</a> <a id="3318" class="Keyword">public</a>
<a id="3325" class="Keyword">open</a> <a id="3330" class="Keyword">import</a> <a id="3337" href="metric-spaces.extensionality-pseudometric-spaces.html" class="Module">metric-spaces.extensionality-pseudometric-spaces</a> <a id="3386" class="Keyword">public</a>
<a id="3393" class="Keyword">open</a> <a id="3398" class="Keyword">import</a> <a id="3405" href="metric-spaces.functions-metric-spaces.html" class="Module">metric-spaces.functions-metric-spaces</a> <a id="3443" class="Keyword">public</a>
<a id="3450" class="Keyword">open</a> <a id="3455" class="Keyword">import</a> <a id="3462" href="metric-spaces.functions-pseudometric-spaces.html" class="Module">metric-spaces.functions-pseudometric-spaces</a> <a id="3506" class="Keyword">public</a>
<a id="3513" class="Keyword">open</a> <a id="3518" class="Keyword">import</a> <a id="3525" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html" class="Module">metric-spaces.functor-category-set-functions-isometry-metric-spaces</a> <a id="3593" class="Keyword">public</a>
<a id="3600" class="Keyword">open</a> <a id="3605" class="Keyword">import</a> <a id="3612" href="metric-spaces.functor-category-short-isometry-metric-spaces.html" class="Module">metric-spaces.functor-category-short-isometry-metric-spaces</a> <a id="3672" class="Keyword">public</a>
<a id="3679" class="Keyword">open</a> <a id="3684" class="Keyword">import</a> <a id="3691" href="metric-spaces.images-isometries-metric-spaces.html" class="Module">metric-spaces.images-isometries-metric-spaces</a> <a id="3737" class="Keyword">public</a>
<a id="3744" class="Keyword">open</a> <a id="3749" class="Keyword">import</a> <a id="3756" href="metric-spaces.images-metric-spaces.html" class="Module">metric-spaces.images-metric-spaces</a> <a id="3791" class="Keyword">public</a>
<a id="3798" class="Keyword">open</a> <a id="3803" class="Keyword">import</a> <a id="3810" href="metric-spaces.images-short-functions-metric-spaces.html" class="Module">metric-spaces.images-short-functions-metric-spaces</a> <a id="3861" class="Keyword">public</a>
<a id="3868" class="Keyword">open</a> <a id="3873" class="Keyword">import</a> <a id="3880" href="metric-spaces.images-uniformly-continuous-functions-metric-spaces.html" class="Module">metric-spaces.images-uniformly-continuous-functions-metric-spaces</a> <a id="3946" class="Keyword">public</a>
<a id="3953" class="Keyword">open</a> <a id="3958" class="Keyword">import</a> <a id="3965" href="metric-spaces.indexed-sums-metric-spaces.html" class="Module">metric-spaces.indexed-sums-metric-spaces</a> <a id="4006" class="Keyword">public</a>
<a id="4013" class="Keyword">open</a> <a id="4018" class="Keyword">import</a> <a id="4025" href="metric-spaces.inhabited-totally-bounded-subspaces-metric-spaces.html" class="Module">metric-spaces.inhabited-totally-bounded-subspaces-metric-spaces</a> <a id="4089" class="Keyword">public</a>
<a id="4096" class="Keyword">open</a> <a id="4101" class="Keyword">import</a> <a id="4108" href="metric-spaces.interior-subsets-metric-spaces.html" class="Module">metric-spaces.interior-subsets-metric-spaces</a> <a id="4153" class="Keyword">public</a>
<a id="4160" class="Keyword">open</a> <a id="4165" class="Keyword">import</a> <a id="4172" href="metric-spaces.isometries-metric-spaces.html" class="Module">metric-spaces.isometries-metric-spaces</a> <a id="4211" class="Keyword">public</a>
<a id="4218" class="Keyword">open</a> <a id="4223" class="Keyword">import</a> <a id="4230" href="metric-spaces.isometries-pseudometric-spaces.html" class="Module">metric-spaces.isometries-pseudometric-spaces</a> <a id="4275" class="Keyword">public</a>
<a id="4282" class="Keyword">open</a> <a id="4287" class="Keyword">import</a> <a id="4294" href="metric-spaces.limits-of-cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.limits-of-cauchy-approximations-metric-spaces</a> <a id="4354" class="Keyword">public</a>
<a id="4361" class="Keyword">open</a> <a id="4366" class="Keyword">import</a> <a id="4373" href="metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces.html" class="Module">metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces</a> <a id="4439" class="Keyword">public</a>
<a id="4446" class="Keyword">open</a> <a id="4451" class="Keyword">import</a> <a id="4458" href="metric-spaces.limits-of-functions-metric-spaces.html" class="Module">metric-spaces.limits-of-functions-metric-spaces</a> <a id="4506" class="Keyword">public</a>
<a id="4513" class="Keyword">open</a> <a id="4518" class="Keyword">import</a> <a id="4525" href="metric-spaces.limits-of-sequences-metric-spaces.html" class="Module">metric-spaces.limits-of-sequences-metric-spaces</a> <a id="4573" class="Keyword">public</a>
<a id="4580" class="Keyword">open</a> <a id="4585" class="Keyword">import</a> <a id="4592" href="metric-spaces.lipschitz-functions-metric-spaces.html" class="Module">metric-spaces.lipschitz-functions-metric-spaces</a> <a id="4640" class="Keyword">public</a>
<a id="4647" class="Keyword">open</a> <a id="4652" class="Keyword">import</a> <a id="4659" href="metric-spaces.locally-constant-functions-metric-spaces.html" class="Module">metric-spaces.locally-constant-functions-metric-spaces</a> <a id="4714" class="Keyword">public</a>
<a id="4721" class="Keyword">open</a> <a id="4726" class="Keyword">import</a> <a id="4733" href="metric-spaces.located-metric-spaces.html" class="Module">metric-spaces.located-metric-spaces</a> <a id="4769" class="Keyword">public</a>
<a id="4776" class="Keyword">open</a> <a id="4781" class="Keyword">import</a> <a id="4788" href="metric-spaces.metric-space-of-cauchy-approximations-complete-metric-spaces.html" class="Module">metric-spaces.metric-space-of-cauchy-approximations-complete-metric-spaces</a> <a id="4863" class="Keyword">public</a>
<a id="4870" class="Keyword">open</a> <a id="4875" class="Keyword">import</a> <a id="4882" href="metric-spaces.metric-space-of-cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.metric-space-of-cauchy-approximations-metric-spaces</a> <a id="4948" class="Keyword">public</a>
<a id="4955" class="Keyword">open</a> <a id="4960" class="Keyword">import</a> <a id="4967" href="metric-spaces.metric-space-of-convergent-cauchy-approximations-metric-spaces.html" class="Module">metric-spaces.metric-space-of-convergent-cauchy-approximations-metric-spaces</a> <a id="5044" class="Keyword">public</a>
<a id="5051" class="Keyword">open</a> <a id="5056" class="Keyword">import</a> <a id="5063" href="metric-spaces.metric-space-of-convergent-sequences-metric-spaces.html" class="Module">metric-spaces.metric-space-of-convergent-sequences-metric-spaces</a> <a id="5128" class="Keyword">public</a>
<a id="5135" class="Keyword">open</a> <a id="5140" class="Keyword">import</a> <a id="5147" href="metric-spaces.metric-space-of-functions-metric-spaces.html" class="Module">metric-spaces.metric-space-of-functions-metric-spaces</a> <a id="5201" class="Keyword">public</a>
<a id="5208" class="Keyword">open</a> <a id="5213" class="Keyword">import</a> <a id="5220" href="metric-spaces.metric-space-of-isometries-metric-spaces.html" class="Module">metric-spaces.metric-space-of-isometries-metric-spaces</a> <a id="5275" class="Keyword">public</a>
<a id="5282" class="Keyword">open</a> <a id="5287" class="Keyword">import</a> <a id="5294" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html" class="Module">metric-spaces.metric-space-of-lipschitz-functions-metric-spaces</a> <a id="5358" class="Keyword">public</a>
<a id="5365" class="Keyword">open</a> <a id="5370" class="Keyword">import</a> <a id="5377" href="metric-spaces.metric-space-of-rational-numbers.html" class="Module">metric-spaces.metric-space-of-rational-numbers</a> <a id="5424" class="Keyword">public</a>
<a id="5431" class="Keyword">open</a> <a id="5436" class="Keyword">import</a> <a id="5443" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html" class="Module">metric-spaces.metric-space-of-short-functions-metric-spaces</a> <a id="5503" class="Keyword">public</a>
<a id="5510" class="Keyword">open</a> <a id="5515" class="Keyword">import</a> <a id="5522" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a> <a id="5550" class="Keyword">public</a>
<a id="5557" class="Keyword">open</a> <a id="5562" class="Keyword">import</a> <a id="5569" href="metric-spaces.metrics.html" class="Module">metric-spaces.metrics</a> <a id="5591" class="Keyword">public</a>
<a id="5598" class="Keyword">open</a> <a id="5603" class="Keyword">import</a> <a id="5610" href="metric-spaces.metrics-of-metric-spaces.html" class="Module">metric-spaces.metrics-of-metric-spaces</a> <a id="5649" class="Keyword">public</a>
<a id="5656" class="Keyword">open</a> <a id="5661" class="Keyword">import</a> <a id="5668" href="metric-spaces.metrics-of-metric-spaces-are-uniformly-continuous.html" class="Module">metric-spaces.metrics-of-metric-spaces-are-uniformly-continuous</a> <a id="5732" class="Keyword">public</a>
<a id="5739" class="Keyword">open</a> <a id="5744" class="Keyword">import</a> <a id="5751" href="metric-spaces.monotonic-rational-neighborhood-relations.html" class="Module">metric-spaces.monotonic-rational-neighborhood-relations</a> <a id="5807" class="Keyword">public</a>
<a id="5814" class="Keyword">open</a> <a id="5819" class="Keyword">import</a> <a id="5826" href="metric-spaces.nets-located-metric-spaces.html" class="Module">metric-spaces.nets-located-metric-spaces</a> <a id="5867" class="Keyword">public</a>
<a id="5874" class="Keyword">open</a> <a id="5879" class="Keyword">import</a> <a id="5886" href="metric-spaces.nets-metric-spaces.html" class="Module">metric-spaces.nets-metric-spaces</a> <a id="5919" class="Keyword">public</a>
<a id="5926" class="Keyword">open</a> <a id="5931" class="Keyword">import</a> <a id="5938" href="metric-spaces.open-subsets-located-metric-spaces.html" class="Module">metric-spaces.open-subsets-located-metric-spaces</a> <a id="5987" class="Keyword">public</a>
<a id="5994" class="Keyword">open</a> <a id="5999" class="Keyword">import</a> <a id="6006" href="metric-spaces.open-subsets-metric-spaces.html" class="Module">metric-spaces.open-subsets-metric-spaces</a> <a id="6047" class="Keyword">public</a>
<a id="6054" class="Keyword">open</a> <a id="6059" class="Keyword">import</a> <a id="6066" href="metric-spaces.poset-of-rational-neighborhood-relations.html" class="Module">metric-spaces.poset-of-rational-neighborhood-relations</a> <a id="6121" class="Keyword">public</a>
<a id="6128" class="Keyword">open</a> <a id="6133" class="Keyword">import</a> <a id="6140" href="metric-spaces.precategory-of-metric-spaces-and-functions.html" class="Module">metric-spaces.precategory-of-metric-spaces-and-functions</a> <a id="6197" class="Keyword">public</a>
<a id="6204" class="Keyword">open</a> <a id="6209" class="Keyword">import</a> <a id="6216" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html" class="Module">metric-spaces.precategory-of-metric-spaces-and-isometries</a> <a id="6274" class="Keyword">public</a>
<a id="6281" class="Keyword">open</a> <a id="6286" class="Keyword">import</a> <a id="6293" href="metric-spaces.precategory-of-metric-spaces-and-short-functions.html" class="Module">metric-spaces.precategory-of-metric-spaces-and-short-functions</a> <a id="6356" class="Keyword">public</a>
<a id="6363" class="Keyword">open</a> <a id="6368" class="Keyword">import</a> <a id="6375" href="metric-spaces.preimages-rational-neighborhood-relations.html" class="Module">metric-spaces.preimages-rational-neighborhood-relations</a> <a id="6431" class="Keyword">public</a>
<a id="6438" class="Keyword">open</a> <a id="6443" class="Keyword">import</a> <a id="6450" href="metric-spaces.pseudometric-spaces.html" class="Module">metric-spaces.pseudometric-spaces</a> <a id="6484" class="Keyword">public</a>
<a id="6491" class="Keyword">open</a> <a id="6496" class="Keyword">import</a> <a id="6503" href="metric-spaces.rational-approximations-of-zero.html" class="Module">metric-spaces.rational-approximations-of-zero</a> <a id="6549" class="Keyword">public</a>
<a id="6556" class="Keyword">open</a> <a id="6561" class="Keyword">import</a> <a id="6568" href="metric-spaces.rational-cauchy-approximations.html" class="Module">metric-spaces.rational-cauchy-approximations</a> <a id="6613" class="Keyword">public</a>
<a id="6620" class="Keyword">open</a> <a id="6625" class="Keyword">import</a> <a id="6632" href="metric-spaces.rational-neighborhood-relations.html" class="Module">metric-spaces.rational-neighborhood-relations</a> <a id="6678" class="Keyword">public</a>
<a id="6685" class="Keyword">open</a> <a id="6690" class="Keyword">import</a> <a id="6697" href="metric-spaces.rational-sequences-approximating-zero.html" class="Module">metric-spaces.rational-sequences-approximating-zero</a> <a id="6749" class="Keyword">public</a>
<a id="6756" class="Keyword">open</a> <a id="6761" class="Keyword">import</a> <a id="6768" href="metric-spaces.reflexive-rational-neighborhood-relations.html" class="Module">metric-spaces.reflexive-rational-neighborhood-relations</a> <a id="6824" class="Keyword">public</a>
<a id="6831" class="Keyword">open</a> <a id="6836" class="Keyword">import</a> <a id="6843" href="metric-spaces.saturated-rational-neighborhood-relations.html" class="Module">metric-spaces.saturated-rational-neighborhood-relations</a> <a id="6899" class="Keyword">public</a>
<a id="6906" class="Keyword">open</a> <a id="6911" class="Keyword">import</a> <a id="6918" href="metric-spaces.sequences-metric-spaces.html" class="Module">metric-spaces.sequences-metric-spaces</a> <a id="6956" class="Keyword">public</a>
<a id="6963" class="Keyword">open</a> <a id="6968" class="Keyword">import</a> <a id="6975" href="metric-spaces.short-functions-metric-spaces.html" class="Module">metric-spaces.short-functions-metric-spaces</a> <a id="7019" class="Keyword">public</a>
<a id="7026" class="Keyword">open</a> <a id="7031" class="Keyword">import</a> <a id="7038" href="metric-spaces.short-functions-pseudometric-spaces.html" class="Module">metric-spaces.short-functions-pseudometric-spaces</a> <a id="7088" class="Keyword">public</a>
<a id="7095" class="Keyword">open</a> <a id="7100" class="Keyword">import</a> <a id="7107" href="metric-spaces.similarity-of-elements-pseudometric-spaces.html" class="Module">metric-spaces.similarity-of-elements-pseudometric-spaces</a> <a id="7164" class="Keyword">public</a>
<a id="7171" class="Keyword">open</a> <a id="7176" class="Keyword">import</a> <a id="7183" href="metric-spaces.subspaces-metric-spaces.html" class="Module">metric-spaces.subspaces-metric-spaces</a> <a id="7221" class="Keyword">public</a>
<a id="7228" class="Keyword">open</a> <a id="7233" class="Keyword">import</a> <a id="7240" href="metric-spaces.symmetric-rational-neighborhood-relations.html" class="Module">metric-spaces.symmetric-rational-neighborhood-relations</a> <a id="7296" class="Keyword">public</a>
<a id="7303" class="Keyword">open</a> <a id="7308" class="Keyword">import</a> <a id="7315" href="metric-spaces.totally-bounded-metric-spaces.html" class="Module">metric-spaces.totally-bounded-metric-spaces</a> <a id="7359" class="Keyword">public</a>
<a id="7366" class="Keyword">open</a> <a id="7371" class="Keyword">import</a> <a id="7378" href="metric-spaces.totally-bounded-subspaces-metric-spaces.html" class="Module">metric-spaces.totally-bounded-subspaces-metric-spaces</a> <a id="7432" class="Keyword">public</a>
<a id="7439" class="Keyword">open</a> <a id="7444" class="Keyword">import</a> <a id="7451" href="metric-spaces.triangular-rational-neighborhood-relations.html" class="Module">metric-spaces.triangular-rational-neighborhood-relations</a> <a id="7508" class="Keyword">public</a>
<a id="7515" class="Keyword">open</a> <a id="7520" class="Keyword">import</a> <a id="7527" href="metric-spaces.uniformly-continuous-functions-metric-spaces.html" class="Module">metric-spaces.uniformly-continuous-functions-metric-spaces</a> <a id="7586" class="Keyword">public</a>
</pre>
## References

Our setup for metric space theory closely follows {{#cite Booij20PhD}}.

{{#bibliography}} {{#reference Booij20PhD}}
