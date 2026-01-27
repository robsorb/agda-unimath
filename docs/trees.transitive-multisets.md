# Transitive multisets

<pre class="Agda"><a id="33" class="Keyword">module</a> <a id="40" href="trees.transitive-multisets.html" class="Module">trees.transitive-multisets</a> <a id="67" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="123" class="Keyword">open</a> <a id="128" class="Keyword">import</a> <a id="135" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="163" class="Keyword">open</a> <a id="168" class="Keyword">import</a> <a id="175" href="trees.multisets.html" class="Module">trees.multisets</a>
<a id="191" class="Keyword">open</a> <a id="196" class="Keyword">import</a> <a id="203" href="trees.submultisets.html" class="Module">trees.submultisets</a>
</pre>
</details>

## Idea

A multiset `x` is said to be **transitive** if `y ⊑-𝕍 x` for every `y ∈-𝕍 x`.
That is, `x` is transitive if for every `z ∈-𝕍 y ∈-𝕍 x` we have
`z ∈-𝕍 y ≃ z ∈-𝕍 x`.

Similarly, we say that `x` is **weakly transitive** if `y ⊆-𝕍 x` for every
`y ∈-𝕍 x`. That is, `x` is weakly transitive if for every `z ∈-𝕍 y ∈-𝕍 x` we
have `z ∈-𝕍 y ↪ z ∈-𝕍 x`.

## Definition

### Transitive multisets

<pre class="Agda"><a id="is-transitive-𝕍"></a><a id="640" href="trees.transitive-multisets.html#640" class="Function">is-transitive-𝕍</a> <a id="656" class="Symbol">:</a> <a id="658" class="Symbol">{</a><a id="659" href="trees.transitive-multisets.html#659" class="Bound">l</a> <a id="661" class="Symbol">:</a> <a id="663" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="668" class="Symbol">}</a> <a id="670" class="Symbol">→</a> <a id="672" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="674" href="trees.transitive-multisets.html#659" class="Bound">l</a> <a id="676" class="Symbol">→</a> <a id="678" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="681" class="Symbol">(</a><a id="682" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="687" href="trees.transitive-multisets.html#659" class="Bound">l</a><a id="688" class="Symbol">)</a>
<a id="690" href="trees.transitive-multisets.html#640" class="Function">is-transitive-𝕍</a> <a id="706" class="Symbol">{</a><a id="707" href="trees.transitive-multisets.html#707" class="Bound">l</a><a id="708" class="Symbol">}</a> <a id="710" href="trees.transitive-multisets.html#710" class="Bound">x</a> <a id="712" class="Symbol">=</a> <a id="714" class="Symbol">(</a><a id="715" href="trees.transitive-multisets.html#715" class="Bound">y</a> <a id="717" class="Symbol">:</a> <a id="719" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="721" href="trees.transitive-multisets.html#707" class="Bound">l</a><a id="722" class="Symbol">)</a> <a id="724" class="Symbol">→</a> <a id="726" href="trees.transitive-multisets.html#715" class="Bound">y</a> <a id="728" href="trees.multisets.html#875" class="Function Operator">∈-𝕍</a> <a id="732" href="trees.transitive-multisets.html#710" class="Bound">x</a> <a id="734" class="Symbol">→</a> <a id="736" href="trees.transitive-multisets.html#715" class="Bound">y</a> <a id="738" href="trees.submultisets.html#837" class="Function Operator">⊑-𝕍</a> <a id="742" href="trees.transitive-multisets.html#710" class="Bound">x</a>
</pre>
### Wealky transitive multisets

<pre class="Agda"><a id="is-weakly-transitive-𝕍"></a><a id="790" href="trees.transitive-multisets.html#790" class="Function">is-weakly-transitive-𝕍</a> <a id="813" class="Symbol">:</a> <a id="815" class="Symbol">{</a><a id="816" href="trees.transitive-multisets.html#816" class="Bound">l</a> <a id="818" class="Symbol">:</a> <a id="820" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="825" class="Symbol">}</a> <a id="827" class="Symbol">→</a> <a id="829" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="831" href="trees.transitive-multisets.html#816" class="Bound">l</a> <a id="833" class="Symbol">→</a> <a id="835" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="838" class="Symbol">(</a><a id="839" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="844" href="trees.transitive-multisets.html#816" class="Bound">l</a><a id="845" class="Symbol">)</a>
<a id="847" href="trees.transitive-multisets.html#790" class="Function">is-weakly-transitive-𝕍</a> <a id="870" class="Symbol">{</a><a id="871" href="trees.transitive-multisets.html#871" class="Bound">l</a><a id="872" class="Symbol">}</a> <a id="874" href="trees.transitive-multisets.html#874" class="Bound">x</a> <a id="876" class="Symbol">=</a> <a id="878" class="Symbol">(</a><a id="879" href="trees.transitive-multisets.html#879" class="Bound">y</a> <a id="881" class="Symbol">:</a> <a id="883" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="885" href="trees.transitive-multisets.html#871" class="Bound">l</a><a id="886" class="Symbol">)</a> <a id="888" class="Symbol">→</a> <a id="890" href="trees.transitive-multisets.html#879" class="Bound">y</a> <a id="892" href="trees.multisets.html#875" class="Function Operator">∈-𝕍</a> <a id="896" href="trees.transitive-multisets.html#874" class="Bound">x</a> <a id="898" class="Symbol">→</a> <a id="900" href="trees.transitive-multisets.html#879" class="Bound">y</a> <a id="902" href="trees.submultisets.html#585" class="Function Operator">⊆-𝕍</a> <a id="906" href="trees.transitive-multisets.html#874" class="Bound">x</a>
</pre>