# Strongly extensional maps

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="foundation.strongly-extensional-maps.html" class="Module">foundation.strongly-extensional-maps</a> <a id="82" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="138" class="Keyword">open</a> <a id="143" class="Keyword">import</a> <a id="150" href="foundation.apartness-relations.html" class="Module">foundation.apartness-relations</a>
<a id="181" class="Keyword">open</a> <a id="186" class="Keyword">import</a> <a id="193" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

Consider a function `f : A → B` between types equipped with apartness relations.
Then we say that `f` is **strongly extensional** if

```text
  f x # f y → x # y
```

## Definition

<pre class="Agda"><a id="strongly-extensional"></a><a id="436" href="foundation.strongly-extensional-maps.html#436" class="Function">strongly-extensional</a> <a id="457" class="Symbol">:</a>
  <a id="461" class="Symbol">{</a><a id="462" href="foundation.strongly-extensional-maps.html#462" class="Bound">l1</a> <a id="465" href="foundation.strongly-extensional-maps.html#465" class="Bound">l2</a> <a id="468" href="foundation.strongly-extensional-maps.html#468" class="Bound">l3</a> <a id="471" href="foundation.strongly-extensional-maps.html#471" class="Bound">l4</a> <a id="474" class="Symbol">:</a> <a id="476" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="481" class="Symbol">}</a> <a id="483" class="Symbol">(</a><a id="484" href="foundation.strongly-extensional-maps.html#484" class="Bound">A</a> <a id="486" class="Symbol">:</a> <a id="488" href="foundation.apartness-relations.html#2997" class="Function">Type-With-Apartness</a> <a id="508" href="foundation.strongly-extensional-maps.html#462" class="Bound">l1</a> <a id="511" href="foundation.strongly-extensional-maps.html#465" class="Bound">l2</a><a id="513" class="Symbol">)</a>
  <a id="517" class="Symbol">(</a><a id="518" href="foundation.strongly-extensional-maps.html#518" class="Bound">B</a> <a id="520" class="Symbol">:</a> <a id="522" href="foundation.apartness-relations.html#2997" class="Function">Type-With-Apartness</a> <a id="542" href="foundation.strongly-extensional-maps.html#468" class="Bound">l3</a> <a id="545" href="foundation.strongly-extensional-maps.html#471" class="Bound">l4</a><a id="547" class="Symbol">)</a> <a id="549" class="Symbol">→</a>
  <a id="553" class="Symbol">(</a><a id="554" href="foundation.apartness-relations.html#3197" class="Function">type-Type-With-Apartness</a> <a id="579" href="foundation.strongly-extensional-maps.html#484" class="Bound">A</a> <a id="581" class="Symbol">→</a> <a id="583" href="foundation.apartness-relations.html#3197" class="Function">type-Type-With-Apartness</a> <a id="608" href="foundation.strongly-extensional-maps.html#518" class="Bound">B</a><a id="609" class="Symbol">)</a> <a id="611" class="Symbol">→</a> <a id="613" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="616" class="Symbol">(</a><a id="617" href="foundation.strongly-extensional-maps.html#462" class="Bound">l1</a> <a id="620" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="622" href="foundation.strongly-extensional-maps.html#465" class="Bound">l2</a> <a id="625" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="627" href="foundation.strongly-extensional-maps.html#471" class="Bound">l4</a><a id="629" class="Symbol">)</a>
<a id="631" href="foundation.strongly-extensional-maps.html#436" class="Function">strongly-extensional</a> <a id="652" href="foundation.strongly-extensional-maps.html#652" class="Bound">A</a> <a id="654" href="foundation.strongly-extensional-maps.html#654" class="Bound">B</a> <a id="656" href="foundation.strongly-extensional-maps.html#656" class="Bound">f</a> <a id="658" class="Symbol">=</a>
  <a id="662" class="Symbol">(</a><a id="663" href="foundation.strongly-extensional-maps.html#663" class="Bound">x</a> <a id="665" href="foundation.strongly-extensional-maps.html#665" class="Bound">y</a> <a id="667" class="Symbol">:</a> <a id="669" href="foundation.apartness-relations.html#3197" class="Function">type-Type-With-Apartness</a> <a id="694" href="foundation.strongly-extensional-maps.html#652" class="Bound">A</a><a id="695" class="Symbol">)</a> <a id="697" class="Symbol">→</a>
  <a id="701" href="foundation.apartness-relations.html#3589" class="Function">apart-Type-With-Apartness</a> <a id="727" href="foundation.strongly-extensional-maps.html#654" class="Bound">B</a> <a id="729" class="Symbol">(</a><a id="730" href="foundation.strongly-extensional-maps.html#656" class="Bound">f</a> <a id="732" href="foundation.strongly-extensional-maps.html#663" class="Bound">x</a><a id="733" class="Symbol">)</a> <a id="735" class="Symbol">(</a><a id="736" href="foundation.strongly-extensional-maps.html#656" class="Bound">f</a> <a id="738" href="foundation.strongly-extensional-maps.html#665" class="Bound">y</a><a id="739" class="Symbol">)</a> <a id="741" class="Symbol">→</a> <a id="743" href="foundation.apartness-relations.html#3589" class="Function">apart-Type-With-Apartness</a> <a id="769" href="foundation.strongly-extensional-maps.html#652" class="Bound">A</a> <a id="771" href="foundation.strongly-extensional-maps.html#663" class="Bound">x</a> <a id="773" href="foundation.strongly-extensional-maps.html#665" class="Bound">y</a>
</pre>
## Properties

```text
is-strongly-extensional :
  {l1 l2 l3 l4 : Level} (A : Type-With-Apartness l1 l2)
  (B : Type-With-Apartness l3 l4) →
  (f : type-Type-With-Apartness A → type-Type-With-Apartness B) →
  strongly-extensional A B f
is-strongly-extensional A B f x y H = {!!}
```
