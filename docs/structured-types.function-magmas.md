# Function magmas

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="structured-types.function-magmas.html" class="Module">structured-types.function-magmas</a> <a id="68" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="124" class="Keyword">open</a> <a id="129" class="Keyword">import</a> <a id="136" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="208" class="Keyword">open</a> <a id="213" class="Keyword">import</a> <a id="220" href="structured-types.magmas.html" class="Module">structured-types.magmas</a>
</pre>
</details>

## Idea

Given a magma `M` and a type `X`, the function magma `M^X` consists of functions
from `X` into the underlying type of `M`. The operation on `M^X` is defined
pointwise.

## Definition

<pre class="Agda"><a id="462" class="Keyword">module</a> <a id="469" href="structured-types.function-magmas.html#469" class="Module">_</a>
  <a id="473" class="Symbol">{</a><a id="474" href="structured-types.function-magmas.html#474" class="Bound">l1</a> <a id="477" href="structured-types.function-magmas.html#477" class="Bound">l2</a> <a id="480" class="Symbol">:</a> <a id="482" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="487" class="Symbol">}</a> <a id="489" class="Symbol">(</a><a id="490" href="structured-types.function-magmas.html#490" class="Bound">M</a> <a id="492" class="Symbol">:</a> <a id="494" href="structured-types.magmas.html#477" class="Function">Magma</a> <a id="500" href="structured-types.function-magmas.html#474" class="Bound">l1</a><a id="502" class="Symbol">)</a> <a id="504" class="Symbol">(</a><a id="505" href="structured-types.function-magmas.html#505" class="Bound">X</a> <a id="507" class="Symbol">:</a> <a id="509" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="512" href="structured-types.function-magmas.html#477" class="Bound">l2</a><a id="514" class="Symbol">)</a>
  <a id="518" class="Keyword">where</a>

  <a id="527" href="structured-types.function-magmas.html#527" class="Function">type-function-Magma</a> <a id="547" class="Symbol">:</a> <a id="549" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="552" class="Symbol">(</a><a id="553" href="structured-types.function-magmas.html#474" class="Bound">l1</a> <a id="556" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="558" href="structured-types.function-magmas.html#477" class="Bound">l2</a><a id="560" class="Symbol">)</a>
  <a id="564" href="structured-types.function-magmas.html#527" class="Function">type-function-Magma</a> <a id="584" class="Symbol">=</a> <a id="586" href="structured-types.function-magmas.html#505" class="Bound">X</a> <a id="588" class="Symbol">→</a> <a id="590" href="structured-types.magmas.html#597" class="Function">type-Magma</a> <a id="601" href="structured-types.function-magmas.html#490" class="Bound">M</a>

  <a id="606" href="structured-types.function-magmas.html#606" class="Function">mul-function-Magma</a> <a id="625" class="Symbol">:</a>
    <a id="631" href="structured-types.function-magmas.html#527" class="Function">type-function-Magma</a> <a id="651" class="Symbol">→</a> <a id="653" href="structured-types.function-magmas.html#527" class="Function">type-function-Magma</a> <a id="673" class="Symbol">→</a> <a id="675" href="structured-types.function-magmas.html#527" class="Function">type-function-Magma</a>
  <a id="697" href="structured-types.function-magmas.html#606" class="Function">mul-function-Magma</a> <a id="716" href="structured-types.function-magmas.html#716" class="Bound">f</a> <a id="718" href="structured-types.function-magmas.html#718" class="Bound">g</a> <a id="720" href="structured-types.function-magmas.html#720" class="Bound">x</a> <a id="722" class="Symbol">=</a> <a id="724" href="structured-types.magmas.html#639" class="Function">mul-Magma</a> <a id="734" href="structured-types.function-magmas.html#490" class="Bound">M</a> <a id="736" class="Symbol">(</a><a id="737" href="structured-types.function-magmas.html#716" class="Bound">f</a> <a id="739" href="structured-types.function-magmas.html#720" class="Bound">x</a><a id="740" class="Symbol">)</a> <a id="742" class="Symbol">(</a><a id="743" href="structured-types.function-magmas.html#718" class="Bound">g</a> <a id="745" href="structured-types.function-magmas.html#720" class="Bound">x</a><a id="746" class="Symbol">)</a>

  <a id="751" href="structured-types.function-magmas.html#751" class="Function">function-Magma</a> <a id="766" class="Symbol">:</a> <a id="768" href="structured-types.magmas.html#477" class="Function">Magma</a> <a id="774" class="Symbol">(</a><a id="775" href="structured-types.function-magmas.html#474" class="Bound">l1</a> <a id="778" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="780" href="structured-types.function-magmas.html#477" class="Bound">l2</a><a id="782" class="Symbol">)</a>
  <a id="786" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="790" href="structured-types.function-magmas.html#751" class="Function">function-Magma</a> <a id="805" class="Symbol">=</a> <a id="807" href="structured-types.function-magmas.html#527" class="Function">type-function-Magma</a>
  <a id="829" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="833" href="structured-types.function-magmas.html#751" class="Function">function-Magma</a> <a id="848" class="Symbol">=</a> <a id="850" href="structured-types.function-magmas.html#606" class="Function">mul-function-Magma</a>
</pre>