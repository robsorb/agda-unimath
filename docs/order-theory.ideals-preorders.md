# Ideals in preorders

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="order-theory.ideals-preorders.html" class="Module">order-theory.ideals-preorders</a> <a id="69" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="125" class="Keyword">open</a> <a id="130" class="Keyword">import</a> <a id="137" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="172" class="Keyword">open</a> <a id="177" class="Keyword">import</a> <a id="184" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="216" class="Keyword">open</a> <a id="221" class="Keyword">import</a> <a id="228" href="foundation.inhabited-types.html" class="Module">foundation.inhabited-types</a>
<a id="255" class="Keyword">open</a> <a id="260" class="Keyword">import</a> <a id="267" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="order-theory.lower-types-preorders.html" class="Module">order-theory.lower-types-preorders</a>
<a id="342" class="Keyword">open</a> <a id="347" class="Keyword">import</a> <a id="354" href="order-theory.preorders.html" class="Module">order-theory.preorders</a>
</pre>
</details>

## Idea

**Ideals** in preorders are inhabited lower types `L` that contain an upper
bound for every pair of elements in `L`.

## Definition

<pre class="Agda"><a id="544" class="Keyword">module</a> <a id="551" href="order-theory.ideals-preorders.html#551" class="Module">_</a>
  <a id="555" class="Symbol">{</a><a id="556" href="order-theory.ideals-preorders.html#556" class="Bound">l1</a> <a id="559" href="order-theory.ideals-preorders.html#559" class="Bound">l2</a> <a id="562" class="Symbol">:</a> <a id="564" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="569" class="Symbol">}</a> <a id="571" class="Symbol">(</a><a id="572" href="order-theory.ideals-preorders.html#572" class="Bound">P</a> <a id="574" class="Symbol">:</a> <a id="576" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="585" href="order-theory.ideals-preorders.html#556" class="Bound">l1</a> <a id="588" href="order-theory.ideals-preorders.html#559" class="Bound">l2</a><a id="590" class="Symbol">)</a>
  <a id="594" class="Keyword">where</a>

  <a id="603" href="order-theory.ideals-preorders.html#603" class="Function">is-ideal-lower-type-Preorder</a> <a id="632" class="Symbol">:</a>
    <a id="638" class="Symbol">{</a><a id="639" href="order-theory.ideals-preorders.html#639" class="Bound">l3</a> <a id="642" class="Symbol">:</a> <a id="644" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="649" class="Symbol">}</a> <a id="651" class="Symbol">(</a><a id="652" href="order-theory.ideals-preorders.html#652" class="Bound">L</a> <a id="654" class="Symbol">:</a> <a id="656" href="order-theory.lower-types-preorders.html#716" class="Function">lower-type-Preorder</a> <a id="676" href="order-theory.ideals-preorders.html#639" class="Bound">l3</a> <a id="679" href="order-theory.ideals-preorders.html#572" class="Bound">P</a><a id="680" class="Symbol">)</a> <a id="682" class="Symbol">→</a> <a id="684" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="687" class="Symbol">(</a><a id="688" href="order-theory.ideals-preorders.html#556" class="Bound">l1</a> <a id="691" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="693" href="order-theory.ideals-preorders.html#559" class="Bound">l2</a> <a id="696" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="698" href="order-theory.ideals-preorders.html#639" class="Bound">l3</a><a id="700" class="Symbol">)</a>
  <a id="704" href="order-theory.ideals-preorders.html#603" class="Function">is-ideal-lower-type-Preorder</a> <a id="733" href="order-theory.ideals-preorders.html#733" class="Bound">L</a> <a id="735" class="Symbol">=</a>
    <a id="741" class="Symbol">(</a> <a id="743" href="foundation.inhabited-types.html#1345" class="Function">is-inhabited</a> <a id="756" class="Symbol">(</a><a id="757" href="order-theory.lower-types-preorders.html#1108" class="Function">type-lower-type-Preorder</a> <a id="782" href="order-theory.ideals-preorders.html#572" class="Bound">P</a> <a id="784" href="order-theory.ideals-preorders.html#733" class="Bound">L</a><a id="785" class="Symbol">))</a> <a id="788" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a>
    <a id="794" class="Symbol">(</a> <a id="796" class="Symbol">(</a><a id="797" href="order-theory.ideals-preorders.html#797" class="Bound">x</a> <a id="799" href="order-theory.ideals-preorders.html#799" class="Bound">y</a> <a id="801" class="Symbol">:</a> <a id="803" href="order-theory.lower-types-preorders.html#1108" class="Function">type-lower-type-Preorder</a> <a id="828" href="order-theory.ideals-preorders.html#572" class="Bound">P</a> <a id="830" href="order-theory.ideals-preorders.html#733" class="Bound">L</a><a id="831" class="Symbol">)</a> <a id="833" class="Symbol">→</a>
      <a id="841" href="foundation.inhabited-types.html#1345" class="Function">is-inhabited</a>
        <a id="862" class="Symbol">(</a> <a id="864" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="866" class="Symbol">(</a> <a id="868" href="order-theory.lower-types-preorders.html#1108" class="Function">type-lower-type-Preorder</a> <a id="893" href="order-theory.ideals-preorders.html#572" class="Bound">P</a> <a id="895" href="order-theory.ideals-preorders.html#733" class="Bound">L</a><a id="896" class="Symbol">)</a>
            <a id="910" class="Symbol">(</a> <a id="912" class="Symbol">λ</a> <a id="914" href="order-theory.ideals-preorders.html#914" class="Bound">z</a> <a id="916" class="Symbol">→</a>
              <a id="932" class="Symbol">(</a> <a id="934" href="order-theory.lower-types-preorders.html#1341" class="Function">leq-lower-type-Preorder</a> <a id="958" href="order-theory.ideals-preorders.html#572" class="Bound">P</a> <a id="960" href="order-theory.ideals-preorders.html#733" class="Bound">L</a> <a id="962" href="order-theory.ideals-preorders.html#797" class="Bound">x</a> <a id="964" href="order-theory.ideals-preorders.html#914" class="Bound">z</a><a id="965" class="Symbol">)</a> <a id="967" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a>
              <a id="983" class="Symbol">(</a> <a id="985" href="order-theory.lower-types-preorders.html#1341" class="Function">leq-lower-type-Preorder</a> <a id="1009" href="order-theory.ideals-preorders.html#572" class="Bound">P</a> <a id="1011" href="order-theory.ideals-preorders.html#733" class="Bound">L</a> <a id="1013" href="order-theory.ideals-preorders.html#799" class="Bound">y</a> <a id="1015" href="order-theory.ideals-preorders.html#914" class="Bound">z</a><a id="1016" class="Symbol">))))</a>
</pre>