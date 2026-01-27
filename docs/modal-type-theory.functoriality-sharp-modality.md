# Functoriality of the sharp modality

<pre class="Agda"><a id="48" class="Symbol">{-#</a> <a id="52" class="Keyword">OPTIONS</a> <a id="60" class="Pragma">--cohesion</a> <a id="71" class="Pragma">--flat-split</a> <a id="84" class="Symbol">#-}</a>

<a id="89" class="Keyword">module</a> <a id="96" href="modal-type-theory.functoriality-sharp-modality.html" class="Module">modal-type-theory.functoriality-sharp-modality</a> <a id="143" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="302" class="Keyword">open</a> <a id="307" class="Keyword">import</a> <a id="314" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="340" class="Keyword">open</a> <a id="345" class="Keyword">import</a> <a id="352" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="374" class="Keyword">open</a> <a id="379" class="Keyword">import</a> <a id="386" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="412" class="Keyword">open</a> <a id="417" class="Keyword">import</a> <a id="424" href="foundation.locally-small-types.html" class="Module">foundation.locally-small-types</a>
<a id="455" class="Keyword">open</a> <a id="460" class="Keyword">import</a> <a id="467" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="495" class="Keyword">open</a> <a id="500" class="Keyword">import</a> <a id="507" href="modal-type-theory.sharp-modality.html" class="Module">modal-type-theory.sharp-modality</a>

<a id="541" class="Keyword">open</a> <a id="546" class="Keyword">import</a> <a id="553" href="orthogonal-factorization-systems.locally-small-modal-operators.html" class="Module">orthogonal-factorization-systems.locally-small-modal-operators</a>
<a id="616" class="Keyword">open</a> <a id="621" class="Keyword">import</a> <a id="628" href="orthogonal-factorization-systems.modal-induction.html" class="Module">orthogonal-factorization-systems.modal-induction</a>
<a id="677" class="Keyword">open</a> <a id="682" class="Keyword">import</a> <a id="689" href="orthogonal-factorization-systems.modal-subuniverse-induction.html" class="Module">orthogonal-factorization-systems.modal-subuniverse-induction</a>
</pre>
</details>

## Idea

The [sharp modality](modal-type-theory.sharp-modality.md) `♯` is functorial.
Given a map `f : A → B`, there is a
[unique](foundation-core.contractible-types.md) map `♯ f : ♯ A → ♯ B` that fits
into a [natural square](foundation-core.commuting-squares-of-maps.md)

```text
         f
    X ------> Y
    |         |
    |         |
    v         v
   ♯ X ----> ♯ Y.
        ♯ f
```

This construction preserves [composition](foundation-core.function-types.md),
[identifications](foundation-core.identity-types.md),
[homotopies](foundation-core.homotopies.md), and
[equivalences](foundation-core.equivalences.md).

## Definitions

### The sharp modality's action on maps

<pre class="Agda"><a id="action-sharp-map"></a><a id="1454" href="modal-type-theory.functoriality-sharp-modality.html#1454" class="Function">action-sharp-map</a> <a id="1471" class="Symbol">:</a>
  <a id="1475" class="Symbol">{</a><a id="1476" href="modal-type-theory.functoriality-sharp-modality.html#1476" class="Bound">l1</a> <a id="1479" href="modal-type-theory.functoriality-sharp-modality.html#1479" class="Bound">l2</a> <a id="1482" class="Symbol">:</a> <a id="1484" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1489" class="Symbol">}</a> <a id="1491" class="Symbol">{</a><a id="1492" href="modal-type-theory.functoriality-sharp-modality.html#1492" class="Bound">A</a> <a id="1494" class="Symbol">:</a> <a id="1496" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1499" href="modal-type-theory.functoriality-sharp-modality.html#1476" class="Bound">l1</a><a id="1501" class="Symbol">}</a> <a id="1503" class="Symbol">{</a><a id="1504" href="modal-type-theory.functoriality-sharp-modality.html#1504" class="Bound">B</a> <a id="1506" class="Symbol">:</a> <a id="1508" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1511" href="modal-type-theory.functoriality-sharp-modality.html#1479" class="Bound">l2</a><a id="1513" class="Symbol">}</a> <a id="1515" class="Symbol">→</a> <a id="1517" class="Symbol">(</a><a id="1518" href="modal-type-theory.functoriality-sharp-modality.html#1492" class="Bound">A</a> <a id="1520" class="Symbol">→</a> <a id="1522" href="modal-type-theory.functoriality-sharp-modality.html#1504" class="Bound">B</a><a id="1523" class="Symbol">)</a> <a id="1525" class="Symbol">→</a> <a id="1527" class="Symbol">(</a><a id="1528" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="1530" href="modal-type-theory.functoriality-sharp-modality.html#1492" class="Bound">A</a> <a id="1532" class="Symbol">→</a> <a id="1534" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="1536" href="modal-type-theory.functoriality-sharp-modality.html#1504" class="Bound">B</a><a id="1537" class="Symbol">)</a>
<a id="1539" href="modal-type-theory.functoriality-sharp-modality.html#1454" class="Function">action-sharp-map</a> <a id="1556" href="modal-type-theory.functoriality-sharp-modality.html#1556" class="Bound">f</a> <a id="1558" class="Symbol">=</a> <a id="1560" href="modal-type-theory.sharp-modality.html#10109" class="Function">rec-sharp</a> <a id="1570" class="Symbol">(</a><a id="1571" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a> <a id="1582" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1584" href="modal-type-theory.functoriality-sharp-modality.html#1556" class="Bound">f</a><a id="1585" class="Symbol">)</a>
</pre>