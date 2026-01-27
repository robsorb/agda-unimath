# The precategory of commutative monoids

<pre class="Agda"><a id="51" class="Keyword">module</a> <a id="58" href="group-theory.precategory-of-commutative-monoids.html" class="Module">group-theory.precategory-of-commutative-monoids</a> <a id="106" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="162" class="Keyword">open</a> <a id="167" class="Keyword">import</a> <a id="174" href="category-theory.full-large-subprecategories.html" class="Module">category-theory.full-large-subprecategories</a>
<a id="218" class="Keyword">open</a> <a id="223" class="Keyword">import</a> <a id="230" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>
<a id="266" class="Keyword">open</a> <a id="271" class="Keyword">import</a> <a id="278" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="309" class="Keyword">open</a> <a id="314" class="Keyword">import</a> <a id="321" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="349" class="Keyword">open</a> <a id="354" class="Keyword">import</a> <a id="361" href="group-theory.commutative-monoids.html" class="Module">group-theory.commutative-monoids</a>
<a id="394" class="Keyword">open</a> <a id="399" class="Keyword">import</a> <a id="406" href="group-theory.precategory-of-monoids.html" class="Module">group-theory.precategory-of-monoids</a>
</pre>
</details>

## Idea

The **precategory of commutative monoids** consists of commutative monoids and
homomorphisms of monoids.

## Definitions

### The precategory of commutative monoids as a full subprecategory of monoids

<pre class="Agda"><a id="Commutative-Monoid-Full-Large-Subprecategory"></a><a id="678" href="group-theory.precategory-of-commutative-monoids.html#678" class="Function">Commutative-Monoid-Full-Large-Subprecategory</a> <a id="723" class="Symbol">:</a>
  <a id="727" href="category-theory.full-large-subprecategories.html#1584" class="Function">Full-Large-Subprecategory</a> <a id="753" class="Symbol">(λ</a> <a id="756" href="group-theory.precategory-of-commutative-monoids.html#756" class="Bound">l</a> <a id="758" class="Symbol">→</a> <a id="760" href="group-theory.precategory-of-commutative-monoids.html#756" class="Bound">l</a><a id="761" class="Symbol">)</a> <a id="763" href="group-theory.precategory-of-monoids.html#1630" class="Function">Monoid-Large-Precategory</a>
<a id="788" href="group-theory.precategory-of-commutative-monoids.html#678" class="Function">Commutative-Monoid-Full-Large-Subprecategory</a> <a id="833" class="Symbol">=</a> <a id="835" href="group-theory.commutative-monoids.html#1292" class="Function">is-commutative-prop-Monoid</a>
</pre>
### The large precategory of commutative monoids

<pre class="Agda"><a id="Commutative-Monoid-Large-Precategory"></a><a id="925" href="group-theory.precategory-of-commutative-monoids.html#925" class="Function">Commutative-Monoid-Large-Precategory</a> <a id="962" class="Symbol">:</a> <a id="964" href="category-theory.large-precategories.html#829" class="Record">Large-Precategory</a> <a id="982" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="987" class="Symbol">(</a><a id="988" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="991" class="Symbol">)</a>
<a id="993" href="group-theory.precategory-of-commutative-monoids.html#925" class="Function">Commutative-Monoid-Large-Precategory</a> <a id="1030" class="Symbol">=</a>
  <a id="1034" href="category-theory.full-large-subprecategories.html#5854" class="Function">large-precategory-Full-Large-Subprecategory</a>
    <a id="1082" class="Symbol">(</a> <a id="1084" href="group-theory.precategory-of-monoids.html#1630" class="Function">Monoid-Large-Precategory</a><a id="1108" class="Symbol">)</a>
    <a id="1114" class="Symbol">(</a> <a id="1116" href="group-theory.precategory-of-commutative-monoids.html#678" class="Function">Commutative-Monoid-Full-Large-Subprecategory</a><a id="1160" class="Symbol">)</a>
</pre>
### The precategory of small commutative monoids

<pre class="Agda"><a id="Commutative-Monoid-Precategory"></a><a id="1225" href="group-theory.precategory-of-commutative-monoids.html#1225" class="Function">Commutative-Monoid-Precategory</a> <a id="1256" class="Symbol">:</a> <a id="1258" class="Symbol">(</a><a id="1259" href="group-theory.precategory-of-commutative-monoids.html#1259" class="Bound">l</a> <a id="1261" class="Symbol">:</a> <a id="1263" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1268" class="Symbol">)</a> <a id="1270" class="Symbol">→</a> <a id="1272" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1284" class="Symbol">(</a><a id="1285" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1290" href="group-theory.precategory-of-commutative-monoids.html#1259" class="Bound">l</a><a id="1291" class="Symbol">)</a> <a id="1293" href="group-theory.precategory-of-commutative-monoids.html#1259" class="Bound">l</a>
<a id="1295" href="group-theory.precategory-of-commutative-monoids.html#1225" class="Function">Commutative-Monoid-Precategory</a> <a id="1326" class="Symbol">=</a>
  <a id="1330" href="category-theory.large-precategories.html#6110" class="Function">precategory-Large-Precategory</a> <a id="1360" href="group-theory.precategory-of-commutative-monoids.html#925" class="Function">Commutative-Monoid-Large-Precategory</a>
</pre>