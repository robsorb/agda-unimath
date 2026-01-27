# The precategory of commutative semirings

<pre class="Agda"><a id="53" class="Keyword">module</a> <a id="60" href="commutative-algebra.precategory-of-commutative-semirings.html" class="Module">commutative-algebra.precategory-of-commutative-semirings</a> <a id="117" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="173" class="Keyword">open</a> <a id="178" class="Keyword">import</a> <a id="185" href="category-theory.full-large-subprecategories.html" class="Module">category-theory.full-large-subprecategories</a>
<a id="229" class="Keyword">open</a> <a id="234" class="Keyword">import</a> <a id="241" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>
<a id="277" class="Keyword">open</a> <a id="282" class="Keyword">import</a> <a id="289" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="320" class="Keyword">open</a> <a id="325" class="Keyword">import</a> <a id="332" href="commutative-algebra.commutative-semirings.html" class="Module">commutative-algebra.commutative-semirings</a>

<a id="375" class="Keyword">open</a> <a id="380" class="Keyword">import</a> <a id="387" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="415" class="Keyword">open</a> <a id="420" class="Keyword">import</a> <a id="427" href="ring-theory.precategory-of-semirings.html" class="Module">ring-theory.precategory-of-semirings</a>
</pre>
</details>

## Idea

The
{{#concept "precategory of commutative semirings" Agda=Commutative-Semiring-Large-Precategory}}
consists of
[commutative semirings](commutative-algebra.commutative-semirings.md) and
[homomorphisms of semirings](commutative-algebra.homomorphisms-commutative-semirings.md).

## Definitions

### The precategory of commutative semirings as a full subprecategory of semirings

<pre class="Agda"><a id="Commutative-Semiring-Full-Large-Precategory"></a><a id="875" href="commutative-algebra.precategory-of-commutative-semirings.html#875" class="Function">Commutative-Semiring-Full-Large-Precategory</a> <a id="919" class="Symbol">:</a>
  <a id="923" href="category-theory.full-large-subprecategories.html#1584" class="Function">Full-Large-Subprecategory</a> <a id="949" class="Symbol">(λ</a> <a id="952" href="commutative-algebra.precategory-of-commutative-semirings.html#952" class="Bound">l</a> <a id="954" class="Symbol">→</a> <a id="956" href="commutative-algebra.precategory-of-commutative-semirings.html#952" class="Bound">l</a><a id="957" class="Symbol">)</a> <a id="959" href="ring-theory.precategory-of-semirings.html#644" class="Function">Semiring-Large-Precategory</a>
<a id="986" href="commutative-algebra.precategory-of-commutative-semirings.html#875" class="Function">Commutative-Semiring-Full-Large-Precategory</a> <a id="1030" class="Symbol">=</a> <a id="1032" href="commutative-algebra.commutative-semirings.html#1382" class="Function">is-commutative-prop-Semiring</a>
</pre>
### The large precategory of commutative semirings

<pre class="Agda"><a id="Commutative-Semiring-Large-Precategory"></a><a id="1126" href="commutative-algebra.precategory-of-commutative-semirings.html#1126" class="Function">Commutative-Semiring-Large-Precategory</a> <a id="1165" class="Symbol">:</a> <a id="1167" href="category-theory.large-precategories.html#829" class="Record">Large-Precategory</a> <a id="1185" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1190" class="Symbol">(</a><a id="1191" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="1194" class="Symbol">)</a>
<a id="1196" href="commutative-algebra.precategory-of-commutative-semirings.html#1126" class="Function">Commutative-Semiring-Large-Precategory</a> <a id="1235" class="Symbol">=</a>
  <a id="1239" href="category-theory.full-large-subprecategories.html#5854" class="Function">large-precategory-Full-Large-Subprecategory</a>
    <a id="1287" class="Symbol">(</a> <a id="1289" href="ring-theory.precategory-of-semirings.html#644" class="Function">Semiring-Large-Precategory</a><a id="1315" class="Symbol">)</a>
    <a id="1321" class="Symbol">(</a> <a id="1323" href="commutative-algebra.precategory-of-commutative-semirings.html#875" class="Function">Commutative-Semiring-Full-Large-Precategory</a><a id="1366" class="Symbol">)</a>
</pre>
### The precategory of commutative semirings of universe level `l`

<pre class="Agda"><a id="Commutative-Semiring-Precategory"></a><a id="1449" href="commutative-algebra.precategory-of-commutative-semirings.html#1449" class="Function">Commutative-Semiring-Precategory</a> <a id="1482" class="Symbol">:</a> <a id="1484" class="Symbol">(</a><a id="1485" href="commutative-algebra.precategory-of-commutative-semirings.html#1485" class="Bound">l</a> <a id="1487" class="Symbol">:</a> <a id="1489" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1494" class="Symbol">)</a> <a id="1496" class="Symbol">→</a> <a id="1498" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1510" class="Symbol">(</a><a id="1511" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1516" href="commutative-algebra.precategory-of-commutative-semirings.html#1485" class="Bound">l</a><a id="1517" class="Symbol">)</a> <a id="1519" href="commutative-algebra.precategory-of-commutative-semirings.html#1485" class="Bound">l</a>
<a id="1521" href="commutative-algebra.precategory-of-commutative-semirings.html#1449" class="Function">Commutative-Semiring-Precategory</a> <a id="1554" class="Symbol">=</a>
  <a id="1558" href="category-theory.large-precategories.html#6110" class="Function">precategory-Large-Precategory</a> <a id="1588" href="commutative-algebra.precategory-of-commutative-semirings.html#1126" class="Function">Commutative-Semiring-Large-Precategory</a>
</pre>