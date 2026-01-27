# Discrete categories

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="category-theory.discrete-categories.html" class="Module">category-theory.discrete-categories</a> <a id="75" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="131" class="Keyword">open</a> <a id="136" class="Keyword">import</a> <a id="143" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="174" class="Keyword">open</a> <a id="179" class="Keyword">import</a> <a id="186" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="218" class="Keyword">open</a> <a id="223" class="Keyword">import</a> <a id="230" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="256" class="Keyword">open</a> <a id="261" class="Keyword">import</a> <a id="268" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="284" class="Keyword">open</a> <a id="289" class="Keyword">import</a> <a id="296" href="foundation.strictly-involutive-identity-types.html" class="Module">foundation.strictly-involutive-identity-types</a>
<a id="342" class="Keyword">open</a> <a id="347" class="Keyword">import</a> <a id="354" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

### Discrete precategories

Any set induces a discrete category whose objects are elements of the set and
which contains no-nonidentity morphisms.

<pre class="Agda"><a id="554" class="Keyword">module</a> <a id="561" href="category-theory.discrete-categories.html#561" class="Module">_</a>
  <a id="565" class="Symbol">{</a><a id="566" href="category-theory.discrete-categories.html#566" class="Bound">l</a> <a id="568" class="Symbol">:</a> <a id="570" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="575" class="Symbol">}</a> <a id="577" class="Symbol">(</a><a id="578" href="category-theory.discrete-categories.html#578" class="Bound">X</a> <a id="580" class="Symbol">:</a> <a id="582" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="586" href="category-theory.discrete-categories.html#566" class="Bound">l</a><a id="587" class="Symbol">)</a>
  <a id="591" class="Keyword">where</a>

  <a id="600" href="category-theory.discrete-categories.html#600" class="Function">discrete-precategory-Set</a> <a id="625" class="Symbol">:</a> <a id="627" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="639" href="category-theory.discrete-categories.html#566" class="Bound">l</a> <a id="641" href="category-theory.discrete-categories.html#566" class="Bound">l</a>
  <a id="645" href="category-theory.discrete-categories.html#600" class="Function">discrete-precategory-Set</a> <a id="670" class="Symbol">=</a>
    <a id="676" href="category-theory.precategories.html#3706" class="Function">make-Precategory</a>
      <a id="699" class="Symbol">(</a> <a id="701" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="710" href="category-theory.discrete-categories.html#578" class="Bound">X</a><a id="711" class="Symbol">)</a>
      <a id="719" class="Symbol">(</a> <a id="721" class="Symbol">λ</a> <a id="723" href="category-theory.discrete-categories.html#723" class="Bound">x</a> <a id="725" href="category-theory.discrete-categories.html#725" class="Bound">y</a> <a id="727" class="Symbol">→</a> <a id="729" href="foundation-core.sets.html#4278" class="Function">set-Prop</a> <a id="738" class="Symbol">(</a><a id="739" href="foundation-core.sets.html#1141" class="Function">Id-Prop</a> <a id="747" href="category-theory.discrete-categories.html#578" class="Bound">X</a> <a id="749" href="category-theory.discrete-categories.html#723" class="Bound">x</a> <a id="751" href="category-theory.discrete-categories.html#725" class="Bound">y</a><a id="752" class="Symbol">))</a>
      <a id="761" class="Symbol">(</a> <a id="763" class="Symbol">λ</a> <a id="765" href="category-theory.discrete-categories.html#765" class="Bound">p</a> <a id="767" href="category-theory.discrete-categories.html#767" class="Bound">q</a> <a id="769" class="Symbol">→</a> <a id="771" href="category-theory.discrete-categories.html#767" class="Bound">q</a> <a id="773" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a> <a id="775" href="category-theory.discrete-categories.html#765" class="Bound">p</a><a id="776" class="Symbol">)</a>
      <a id="784" class="Symbol">(</a> <a id="786" class="Symbol">λ</a> <a id="788" href="category-theory.discrete-categories.html#788" class="Bound">x</a> <a id="790" class="Symbol">→</a> <a id="792" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="796" class="Symbol">)</a>
      <a id="804" class="Symbol">(</a> <a id="806" class="Symbol">λ</a> <a id="808" href="category-theory.discrete-categories.html#808" class="Bound">h</a> <a id="810" href="category-theory.discrete-categories.html#810" class="Bound">g</a> <a id="812" href="category-theory.discrete-categories.html#812" class="Bound">f</a> <a id="814" class="Symbol">→</a> <a id="816" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="820" class="Symbol">(</a><a id="821" href="foundation-core.identity-types.html#7454" class="Function">assoc</a> <a id="827" href="category-theory.discrete-categories.html#812" class="Bound">f</a> <a id="829" href="category-theory.discrete-categories.html#810" class="Bound">g</a> <a id="831" href="category-theory.discrete-categories.html#808" class="Bound">h</a><a id="832" class="Symbol">))</a>
      <a id="841" class="Symbol">(</a> <a id="843" class="Symbol">λ</a> <a id="845" href="category-theory.discrete-categories.html#845" class="Bound">_</a> <a id="847" class="Symbol">→</a> <a id="849" href="foundation-core.identity-types.html#8440" class="Function">right-unit</a><a id="859" class="Symbol">)</a>
      <a id="867" class="Symbol">(</a> <a id="869" class="Symbol">λ</a> <a id="871" href="category-theory.discrete-categories.html#871" class="Bound">_</a> <a id="873" class="Symbol">→</a> <a id="875" href="foundation-core.identity-types.html#8369" class="Function">left-unit</a><a id="884" class="Symbol">)</a>
</pre>