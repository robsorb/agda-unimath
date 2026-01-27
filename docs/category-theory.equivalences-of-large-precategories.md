# Equivalences between large precategories

<pre class="Agda"><a id="53" class="Keyword">module</a> <a id="60" href="category-theory.equivalences-of-large-precategories.html" class="Module">category-theory.equivalences-of-large-precategories</a> <a id="112" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="category-theory.functors-large-precategories.html" class="Module">category-theory.functors-large-precategories</a>
<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>
<a id="273" class="Keyword">open</a> <a id="278" class="Keyword">import</a> <a id="285" href="category-theory.natural-isomorphisms-functors-large-precategories.html" class="Module">category-theory.natural-isomorphisms-functors-large-precategories</a>

<a id="352" class="Keyword">open</a> <a id="357" class="Keyword">import</a> <a id="364" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

Two [large precategories](category-theory.large-precategories.md) `C` and `D`
are said to be **equivalent** if there are
[functors](category-theory.functors-large-precategories.md) `F : C → D` and
`G : D → C` such that

- `G ∘ F` is
  [naturally isomorphic](category-theory.natural-isomorphisms-functors-large-precategories.md)
  to the identity functor on `C`,
- `F ∘ G` is naturally isomorphic to the identity functor on `D`.

## Definition

<pre class="Agda"><a id="869" class="Keyword">module</a> <a id="876" href="category-theory.equivalences-of-large-precategories.html#876" class="Module">_</a>
  <a id="880" class="Symbol">{</a><a id="881" href="category-theory.equivalences-of-large-precategories.html#881" class="Bound">αC</a> <a id="884" href="category-theory.equivalences-of-large-precategories.html#884" class="Bound">αD</a> <a id="887" class="Symbol">:</a> <a id="889" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="895" class="Symbol">→</a> <a id="897" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="902" class="Symbol">}</a> <a id="904" class="Symbol">{</a><a id="905" href="category-theory.equivalences-of-large-precategories.html#905" class="Bound">βC</a> <a id="908" href="category-theory.equivalences-of-large-precategories.html#908" class="Bound">βD</a> <a id="911" class="Symbol">:</a> <a id="913" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="919" class="Symbol">→</a> <a id="921" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="927" class="Symbol">→</a> <a id="929" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="934" class="Symbol">}</a>
  <a id="938" class="Symbol">(</a><a id="939" href="category-theory.equivalences-of-large-precategories.html#939" class="Bound">C</a> <a id="941" class="Symbol">:</a> <a id="943" href="category-theory.large-precategories.html#829" class="Record">Large-Precategory</a> <a id="961" href="category-theory.equivalences-of-large-precategories.html#881" class="Bound">αC</a> <a id="964" href="category-theory.equivalences-of-large-precategories.html#905" class="Bound">βC</a><a id="966" class="Symbol">)</a> <a id="968" class="Symbol">(</a><a id="969" href="category-theory.equivalences-of-large-precategories.html#969" class="Bound">D</a> <a id="971" class="Symbol">:</a> <a id="973" href="category-theory.large-precategories.html#829" class="Record">Large-Precategory</a> <a id="991" href="category-theory.equivalences-of-large-precategories.html#884" class="Bound">αD</a> <a id="994" href="category-theory.equivalences-of-large-precategories.html#908" class="Bound">βD</a><a id="996" class="Symbol">)</a>
  <a id="1000" class="Keyword">where</a>

  <a id="1009" class="Keyword">record</a>
    <a id="1020" href="category-theory.equivalences-of-large-precategories.html#1020" class="Record">equivalence-Large-Precategory</a> <a id="1050" class="Symbol">(</a><a id="1051" href="category-theory.equivalences-of-large-precategories.html#1051" class="Bound">γ</a> <a id="1053" href="category-theory.equivalences-of-large-precategories.html#1053" class="Bound">γ&#39;</a> <a id="1056" class="Symbol">:</a> <a id="1058" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1064" class="Symbol">→</a> <a id="1066" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1071" class="Symbol">)</a> <a id="1073" class="Symbol">:</a> <a id="1075" href="Agda.Primitive.html#512" class="Primitive">UUω</a> <a id="1079" class="Keyword">where</a>
    <a id="1089" class="Keyword">constructor</a>
      <a id="1107" href="category-theory.equivalences-of-large-precategories.html#1107" class="InductiveConstructor">make-equivalence-Large-Precategory</a>
    <a id="1146" class="Keyword">field</a>
      <a id="1158" href="category-theory.equivalences-of-large-precategories.html#1158" class="Field">functor-equivalence-Large-Precategory</a> <a id="1196" class="Symbol">:</a>
        <a id="1206" href="category-theory.functors-large-precategories.html#906" class="Record">functor-Large-Precategory</a> <a id="1232" href="category-theory.equivalences-of-large-precategories.html#1051" class="Bound">γ</a> <a id="1234" href="category-theory.equivalences-of-large-precategories.html#939" class="Bound">C</a> <a id="1236" href="category-theory.equivalences-of-large-precategories.html#969" class="Bound">D</a>
      <a id="1244" href="category-theory.equivalences-of-large-precategories.html#1244" class="Field">functor-inv-equivalence-Large-Precategory</a> <a id="1286" class="Symbol">:</a>
        <a id="1296" href="category-theory.functors-large-precategories.html#906" class="Record">functor-Large-Precategory</a> <a id="1322" href="category-theory.equivalences-of-large-precategories.html#1053" class="Bound">γ&#39;</a> <a id="1325" href="category-theory.equivalences-of-large-precategories.html#969" class="Bound">D</a> <a id="1327" href="category-theory.equivalences-of-large-precategories.html#939" class="Bound">C</a>
      <a id="1335" href="category-theory.equivalences-of-large-precategories.html#1335" class="Field">is-section-functor-inv-equivalence-Large-Precategory</a> <a id="1388" class="Symbol">:</a>
        <a id="1398" href="category-theory.natural-isomorphisms-functors-large-precategories.html#1512" class="Record">natural-isomorphism-Large-Precategory</a>
          <a id="1446" class="Symbol">(</a> <a id="1448" href="category-theory.functors-large-precategories.html#4888" class="Function">comp-functor-Large-Precategory</a> <a id="1479" href="category-theory.equivalences-of-large-precategories.html#969" class="Bound">D</a> <a id="1481" href="category-theory.equivalences-of-large-precategories.html#939" class="Bound">C</a> <a id="1483" href="category-theory.equivalences-of-large-precategories.html#969" class="Bound">D</a>
            <a id="1497" href="category-theory.equivalences-of-large-precategories.html#1158" class="Field">functor-equivalence-Large-Precategory</a>
            <a id="1547" href="category-theory.equivalences-of-large-precategories.html#1244" class="Field">functor-inv-equivalence-Large-Precategory</a><a id="1588" class="Symbol">)</a>
          <a id="1600" class="Symbol">(</a> <a id="1602" href="category-theory.functors-large-precategories.html#2287" class="Function">id-functor-Large-Precategory</a> <a id="1631" href="category-theory.equivalences-of-large-precategories.html#969" class="Bound">D</a><a id="1632" class="Symbol">)</a>
      <a id="1640" href="category-theory.equivalences-of-large-precategories.html#1640" class="Field">is-retraction-functor-inv-equivalence-Large-Precategory</a> <a id="1696" class="Symbol">:</a>
        <a id="1706" href="category-theory.natural-isomorphisms-functors-large-precategories.html#1512" class="Record">natural-isomorphism-Large-Precategory</a>
          <a id="1754" class="Symbol">(</a> <a id="1756" href="category-theory.functors-large-precategories.html#4888" class="Function">comp-functor-Large-Precategory</a> <a id="1787" href="category-theory.equivalences-of-large-precategories.html#939" class="Bound">C</a> <a id="1789" href="category-theory.equivalences-of-large-precategories.html#969" class="Bound">D</a> <a id="1791" href="category-theory.equivalences-of-large-precategories.html#939" class="Bound">C</a>
            <a id="1805" href="category-theory.equivalences-of-large-precategories.html#1244" class="Field">functor-inv-equivalence-Large-Precategory</a>
            <a id="1859" href="category-theory.equivalences-of-large-precategories.html#1158" class="Field">functor-equivalence-Large-Precategory</a><a id="1896" class="Symbol">)</a>
          <a id="1908" class="Symbol">(</a> <a id="1910" href="category-theory.functors-large-precategories.html#2287" class="Function">id-functor-Large-Precategory</a> <a id="1939" href="category-theory.equivalences-of-large-precategories.html#939" class="Bound">C</a><a id="1940" class="Symbol">)</a>
</pre>