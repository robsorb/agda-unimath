# The precategory of metric spaces and functions

<pre class="Agda"><a id="59" class="Keyword">module</a> <a id="66" href="metric-spaces.precategory-of-metric-spaces-and-functions.html" class="Module">metric-spaces.precategory-of-metric-spaces-and-functions</a> <a id="123" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="179" class="Keyword">open</a> <a id="184" class="Keyword">import</a> <a id="191" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="222" class="Keyword">open</a> <a id="227" class="Keyword">import</a> <a id="234" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="260" class="Keyword">open</a> <a id="265" class="Keyword">import</a> <a id="272" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="298" class="Keyword">open</a> <a id="303" class="Keyword">import</a> <a id="310" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="338" class="Keyword">open</a> <a id="343" class="Keyword">import</a> <a id="350" href="metric-spaces.functions-metric-spaces.html" class="Module">metric-spaces.functions-metric-spaces</a>
<a id="388" class="Keyword">open</a> <a id="393" class="Keyword">import</a> <a id="400" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
</pre>
</details>

## Idea

Since the carrier type of any [metric space](metric-spaces.metric-spaces.md) is
a [set](foundation-core.sets.md), they are the objects of a
[precategory](category-theory.precategories.md) where morphisms are
[functions](metric-spaces.functions-metric-spaces.md) between them.

## Definition

<pre class="Agda"><a id="754" class="Keyword">module</a> <a id="761" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#761" class="Module">_</a>
  <a id="765" class="Symbol">{</a><a id="766" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#766" class="Bound">l1</a> <a id="769" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#769" class="Bound">l2</a> <a id="772" class="Symbol">:</a> <a id="774" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="779" class="Symbol">}</a>
  <a id="783" class="Keyword">where</a>

  <a id="792" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#792" class="Function">precategory-function-Metric-Space</a> <a id="826" class="Symbol">:</a>
    <a id="832" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="844" class="Symbol">(</a><a id="845" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="850" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#766" class="Bound">l1</a> <a id="853" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="855" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="860" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#769" class="Bound">l2</a><a id="862" class="Symbol">)</a> <a id="864" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#766" class="Bound">l1</a>
  <a id="869" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#792" class="Function">precategory-function-Metric-Space</a> <a id="903" class="Symbol">=</a>
    <a id="909" href="category-theory.precategories.html#3706" class="Function">make-Precategory</a>
      <a id="932" class="Symbol">(</a> <a id="934" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="947" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#766" class="Bound">l1</a> <a id="950" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#769" class="Bound">l2</a><a id="952" class="Symbol">)</a>
      <a id="960" class="Symbol">(</a> <a id="962" href="metric-spaces.functions-metric-spaces.html#729" class="Function">set-function-Metric-Space</a><a id="987" class="Symbol">)</a>
      <a id="995" class="Symbol">(</a> <a id="997" class="Symbol">λ</a> <a id="999" class="Symbol">{</a><a id="1000" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1000" class="Bound">A</a> <a id="1002" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1002" class="Bound">B</a> <a id="1004" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1004" class="Bound">C</a><a id="1005" class="Symbol">}</a> <a id="1007" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1007" class="Bound">g</a> <a id="1009" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1009" class="Bound">f</a> <a id="1011" class="Symbol">→</a> <a id="1013" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1007" class="Bound">g</a> <a id="1015" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1017" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1009" class="Bound">f</a><a id="1018" class="Symbol">)</a>
      <a id="1026" class="Symbol">(</a> <a id="1028" class="Symbol">λ</a> <a id="1030" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1030" class="Bound">A</a> <a id="1032" class="Symbol">→</a> <a id="1034" href="foundation-core.function-types.html#307" class="Function">id</a><a id="1036" class="Symbol">)</a>
      <a id="1044" class="Symbol">(</a> <a id="1046" class="Symbol">λ</a> <a id="1048" class="Symbol">{</a><a id="1049" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1049" class="Bound">A</a> <a id="1051" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1051" class="Bound">B</a> <a id="1053" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1053" class="Bound">C</a> <a id="1055" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1055" class="Bound">D</a><a id="1056" class="Symbol">}</a> <a id="1058" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1058" class="Bound">h</a> <a id="1060" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1060" class="Bound">g</a> <a id="1062" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1062" class="Bound">f</a> <a id="1064" class="Symbol">→</a> <a id="1066" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="1070" class="Symbol">)</a>
      <a id="1078" class="Symbol">(</a> <a id="1080" class="Symbol">λ</a> <a id="1082" class="Symbol">{</a><a id="1083" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1083" class="Bound">A</a> <a id="1085" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1085" class="Bound">B</a><a id="1086" class="Symbol">}</a> <a id="1088" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1088" class="Bound">f</a> <a id="1090" class="Symbol">→</a> <a id="1092" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="1096" class="Symbol">)</a>
      <a id="1104" class="Symbol">(</a> <a id="1106" class="Symbol">λ</a> <a id="1108" class="Symbol">{</a><a id="1109" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1109" class="Bound">A</a> <a id="1111" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1111" class="Bound">B</a><a id="1112" class="Symbol">}</a> <a id="1114" href="metric-spaces.precategory-of-metric-spaces-and-functions.html#1114" class="Bound">f</a> <a id="1116" class="Symbol">→</a> <a id="1118" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="1122" class="Symbol">)</a>
</pre>