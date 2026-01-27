# Monotonic rational neighborhood relations

<pre class="Agda"><a id="54" class="Keyword">module</a> <a id="61" href="metric-spaces.monotonic-rational-neighborhood-relations.html" class="Module">metric-spaces.monotonic-rational-neighborhood-relations</a> <a id="117" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="173" class="Keyword">open</a> <a id="178" class="Keyword">import</a> <a id="185" href="elementary-number-theory.positive-rational-numbers.html" class="Module">elementary-number-theory.positive-rational-numbers</a>

<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="273" class="Keyword">open</a> <a id="278" class="Keyword">import</a> <a id="285" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="313" class="Keyword">open</a> <a id="318" class="Keyword">import</a> <a id="325" href="metric-spaces.rational-neighborhood-relations.html" class="Module">metric-spaces.rational-neighborhood-relations</a>
</pre>
</details>

## Idea

A
[rational neighborhood relation](metric-spaces.rational-neighborhood-relations.md)
is
{{#concept "monotonic" Disambiguation="rational neighborhood relation" Agda=is-monotonic-Rational-Neighborhood-Relation}}
if, for all `d₁ < d₂`, all `d₁`-neighborhoods are `d₂`-neighborhoods.

## Definitions

### The property of being a monotonic rational neighborhood relation

<pre class="Agda"><a id="772" class="Keyword">module</a> <a id="779" href="metric-spaces.monotonic-rational-neighborhood-relations.html#779" class="Module">_</a>
  <a id="783" class="Symbol">{</a><a id="784" href="metric-spaces.monotonic-rational-neighborhood-relations.html#784" class="Bound">l1</a> <a id="787" href="metric-spaces.monotonic-rational-neighborhood-relations.html#787" class="Bound">l2</a> <a id="790" class="Symbol">:</a> <a id="792" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="797" class="Symbol">}</a> <a id="799" class="Symbol">{</a><a id="800" href="metric-spaces.monotonic-rational-neighborhood-relations.html#800" class="Bound">A</a> <a id="802" class="Symbol">:</a> <a id="804" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="807" href="metric-spaces.monotonic-rational-neighborhood-relations.html#784" class="Bound">l1</a><a id="809" class="Symbol">}</a> <a id="811" class="Symbol">(</a><a id="812" href="metric-spaces.monotonic-rational-neighborhood-relations.html#812" class="Bound">B</a> <a id="814" class="Symbol">:</a> <a id="816" href="metric-spaces.rational-neighborhood-relations.html#1912" class="Function">Rational-Neighborhood-Relation</a> <a id="847" href="metric-spaces.monotonic-rational-neighborhood-relations.html#787" class="Bound">l2</a> <a id="850" href="metric-spaces.monotonic-rational-neighborhood-relations.html#800" class="Bound">A</a><a id="851" class="Symbol">)</a>
  <a id="855" class="Keyword">where</a>

  <a id="864" href="metric-spaces.monotonic-rational-neighborhood-relations.html#864" class="Function">is-monotonic-prop-Rational-Neighborhood-Relation</a> <a id="913" class="Symbol">:</a> <a id="915" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="920" class="Symbol">(</a><a id="921" href="metric-spaces.monotonic-rational-neighborhood-relations.html#784" class="Bound">l1</a> <a id="924" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="926" href="metric-spaces.monotonic-rational-neighborhood-relations.html#787" class="Bound">l2</a><a id="928" class="Symbol">)</a>
  <a id="932" href="metric-spaces.monotonic-rational-neighborhood-relations.html#864" class="Function">is-monotonic-prop-Rational-Neighborhood-Relation</a> <a id="981" class="Symbol">=</a>
    <a id="987" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
      <a id="1000" class="Symbol">(</a> <a id="1002" href="metric-spaces.monotonic-rational-neighborhood-relations.html#800" class="Bound">A</a><a id="1003" class="Symbol">)</a>
      <a id="1011" class="Symbol">(</a> <a id="1013" class="Symbol">λ</a> <a id="1015" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1015" class="Bound">x</a> <a id="1017" class="Symbol">→</a>
        <a id="1027" class="Symbol">(</a> <a id="1029" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
          <a id="1046" class="Symbol">(</a> <a id="1048" href="metric-spaces.monotonic-rational-neighborhood-relations.html#800" class="Bound">A</a><a id="1049" class="Symbol">)</a>
          <a id="1061" class="Symbol">(</a> <a id="1063" class="Symbol">λ</a> <a id="1065" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1065" class="Bound">y</a> <a id="1067" class="Symbol">→</a>
            <a id="1081" class="Symbol">(</a> <a id="1083" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
              <a id="1104" class="Symbol">(</a> <a id="1106" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a><a id="1108" class="Symbol">)</a>
              <a id="1124" class="Symbol">(</a> <a id="1126" class="Symbol">λ</a> <a id="1128" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1128" class="Bound">d₁</a> <a id="1131" class="Symbol">→</a>
                <a id="1149" class="Symbol">(</a> <a id="1151" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
                  <a id="1176" class="Symbol">(</a> <a id="1178" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a><a id="1180" class="Symbol">)</a>
                  <a id="1200" class="Symbol">(</a> <a id="1202" class="Symbol">λ</a> <a id="1204" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1204" class="Bound">d₂</a> <a id="1207" class="Symbol">→</a>
                    <a id="1229" class="Symbol">(</a> <a id="1231" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
                      <a id="1260" class="Symbol">(</a> <a id="1262" href="elementary-number-theory.positive-rational-numbers.html#16585" class="Function">le-ℚ⁺</a> <a id="1268" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1128" class="Bound">d₁</a> <a id="1271" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1204" class="Bound">d₂</a><a id="1273" class="Symbol">)</a>
                      <a id="1297" class="Symbol">(</a> <a id="1299" class="Symbol">λ</a> <a id="1301" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1301" class="Bound">H</a> <a id="1303" class="Symbol">→</a>
                        <a id="1329" href="foundation-core.propositions.html#8765" class="Function">hom-Prop</a> <a id="1338" class="Symbol">(</a><a id="1339" href="metric-spaces.monotonic-rational-neighborhood-relations.html#812" class="Bound">B</a> <a id="1341" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1128" class="Bound">d₁</a> <a id="1344" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1015" class="Bound">x</a> <a id="1346" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1065" class="Bound">y</a><a id="1347" class="Symbol">)</a> <a id="1349" class="Symbol">(</a><a id="1350" href="metric-spaces.monotonic-rational-neighborhood-relations.html#812" class="Bound">B</a> <a id="1352" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1204" class="Bound">d₂</a> <a id="1355" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1015" class="Bound">x</a> <a id="1357" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1065" class="Bound">y</a><a id="1358" class="Symbol">))))))))))</a>

  <a id="1372" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1372" class="Function">is-monotonic-Rational-Neighborhood-Relation</a> <a id="1416" class="Symbol">:</a> <a id="1418" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1421" class="Symbol">(</a><a id="1422" href="metric-spaces.monotonic-rational-neighborhood-relations.html#784" class="Bound">l1</a> <a id="1425" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1427" href="metric-spaces.monotonic-rational-neighborhood-relations.html#787" class="Bound">l2</a><a id="1429" class="Symbol">)</a>
  <a id="1433" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1372" class="Function">is-monotonic-Rational-Neighborhood-Relation</a> <a id="1477" class="Symbol">=</a>
    <a id="1483" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1493" href="metric-spaces.monotonic-rational-neighborhood-relations.html#864" class="Function">is-monotonic-prop-Rational-Neighborhood-Relation</a>

  <a id="1545" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1545" class="Function">is-prop-is-monotonic-Rational-Neighborhood-Relation</a> <a id="1597" class="Symbol">:</a>
    <a id="1603" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1611" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1372" class="Function">is-monotonic-Rational-Neighborhood-Relation</a>
  <a id="1657" href="metric-spaces.monotonic-rational-neighborhood-relations.html#1545" class="Function">is-prop-is-monotonic-Rational-Neighborhood-Relation</a> <a id="1709" class="Symbol">=</a>
    <a id="1715" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1733" href="metric-spaces.monotonic-rational-neighborhood-relations.html#864" class="Function">is-monotonic-prop-Rational-Neighborhood-Relation</a>
</pre>