# Operations on spans of families of types

<pre class="Agda"><a id="53" class="Keyword">module</a> <a id="60" href="foundation.operations-spans-families-of-types.html" class="Module">foundation.operations-spans-families-of-types</a> <a id="106" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="162" class="Keyword">open</a> <a id="167" class="Keyword">import</a> <a id="174" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="foundation.spans-families-of-types.html" class="Module">foundation.spans-families-of-types</a>
<a id="253" class="Keyword">open</a> <a id="258" class="Keyword">import</a> <a id="265" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="293" class="Keyword">open</a> <a id="298" class="Keyword">import</a> <a id="305" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
</pre>
</details>

## Idea

This file contains a collection of operations that produce new
[spans of families of types](foundation.spans-families-of-types.md) from given
spans of families of types.

## Definitions

### Concatenation of spans and families of maps

Consider a span `𝒮 := (S , s)` on a family of types `A : I → 𝒰` and consider a
family of maps `f : (i : I) → A i → B i`. Then we can concatenate the span `𝒮`
with the family of maps `f` to obtain the span `(S , λ i → f i ∘ s i)` on `B`.

<pre class="Agda"><a id="844" class="Keyword">module</a> <a id="851" href="foundation.operations-spans-families-of-types.html#851" class="Module">_</a>
  <a id="855" class="Symbol">{</a><a id="856" href="foundation.operations-spans-families-of-types.html#856" class="Bound">l1</a> <a id="859" href="foundation.operations-spans-families-of-types.html#859" class="Bound">l2</a> <a id="862" href="foundation.operations-spans-families-of-types.html#862" class="Bound">l3</a> <a id="865" href="foundation.operations-spans-families-of-types.html#865" class="Bound">l4</a> <a id="868" class="Symbol">:</a> <a id="870" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="875" class="Symbol">}</a> <a id="877" class="Symbol">{</a><a id="878" href="foundation.operations-spans-families-of-types.html#878" class="Bound">I</a> <a id="880" class="Symbol">:</a> <a id="882" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="885" href="foundation.operations-spans-families-of-types.html#856" class="Bound">l1</a><a id="887" class="Symbol">}</a> <a id="889" class="Symbol">{</a><a id="890" href="foundation.operations-spans-families-of-types.html#890" class="Bound">A</a> <a id="892" class="Symbol">:</a> <a id="894" href="foundation.operations-spans-families-of-types.html#878" class="Bound">I</a> <a id="896" class="Symbol">→</a> <a id="898" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="901" href="foundation.operations-spans-families-of-types.html#859" class="Bound">l2</a><a id="903" class="Symbol">}</a> <a id="905" class="Symbol">{</a><a id="906" href="foundation.operations-spans-families-of-types.html#906" class="Bound">B</a> <a id="908" class="Symbol">:</a> <a id="910" href="foundation.operations-spans-families-of-types.html#878" class="Bound">I</a> <a id="912" class="Symbol">→</a> <a id="914" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="917" href="foundation.operations-spans-families-of-types.html#862" class="Bound">l3</a><a id="919" class="Symbol">}</a>
  <a id="923" class="Symbol">(</a><a id="924" href="foundation.operations-spans-families-of-types.html#924" class="Bound">𝒮</a> <a id="926" class="Symbol">:</a> <a id="928" href="foundation.spans-families-of-types.html#839" class="Function">span-type-family</a> <a id="945" href="foundation.operations-spans-families-of-types.html#865" class="Bound">l4</a> <a id="948" href="foundation.operations-spans-families-of-types.html#890" class="Bound">A</a><a id="949" class="Symbol">)</a>
  <a id="953" class="Symbol">(</a><a id="954" href="foundation.operations-spans-families-of-types.html#954" class="Bound">f</a> <a id="956" class="Symbol">:</a> <a id="958" class="Symbol">(</a><a id="959" href="foundation.operations-spans-families-of-types.html#959" class="Bound">i</a> <a id="961" class="Symbol">:</a> <a id="963" href="foundation.operations-spans-families-of-types.html#878" class="Bound">I</a><a id="964" class="Symbol">)</a> <a id="966" class="Symbol">→</a> <a id="968" href="foundation.operations-spans-families-of-types.html#890" class="Bound">A</a> <a id="970" href="foundation.operations-spans-families-of-types.html#959" class="Bound">i</a> <a id="972" class="Symbol">→</a> <a id="974" href="foundation.operations-spans-families-of-types.html#906" class="Bound">B</a> <a id="976" href="foundation.operations-spans-families-of-types.html#959" class="Bound">i</a><a id="977" class="Symbol">)</a>
  <a id="981" class="Keyword">where</a>

  <a id="990" href="foundation.operations-spans-families-of-types.html#990" class="Function">spanning-type-concat-span-hom-family-of-types</a> <a id="1036" class="Symbol">:</a> <a id="1038" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1041" href="foundation.operations-spans-families-of-types.html#865" class="Bound">l4</a>
  <a id="1046" href="foundation.operations-spans-families-of-types.html#990" class="Function">spanning-type-concat-span-hom-family-of-types</a> <a id="1092" class="Symbol">=</a>
    <a id="1098" href="foundation.spans-families-of-types.html#1038" class="Function">spanning-type-span-type-family</a> <a id="1129" href="foundation.operations-spans-families-of-types.html#924" class="Bound">𝒮</a>

  <a id="1134" href="foundation.operations-spans-families-of-types.html#1134" class="Function">map-concat-span-hom-family-of-types</a> <a id="1170" class="Symbol">:</a>
    <a id="1176" class="Symbol">(</a><a id="1177" href="foundation.operations-spans-families-of-types.html#1177" class="Bound">i</a> <a id="1179" class="Symbol">:</a> <a id="1181" href="foundation.operations-spans-families-of-types.html#878" class="Bound">I</a><a id="1182" class="Symbol">)</a> <a id="1184" class="Symbol">→</a> <a id="1186" href="foundation.operations-spans-families-of-types.html#990" class="Function">spanning-type-concat-span-hom-family-of-types</a> <a id="1232" class="Symbol">→</a> <a id="1234" href="foundation.operations-spans-families-of-types.html#906" class="Bound">B</a> <a id="1236" href="foundation.operations-spans-families-of-types.html#1177" class="Bound">i</a>
  <a id="1240" href="foundation.operations-spans-families-of-types.html#1134" class="Function">map-concat-span-hom-family-of-types</a> <a id="1276" href="foundation.operations-spans-families-of-types.html#1276" class="Bound">i</a> <a id="1278" class="Symbol">=</a>
    <a id="1284" href="foundation.operations-spans-families-of-types.html#954" class="Bound">f</a> <a id="1286" href="foundation.operations-spans-families-of-types.html#1276" class="Bound">i</a> <a id="1288" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1290" href="foundation.spans-families-of-types.html#1121" class="Function">map-span-type-family</a> <a id="1311" href="foundation.operations-spans-families-of-types.html#924" class="Bound">𝒮</a> <a id="1313" href="foundation.operations-spans-families-of-types.html#1276" class="Bound">i</a>

  <a id="1318" href="foundation.operations-spans-families-of-types.html#1318" class="Function">concat-span-hom-family-of-types</a> <a id="1350" class="Symbol">:</a>
    <a id="1356" href="foundation.spans-families-of-types.html#839" class="Function">span-type-family</a> <a id="1373" href="foundation.operations-spans-families-of-types.html#865" class="Bound">l4</a> <a id="1376" href="foundation.operations-spans-families-of-types.html#906" class="Bound">B</a>
  <a id="1380" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1384" href="foundation.operations-spans-families-of-types.html#1318" class="Function">concat-span-hom-family-of-types</a> <a id="1416" class="Symbol">=</a>
    <a id="1422" href="foundation.operations-spans-families-of-types.html#990" class="Function">spanning-type-concat-span-hom-family-of-types</a>
  <a id="1470" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1474" href="foundation.operations-spans-families-of-types.html#1318" class="Function">concat-span-hom-family-of-types</a> <a id="1506" class="Symbol">=</a>
    <a id="1512" href="foundation.operations-spans-families-of-types.html#1134" class="Function">map-concat-span-hom-family-of-types</a>
</pre>