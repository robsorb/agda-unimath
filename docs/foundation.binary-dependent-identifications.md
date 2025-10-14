# Binary dependent identifications

<pre class="Agda"><a id="45" class="Keyword">module</a> <a id="52" href="foundation.binary-dependent-identifications.html" class="Module">foundation.binary-dependent-identifications</a> <a id="96" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="152" class="Keyword">open</a> <a id="157" class="Keyword">import</a> <a id="164" href="foundation.binary-transport.html" class="Module">foundation.binary-transport</a>
<a id="192" class="Keyword">open</a> <a id="197" class="Keyword">import</a> <a id="204" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="230" class="Keyword">open</a> <a id="235" class="Keyword">import</a> <a id="242" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

Consider a family of types `C x y` indexed by `x : A` and `y : B`, and consider
[identifications](foundation-core.identity-types.md) `p : x ＝ x'` and
`q : y ＝ y'` in `A` and `B`, respectively. A
{{#concept "binary dependent identification" Agda=binary-dependent-identification}}
from `c : C x y` to `c' : C x' y'` over `p` and `q` is a
[dependent identification](foundation.dependent-identifications.md)

```text
  r : dependent-identification (C x') p (tr (λ t → C t y) p c) c'.
```

## Definitions

### Binary dependent identifications

<pre class="Agda"><a id="842" class="Keyword">module</a> <a id="849" href="foundation.binary-dependent-identifications.html#849" class="Module">_</a>
  <a id="853" class="Symbol">{</a><a id="854" href="foundation.binary-dependent-identifications.html#854" class="Bound">l1</a> <a id="857" href="foundation.binary-dependent-identifications.html#857" class="Bound">l2</a> <a id="860" href="foundation.binary-dependent-identifications.html#860" class="Bound">l3</a> <a id="863" class="Symbol">:</a> <a id="865" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="870" class="Symbol">}</a> <a id="872" class="Symbol">{</a><a id="873" href="foundation.binary-dependent-identifications.html#873" class="Bound">A</a> <a id="875" class="Symbol">:</a> <a id="877" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="880" href="foundation.binary-dependent-identifications.html#854" class="Bound">l1</a><a id="882" class="Symbol">}</a> <a id="884" class="Symbol">{</a><a id="885" href="foundation.binary-dependent-identifications.html#885" class="Bound">B</a> <a id="887" class="Symbol">:</a> <a id="889" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="892" href="foundation.binary-dependent-identifications.html#857" class="Bound">l2</a><a id="894" class="Symbol">}</a> <a id="896" class="Symbol">(</a><a id="897" href="foundation.binary-dependent-identifications.html#897" class="Bound">C</a> <a id="899" class="Symbol">:</a> <a id="901" href="foundation.binary-dependent-identifications.html#873" class="Bound">A</a> <a id="903" class="Symbol">→</a> <a id="905" href="foundation.binary-dependent-identifications.html#885" class="Bound">B</a> <a id="907" class="Symbol">→</a> <a id="909" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="912" href="foundation.binary-dependent-identifications.html#860" class="Bound">l3</a><a id="914" class="Symbol">)</a>
  <a id="918" class="Keyword">where</a>

  <a id="927" href="foundation.binary-dependent-identifications.html#927" class="Function">binary-dependent-identification</a> <a id="959" class="Symbol">:</a>
    <a id="965" class="Symbol">{</a><a id="966" href="foundation.binary-dependent-identifications.html#966" class="Bound">x</a> <a id="968" href="foundation.binary-dependent-identifications.html#968" class="Bound">x&#39;</a> <a id="971" class="Symbol">:</a> <a id="973" href="foundation.binary-dependent-identifications.html#873" class="Bound">A</a><a id="974" class="Symbol">}</a> <a id="976" class="Symbol">(</a><a id="977" href="foundation.binary-dependent-identifications.html#977" class="Bound">p</a> <a id="979" class="Symbol">:</a> <a id="981" href="foundation.binary-dependent-identifications.html#966" class="Bound">x</a> <a id="983" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="985" href="foundation.binary-dependent-identifications.html#968" class="Bound">x&#39;</a><a id="987" class="Symbol">)</a> <a id="989" class="Symbol">{</a><a id="990" href="foundation.binary-dependent-identifications.html#990" class="Bound">y</a> <a id="992" href="foundation.binary-dependent-identifications.html#992" class="Bound">y&#39;</a> <a id="995" class="Symbol">:</a> <a id="997" href="foundation.binary-dependent-identifications.html#885" class="Bound">B</a><a id="998" class="Symbol">}</a> <a id="1000" class="Symbol">(</a><a id="1001" href="foundation.binary-dependent-identifications.html#1001" class="Bound">q</a> <a id="1003" class="Symbol">:</a> <a id="1005" href="foundation.binary-dependent-identifications.html#990" class="Bound">y</a> <a id="1007" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1009" href="foundation.binary-dependent-identifications.html#992" class="Bound">y&#39;</a><a id="1011" class="Symbol">)</a> <a id="1013" class="Symbol">→</a>
    <a id="1019" href="foundation.binary-dependent-identifications.html#897" class="Bound">C</a> <a id="1021" href="foundation.binary-dependent-identifications.html#966" class="Bound">x</a> <a id="1023" href="foundation.binary-dependent-identifications.html#990" class="Bound">y</a> <a id="1025" class="Symbol">→</a> <a id="1027" href="foundation.binary-dependent-identifications.html#897" class="Bound">C</a> <a id="1029" href="foundation.binary-dependent-identifications.html#968" class="Bound">x&#39;</a> <a id="1032" href="foundation.binary-dependent-identifications.html#992" class="Bound">y&#39;</a> <a id="1035" class="Symbol">→</a> <a id="1037" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1040" href="foundation.binary-dependent-identifications.html#860" class="Bound">l3</a>
  <a id="1045" href="foundation.binary-dependent-identifications.html#927" class="Function">binary-dependent-identification</a> <a id="1077" href="foundation.binary-dependent-identifications.html#1077" class="Bound">p</a> <a id="1079" href="foundation.binary-dependent-identifications.html#1079" class="Bound">q</a> <a id="1081" href="foundation.binary-dependent-identifications.html#1081" class="Bound">c</a> <a id="1083" href="foundation.binary-dependent-identifications.html#1083" class="Bound">c&#39;</a> <a id="1086" class="Symbol">=</a> <a id="1088" href="foundation.binary-transport.html#801" class="Function">binary-tr</a> <a id="1098" href="foundation.binary-dependent-identifications.html#897" class="Bound">C</a> <a id="1100" href="foundation.binary-dependent-identifications.html#1077" class="Bound">p</a> <a id="1102" href="foundation.binary-dependent-identifications.html#1079" class="Bound">q</a> <a id="1104" href="foundation.binary-dependent-identifications.html#1081" class="Bound">c</a> <a id="1106" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1108" href="foundation.binary-dependent-identifications.html#1083" class="Bound">c&#39;</a>
</pre>