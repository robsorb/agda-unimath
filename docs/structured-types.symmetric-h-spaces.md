# Symmetric H-spaces

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="structured-types.symmetric-h-spaces.html" class="Module">structured-types.symmetric-h-spaces</a> <a id="74" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="130" class="Keyword">open</a> <a id="135" class="Keyword">import</a> <a id="142" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="174" class="Keyword">open</a> <a id="179" class="Keyword">import</a> <a id="186" href="foundation.symmetric-operations.html" class="Module">foundation.symmetric-operations</a>
<a id="218" class="Keyword">open</a> <a id="223" class="Keyword">import</a> <a id="230" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="structured-types.involutive-type-of-h-space-structures.html" class="Module">structured-types.involutive-type-of-h-space-structures</a>
<a id="325" class="Keyword">open</a> <a id="330" class="Keyword">import</a> <a id="337" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
<a id="368" class="Keyword">open</a> <a id="373" class="Keyword">import</a> <a id="380" href="structured-types.symmetric-elements-involutive-types.html" class="Module">structured-types.symmetric-elements-involutive-types</a>
</pre>
</details>

## Idea

**Symmetric H-spaces** are [pointed types](structured-types.pointed-types.md)
`A` [equipped](foundation.structure.md) with a symmetric element of the
[involutive type of H-space structures](structured-types.involutive-type-of-h-space-structures.md)
on `A`.

## Definitions

### Symmetric H-space structures on a pointed type

<pre class="Agda"><a id="symmetric-H-Space"></a><a id="793" href="structured-types.symmetric-h-spaces.html#793" class="Function">symmetric-H-Space</a> <a id="811" class="Symbol">:</a>
  <a id="815" class="Symbol">{</a><a id="816" href="structured-types.symmetric-h-spaces.html#816" class="Bound">l1</a> <a id="819" class="Symbol">:</a> <a id="821" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="826" class="Symbol">}</a> <a id="828" class="Symbol">(</a><a id="829" href="structured-types.symmetric-h-spaces.html#829" class="Bound">A</a> <a id="831" class="Symbol">:</a> <a id="833" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="846" href="structured-types.symmetric-h-spaces.html#816" class="Bound">l1</a><a id="848" class="Symbol">)</a> <a id="850" class="Symbol">→</a> <a id="852" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="855" class="Symbol">(</a><a id="856" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="861" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="867" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="869" href="structured-types.symmetric-h-spaces.html#816" class="Bound">l1</a><a id="871" class="Symbol">)</a>
<a id="873" href="structured-types.symmetric-h-spaces.html#793" class="Function">symmetric-H-Space</a> <a id="891" href="structured-types.symmetric-h-spaces.html#891" class="Bound">A</a> <a id="893" class="Symbol">=</a>
  <a id="897" href="structured-types.symmetric-elements-involutive-types.html#569" class="Function">symmetric-element-Involutive-Type</a> <a id="931" class="Symbol">(</a><a id="932" href="structured-types.involutive-type-of-h-space-structures.html#1265" class="Function">h-space-Involutive-Type</a> <a id="956" href="structured-types.symmetric-h-spaces.html#891" class="Bound">A</a><a id="957" class="Symbol">)</a>
</pre>
### The symmetric binary operation on a symmetric H-space

<pre class="Agda"><a id="symmetric-mul-symmetric-H-Space"></a><a id="1031" href="structured-types.symmetric-h-spaces.html#1031" class="Function">symmetric-mul-symmetric-H-Space</a> <a id="1063" class="Symbol">:</a>
  <a id="1067" class="Symbol">{</a><a id="1068" href="structured-types.symmetric-h-spaces.html#1068" class="Bound">l1</a> <a id="1071" class="Symbol">:</a> <a id="1073" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1078" class="Symbol">}</a> <a id="1080" class="Symbol">(</a><a id="1081" href="structured-types.symmetric-h-spaces.html#1081" class="Bound">A</a> <a id="1083" class="Symbol">:</a> <a id="1085" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1098" href="structured-types.symmetric-h-spaces.html#1068" class="Bound">l1</a><a id="1100" class="Symbol">)</a> <a id="1102" class="Symbol">(</a><a id="1103" href="structured-types.symmetric-h-spaces.html#1103" class="Bound">μ</a> <a id="1105" class="Symbol">:</a> <a id="1107" href="structured-types.symmetric-h-spaces.html#793" class="Function">symmetric-H-Space</a> <a id="1125" href="structured-types.symmetric-h-spaces.html#1081" class="Bound">A</a><a id="1126" class="Symbol">)</a> <a id="1128" class="Symbol">→</a>
  <a id="1132" href="foundation.symmetric-operations.html#2506" class="Function">symmetric-operation</a> <a id="1152" class="Symbol">(</a><a id="1153" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="1171" href="structured-types.symmetric-h-spaces.html#1081" class="Bound">A</a><a id="1172" class="Symbol">)</a> <a id="1174" class="Symbol">(</a><a id="1175" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="1193" href="structured-types.symmetric-h-spaces.html#1081" class="Bound">A</a><a id="1194" class="Symbol">)</a>
<a id="1196" href="structured-types.symmetric-h-spaces.html#1031" class="Function">symmetric-mul-symmetric-H-Space</a> <a id="1228" href="structured-types.symmetric-h-spaces.html#1228" class="Bound">A</a> <a id="1230" href="structured-types.symmetric-h-spaces.html#1230" class="Bound">μ</a> <a id="1232" class="Symbol">(</a><a id="1233" href="structured-types.symmetric-h-spaces.html#1233" class="Bound">X</a> <a id="1235" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1237" href="structured-types.symmetric-h-spaces.html#1237" class="Bound">f</a><a id="1238" class="Symbol">)</a> <a id="1240" class="Symbol">=</a> <a id="1242" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1246" class="Symbol">(</a><a id="1247" href="structured-types.symmetric-h-spaces.html#1230" class="Bound">μ</a> <a id="1249" href="structured-types.symmetric-h-spaces.html#1233" class="Bound">X</a><a id="1250" class="Symbol">)</a> <a id="1252" href="structured-types.symmetric-h-spaces.html#1237" class="Bound">f</a>
</pre>