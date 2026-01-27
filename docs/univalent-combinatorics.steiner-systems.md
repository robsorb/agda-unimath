# Steiner systems

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="univalent-combinatorics.steiner-systems.html" class="Module">univalent-combinatorics.steiner-systems</a> <a id="75" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="131" class="Keyword">open</a> <a id="136" class="Keyword">import</a> <a id="143" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="foundation.decidable-subtypes.html" class="Module">foundation.decidable-subtypes</a>
<a id="269" class="Keyword">open</a> <a id="274" class="Keyword">import</a> <a id="281" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="313" class="Keyword">open</a> <a id="318" class="Keyword">import</a> <a id="325" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="353" class="Keyword">open</a> <a id="358" class="Keyword">import</a> <a id="365" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
</pre>
</details>

## Idea

A Steiner system of type `(t,k,n) : ℕ³` consists of an `n`-element type `X`
equipped with a (decidable) set `P` of `k`-element subtypes of `X` such that
each `t`-element subtype of `X` is contained in exactly one `k`-element subtype
in `P`. A basic example is the Fano plane, which is a Steiner system of type
`(2,3,7)`.

## Definition

### Steiner systems

<pre class="Agda"><a id="Steiner-System"></a><a id="794" href="univalent-combinatorics.steiner-systems.html#794" class="Function">Steiner-System</a> <a id="809" class="Symbol">:</a> <a id="811" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="813" class="Symbol">→</a> <a id="815" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="817" class="Symbol">→</a> <a id="819" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="821" class="Symbol">→</a> <a id="823" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="826" class="Symbol">(</a><a id="827" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="832" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="837" class="Symbol">)</a>
<a id="839" href="univalent-combinatorics.steiner-systems.html#794" class="Function">Steiner-System</a> <a id="854" href="univalent-combinatorics.steiner-systems.html#854" class="Bound">t</a> <a id="856" href="univalent-combinatorics.steiner-systems.html#856" class="Bound">k</a> <a id="858" href="univalent-combinatorics.steiner-systems.html#858" class="Bound">n</a> <a id="860" class="Symbol">=</a>
  <a id="864" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="866" class="Symbol">(</a> <a id="868" href="univalent-combinatorics.finite-types.html#3324" class="Function">Type-With-Cardinality-ℕ</a> <a id="892" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="898" href="univalent-combinatorics.steiner-systems.html#858" class="Bound">n</a><a id="899" class="Symbol">)</a>
    <a id="905" class="Symbol">(</a> <a id="907" class="Symbol">λ</a> <a id="909" href="univalent-combinatorics.steiner-systems.html#909" class="Bound">X</a> <a id="911" class="Symbol">→</a>
      <a id="919" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="921" class="Symbol">(</a> <a id="923" href="foundation.decidable-subtypes.html#2727" class="Function">decidable-subtype</a> <a id="941" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
          <a id="957" class="Symbol">(</a> <a id="959" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="961" class="Symbol">(</a> <a id="963" href="foundation.decidable-subtypes.html#2727" class="Function">decidable-subtype</a> <a id="981" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="987" class="Symbol">(</a><a id="988" href="univalent-combinatorics.finite-types.html#3442" class="Function">type-Type-With-Cardinality-ℕ</a> <a id="1017" href="univalent-combinatorics.steiner-systems.html#858" class="Bound">n</a> <a id="1019" href="univalent-combinatorics.steiner-systems.html#909" class="Bound">X</a><a id="1020" class="Symbol">))</a>
              <a id="1037" class="Symbol">(</a> <a id="1039" class="Symbol">λ</a> <a id="1041" href="univalent-combinatorics.steiner-systems.html#1041" class="Bound">P</a> <a id="1043" class="Symbol">→</a> <a id="1045" href="univalent-combinatorics.finite-types.html#3146" class="Function">has-cardinality-ℕ</a> <a id="1063" href="univalent-combinatorics.steiner-systems.html#856" class="Bound">k</a> <a id="1065" class="Symbol">(</a><a id="1066" href="foundation.decidable-subtypes.html#3903" class="Function">type-decidable-subtype</a> <a id="1089" href="univalent-combinatorics.steiner-systems.html#1041" class="Bound">P</a><a id="1090" class="Symbol">))))</a>
        <a id="1103" class="Symbol">(</a> <a id="1105" class="Symbol">λ</a> <a id="1107" href="univalent-combinatorics.steiner-systems.html#1107" class="Bound">P</a> <a id="1109" class="Symbol">→</a>
          <a id="1121" class="Symbol">(</a> <a id="1123" href="univalent-combinatorics.steiner-systems.html#1123" class="Bound">Q</a> <a id="1125" class="Symbol">:</a>
            <a id="1139" href="foundation.decidable-subtypes.html#2727" class="Function">decidable-subtype</a> <a id="1157" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1163" class="Symbol">(</a><a id="1164" href="univalent-combinatorics.finite-types.html#3442" class="Function">type-Type-With-Cardinality-ℕ</a> <a id="1193" href="univalent-combinatorics.steiner-systems.html#858" class="Bound">n</a> <a id="1195" href="univalent-combinatorics.steiner-systems.html#909" class="Bound">X</a><a id="1196" class="Symbol">))</a> <a id="1199" class="Symbol">→</a>
          <a id="1211" href="univalent-combinatorics.finite-types.html#3146" class="Function">has-cardinality-ℕ</a> <a id="1229" href="univalent-combinatorics.steiner-systems.html#854" class="Bound">t</a> <a id="1231" class="Symbol">(</a><a id="1232" href="foundation.decidable-subtypes.html#3903" class="Function">type-decidable-subtype</a> <a id="1255" href="univalent-combinatorics.steiner-systems.html#1123" class="Bound">Q</a><a id="1256" class="Symbol">)</a> <a id="1258" class="Symbol">→</a>
          <a id="1270" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a>
            <a id="1291" class="Symbol">(</a> <a id="1293" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1295" class="Symbol">(</a> <a id="1297" href="foundation.decidable-subtypes.html#3903" class="Function">type-decidable-subtype</a> <a id="1320" href="univalent-combinatorics.steiner-systems.html#1107" class="Bound">P</a><a id="1321" class="Symbol">)</a>
                <a id="1339" class="Symbol">(</a> <a id="1341" class="Symbol">λ</a> <a id="1343" href="univalent-combinatorics.steiner-systems.html#1343" class="Bound">U</a> <a id="1345" class="Symbol">→</a>
                  <a id="1365" class="Symbol">(</a><a id="1366" href="univalent-combinatorics.steiner-systems.html#1366" class="Bound">x</a> <a id="1368" class="Symbol">:</a> <a id="1370" href="univalent-combinatorics.finite-types.html#3442" class="Function">type-Type-With-Cardinality-ℕ</a> <a id="1399" href="univalent-combinatorics.steiner-systems.html#858" class="Bound">n</a> <a id="1401" href="univalent-combinatorics.steiner-systems.html#909" class="Bound">X</a><a id="1402" class="Symbol">)</a> <a id="1404" class="Symbol">→</a>
                  <a id="1424" href="foundation.decidable-subtypes.html#3255" class="Function">is-in-decidable-subtype</a> <a id="1448" href="univalent-combinatorics.steiner-systems.html#1123" class="Bound">Q</a> <a id="1450" href="univalent-combinatorics.steiner-systems.html#1366" class="Bound">x</a> <a id="1452" class="Symbol">→</a>
                  <a id="1472" href="foundation.decidable-subtypes.html#3255" class="Function">is-in-decidable-subtype</a> <a id="1496" class="Symbol">(</a><a id="1497" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1501" class="Symbol">(</a><a id="1502" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1506" href="univalent-combinatorics.steiner-systems.html#1343" class="Bound">U</a><a id="1507" class="Symbol">))</a> <a id="1510" href="univalent-combinatorics.steiner-systems.html#1366" class="Bound">x</a><a id="1511" class="Symbol">))))</a>
</pre>