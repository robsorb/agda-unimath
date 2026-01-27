# Orientations of cubes

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="univalent-combinatorics.orientations-cubes.html" class="Module">univalent-combinatorics.orientations-cubes</a> <a id="84" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="140" class="Keyword">open</a> <a id="145" class="Keyword">import</a> <a id="152" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="194" class="Keyword">open</a> <a id="199" class="Keyword">import</a> <a id="206" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="232" class="Keyword">open</a> <a id="237" class="Keyword">import</a> <a id="244" href="foundation.iterating-functions.html" class="Module">foundation.iterating-functions</a>
<a id="275" class="Keyword">open</a> <a id="280" class="Keyword">import</a> <a id="287" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="315" class="Keyword">open</a> <a id="320" class="Keyword">import</a> <a id="327" href="univalent-combinatorics.cubes.html" class="Module">univalent-combinatorics.cubes</a>
<a id="357" class="Keyword">open</a> <a id="362" class="Keyword">import</a> <a id="369" href="univalent-combinatorics.dependent-pair-types.html" class="Module">univalent-combinatorics.dependent-pair-types</a>
<a id="414" class="Keyword">open</a> <a id="419" class="Keyword">import</a> <a id="426" href="univalent-combinatorics.equality-finite-types.html" class="Module">univalent-combinatorics.equality-finite-types</a>
<a id="472" class="Keyword">open</a> <a id="477" class="Keyword">import</a> <a id="484" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
<a id="521" class="Keyword">open</a> <a id="526" class="Keyword">import</a> <a id="533" href="univalent-combinatorics.function-types.html" class="Module">univalent-combinatorics.function-types</a>
<a id="572" class="Keyword">open</a> <a id="577" class="Keyword">import</a> <a id="584" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Definition

<pre class="Agda"><a id="orientation-cube"></a><a id="670" href="univalent-combinatorics.orientations-cubes.html#670" class="Function">orientation-cube</a> <a id="687" class="Symbol">:</a> <a id="689" class="Symbol">{</a><a id="690" href="univalent-combinatorics.orientations-cubes.html#690" class="Bound">k</a> <a id="692" class="Symbol">:</a> <a id="694" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="695" class="Symbol">}</a> <a id="697" class="Symbol">→</a> <a id="699" href="univalent-combinatorics.cubes.html#416" class="Function">cube</a> <a id="704" href="univalent-combinatorics.orientations-cubes.html#690" class="Bound">k</a> <a id="706" class="Symbol">→</a> <a id="708" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="711" class="Symbol">(</a><a id="712" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="717" class="Symbol">)</a>
<a id="719" href="univalent-combinatorics.orientations-cubes.html#670" class="Function">orientation-cube</a> <a id="736" class="Symbol">{</a><a id="737" href="univalent-combinatorics.orientations-cubes.html#737" class="Bound">k</a><a id="738" class="Symbol">}</a> <a id="740" href="univalent-combinatorics.orientations-cubes.html#740" class="Bound">X</a> <a id="742" class="Symbol">=</a>
  <a id="746" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="748" class="Symbol">(</a> <a id="750" href="univalent-combinatorics.cubes.html#1911" class="Function">vertex-cube</a> <a id="762" href="univalent-combinatorics.orientations-cubes.html#737" class="Bound">k</a> <a id="764" href="univalent-combinatorics.orientations-cubes.html#740" class="Bound">X</a> <a id="766" class="Symbol">→</a> <a id="768" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="772" class="Number">2</a><a id="773" class="Symbol">)</a>
    <a id="779" class="Symbol">(</a> <a id="781" class="Symbol">λ</a> <a id="783" href="univalent-combinatorics.orientations-cubes.html#783" class="Bound">h</a> <a id="785" class="Symbol">→</a>
      <a id="793" class="Symbol">(</a> <a id="795" href="univalent-combinatorics.orientations-cubes.html#795" class="Bound">x</a> <a id="797" href="univalent-combinatorics.orientations-cubes.html#797" class="Bound">y</a> <a id="799" class="Symbol">:</a> <a id="801" href="univalent-combinatorics.cubes.html#1911" class="Function">vertex-cube</a> <a id="813" href="univalent-combinatorics.orientations-cubes.html#737" class="Bound">k</a> <a id="815" href="univalent-combinatorics.orientations-cubes.html#740" class="Bound">X</a><a id="816" class="Symbol">)</a> <a id="818" class="Symbol">→</a>
        <a id="828" href="foundation-core.identity-types.html#2641" class="Datatype">Id</a>
          <a id="841" class="Symbol">(</a> <a id="843" href="foundation-core.iterating-functions.html#724" class="Function">iterate</a>
            <a id="863" class="Symbol">(</a> <a id="865" href="univalent-combinatorics.finite-types.html#11098" class="Function">number-of-elements-is-finite</a>
              <a id="908" class="Symbol">(</a> <a id="910" href="univalent-combinatorics.dependent-pair-types.html#1750" class="Function">is-finite-Σ</a>
                <a id="938" class="Symbol">(</a> <a id="940" href="univalent-combinatorics.cubes.html#1118" class="Function">is-finite-dim-cube</a> <a id="959" href="univalent-combinatorics.orientations-cubes.html#737" class="Bound">k</a> <a id="961" href="univalent-combinatorics.orientations-cubes.html#740" class="Bound">X</a><a id="962" class="Symbol">)</a>
                <a id="980" class="Symbol">(</a> <a id="982" class="Symbol">λ</a> <a id="984" href="univalent-combinatorics.orientations-cubes.html#984" class="Bound">d</a> <a id="986" class="Symbol">→</a>
                  <a id="1006" href="univalent-combinatorics.function-types.html#1653" class="Function">is-finite-function-type</a>
                    <a id="1050" class="Symbol">(</a> <a id="1052" href="univalent-combinatorics.equality-finite-types.html#1883" class="Function">is-finite-eq</a>
                      <a id="1087" class="Symbol">(</a> <a id="1089" href="univalent-combinatorics.equality-finite-types.html#975" class="Function">has-decidable-equality-is-finite</a>
                        <a id="1146" class="Symbol">(</a> <a id="1148" href="univalent-combinatorics.cubes.html#1755" class="Function">is-finite-axis-cube</a> <a id="1168" href="univalent-combinatorics.orientations-cubes.html#737" class="Bound">k</a> <a id="1170" href="univalent-combinatorics.orientations-cubes.html#740" class="Bound">X</a> <a id="1172" href="univalent-combinatorics.orientations-cubes.html#984" class="Bound">d</a><a id="1173" class="Symbol">))</a>
                    <a id="1196" class="Symbol">{</a> <a id="1198" href="univalent-combinatorics.orientations-cubes.html#795" class="Bound">x</a> <a id="1200" href="univalent-combinatorics.orientations-cubes.html#984" class="Bound">d</a><a id="1201" class="Symbol">}</a>
                    <a id="1223" class="Symbol">{</a> <a id="1225" href="univalent-combinatorics.orientations-cubes.html#797" class="Bound">y</a> <a id="1227" href="univalent-combinatorics.orientations-cubes.html#984" class="Bound">d</a><a id="1228" class="Symbol">})</a>
                    <a id="1251" class="Symbol">(</a> <a id="1253" href="univalent-combinatorics.finite-types.html#5504" class="Function">is-finite-empty</a><a id="1268" class="Symbol">))))</a>
            <a id="1285" class="Symbol">(</a> <a id="1287" href="univalent-combinatorics.standard-finite-types.html#6352" class="Function">succ-Fin</a> <a id="1296" class="Number">2</a><a id="1297" class="Symbol">)</a>
            <a id="1311" class="Symbol">(</a> <a id="1313" href="univalent-combinatorics.orientations-cubes.html#783" class="Bound">h</a> <a id="1315" href="univalent-combinatorics.orientations-cubes.html#795" class="Bound">x</a><a id="1316" class="Symbol">))</a>
          <a id="1329" class="Symbol">(</a> <a id="1331" href="univalent-combinatorics.orientations-cubes.html#783" class="Bound">h</a> <a id="1333" href="univalent-combinatorics.orientations-cubes.html#797" class="Bound">y</a><a id="1334" class="Symbol">))</a>
</pre>