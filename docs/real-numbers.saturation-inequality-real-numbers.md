# Saturation of inequality of real numbers

<pre class="Agda"><a id="53" class="Symbol">{-#</a> <a id="57" class="Keyword">OPTIONS</a> <a id="65" class="Pragma">--lossy-unification</a> <a id="85" class="Symbol">#-}</a>

<a id="90" class="Keyword">module</a> <a id="97" href="real-numbers.saturation-inequality-real-numbers.html" class="Module">real-numbers.saturation-inequality-real-numbers</a> <a id="145" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="201" class="Keyword">open</a> <a id="206" class="Keyword">import</a> <a id="213" href="elementary-number-theory.positive-rational-numbers.html" class="Module">elementary-number-theory.positive-rational-numbers</a>

<a id="265" class="Keyword">open</a> <a id="270" class="Keyword">import</a> <a id="277" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="305" class="Keyword">open</a> <a id="310" class="Keyword">import</a> <a id="317" href="real-numbers.addition-real-numbers.html" class="Module">real-numbers.addition-real-numbers</a>
<a id="352" class="Keyword">open</a> <a id="357" class="Keyword">import</a> <a id="364" href="real-numbers.dedekind-real-numbers.html" class="Module">real-numbers.dedekind-real-numbers</a>
<a id="399" class="Keyword">open</a> <a id="404" class="Keyword">import</a> <a id="411" href="real-numbers.inequality-real-numbers.html" class="Module">real-numbers.inequality-real-numbers</a>
<a id="448" class="Keyword">open</a> <a id="453" class="Keyword">import</a> <a id="460" href="real-numbers.rational-real-numbers.html" class="Module">real-numbers.rational-real-numbers</a>
<a id="495" class="Keyword">open</a> <a id="500" class="Keyword">import</a> <a id="507" href="real-numbers.strict-inequality-real-numbers.html" class="Module">real-numbers.strict-inequality-real-numbers</a>
</pre>
</details>

## Idea

If `x ≤ y + ε` for [real numbers](real-numbers.dedekind-real-numbers.md) `x` and
`y` and every
[positive rational](elementary-number-theory.positive-rational-numbers.md) `ε`,
then `x ≤ y`.

Despite being a property of
[inequality of real numbers](real-numbers.inequality-real-numbers.md), this is
much easier to prove via
[strict inequality](real-numbers.strict-inequality-real-numbers.md), so it is
moved to its own file to prevent circular dependency.

## Proof

<pre class="Agda"><a id="1050" class="Keyword">module</a> <a id="1057" href="real-numbers.saturation-inequality-real-numbers.html#1057" class="Module">_</a>
  <a id="1061" class="Symbol">{</a><a id="1062" href="real-numbers.saturation-inequality-real-numbers.html#1062" class="Bound">l1</a> <a id="1065" href="real-numbers.saturation-inequality-real-numbers.html#1065" class="Bound">l2</a> <a id="1068" class="Symbol">:</a> <a id="1070" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1075" class="Symbol">}</a> <a id="1077" class="Symbol">(</a><a id="1078" href="real-numbers.saturation-inequality-real-numbers.html#1078" class="Bound">x</a> <a id="1080" class="Symbol">:</a> <a id="1082" href="real-numbers.dedekind-real-numbers.html#4019" class="Function">ℝ</a> <a id="1084" href="real-numbers.saturation-inequality-real-numbers.html#1062" class="Bound">l1</a><a id="1086" class="Symbol">)</a> <a id="1088" class="Symbol">(</a><a id="1089" href="real-numbers.saturation-inequality-real-numbers.html#1089" class="Bound">y</a> <a id="1091" class="Symbol">:</a> <a id="1093" href="real-numbers.dedekind-real-numbers.html#4019" class="Function">ℝ</a> <a id="1095" href="real-numbers.saturation-inequality-real-numbers.html#1065" class="Bound">l2</a><a id="1097" class="Symbol">)</a>
  <a id="1101" class="Keyword">where</a>

  <a id="1110" class="Keyword">abstract</a>
    <a id="1123" href="real-numbers.saturation-inequality-real-numbers.html#1123" class="Function">saturated-leq-ℝ</a> <a id="1139" class="Symbol">:</a> <a id="1141" class="Symbol">((</a><a id="1143" href="real-numbers.saturation-inequality-real-numbers.html#1143" class="Bound">ε</a> <a id="1145" class="Symbol">:</a> <a id="1147" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a><a id="1149" class="Symbol">)</a> <a id="1151" class="Symbol">→</a> <a id="1153" href="real-numbers.inequality-real-numbers.html#2431" class="Function">leq-ℝ</a> <a id="1159" href="real-numbers.saturation-inequality-real-numbers.html#1078" class="Bound">x</a> <a id="1161" class="Symbol">(</a><a id="1162" href="real-numbers.saturation-inequality-real-numbers.html#1089" class="Bound">y</a> <a id="1164" href="real-numbers.addition-real-numbers.html#4848" class="Function Operator">+ℝ</a> <a id="1167" href="real-numbers.rational-real-numbers.html#2590" class="Function">real-ℚ⁺</a> <a id="1175" href="real-numbers.saturation-inequality-real-numbers.html#1143" class="Bound">ε</a><a id="1176" class="Symbol">))</a> <a id="1179" class="Symbol">→</a> <a id="1181" href="real-numbers.inequality-real-numbers.html#2431" class="Function">leq-ℝ</a> <a id="1187" href="real-numbers.saturation-inequality-real-numbers.html#1078" class="Bound">x</a> <a id="1189" href="real-numbers.saturation-inequality-real-numbers.html#1089" class="Bound">y</a>
    <a id="1195" href="real-numbers.saturation-inequality-real-numbers.html#1123" class="Function">saturated-leq-ℝ</a> <a id="1211" href="real-numbers.saturation-inequality-real-numbers.html#1211" class="Bound">H</a> <a id="1213" class="Symbol">=</a>
      <a id="1221" href="real-numbers.strict-inequality-real-numbers.html#20556" class="Function">saturated-le-ℝ</a> <a id="1236" href="real-numbers.saturation-inequality-real-numbers.html#1078" class="Bound">x</a> <a id="1238" href="real-numbers.saturation-inequality-real-numbers.html#1089" class="Bound">y</a>
        <a id="1248" class="Symbol">(</a> <a id="1250" class="Symbol">λ</a> <a id="1252" href="real-numbers.saturation-inequality-real-numbers.html#1252" class="Bound">ε</a> <a id="1254" class="Symbol">→</a>
          <a id="1266" href="real-numbers.strict-inequality-real-numbers.html#5693" class="Function">concatenate-leq-le-ℝ</a>
            <a id="1299" class="Symbol">(</a> <a id="1301" href="real-numbers.saturation-inequality-real-numbers.html#1078" class="Bound">x</a><a id="1302" class="Symbol">)</a>
            <a id="1316" class="Symbol">(</a> <a id="1318" href="real-numbers.saturation-inequality-real-numbers.html#1089" class="Bound">y</a> <a id="1320" href="real-numbers.addition-real-numbers.html#4848" class="Function Operator">+ℝ</a> <a id="1323" href="real-numbers.rational-real-numbers.html#2590" class="Function">real-ℚ⁺</a> <a id="1331" class="Symbol">(</a><a id="1332" href="elementary-number-theory.positive-rational-numbers.html#25353" class="Function">mediant-zero-ℚ⁺</a> <a id="1348" href="real-numbers.saturation-inequality-real-numbers.html#1252" class="Bound">ε</a><a id="1349" class="Symbol">))</a>
            <a id="1364" class="Symbol">(</a> <a id="1366" href="real-numbers.saturation-inequality-real-numbers.html#1089" class="Bound">y</a> <a id="1368" href="real-numbers.addition-real-numbers.html#4848" class="Function Operator">+ℝ</a> <a id="1371" href="real-numbers.rational-real-numbers.html#2590" class="Function">real-ℚ⁺</a> <a id="1379" href="real-numbers.saturation-inequality-real-numbers.html#1252" class="Bound">ε</a><a id="1380" class="Symbol">)</a>
            <a id="1394" class="Symbol">(</a> <a id="1396" href="real-numbers.saturation-inequality-real-numbers.html#1211" class="Bound">H</a> <a id="1398" class="Symbol">(</a><a id="1399" href="elementary-number-theory.positive-rational-numbers.html#25353" class="Function">mediant-zero-ℚ⁺</a> <a id="1415" href="real-numbers.saturation-inequality-real-numbers.html#1252" class="Bound">ε</a><a id="1416" class="Symbol">))</a>
            <a id="1431" class="Symbol">(</a> <a id="1433" href="real-numbers.strict-inequality-real-numbers.html#14985" class="Function">preserves-le-left-add-ℝ</a>
              <a id="1471" class="Symbol">(</a> <a id="1473" href="real-numbers.saturation-inequality-real-numbers.html#1089" class="Bound">y</a><a id="1474" class="Symbol">)</a>
              <a id="1490" class="Symbol">(</a> <a id="1492" href="real-numbers.rational-real-numbers.html#2590" class="Function">real-ℚ⁺</a> <a id="1500" class="Symbol">(</a><a id="1501" href="elementary-number-theory.positive-rational-numbers.html#25353" class="Function">mediant-zero-ℚ⁺</a> <a id="1517" href="real-numbers.saturation-inequality-real-numbers.html#1252" class="Bound">ε</a><a id="1518" class="Symbol">))</a>
              <a id="1535" class="Symbol">(</a> <a id="1537" href="real-numbers.rational-real-numbers.html#2590" class="Function">real-ℚ⁺</a> <a id="1545" href="real-numbers.saturation-inequality-real-numbers.html#1252" class="Bound">ε</a><a id="1546" class="Symbol">)</a>
              <a id="1562" class="Symbol">(</a> <a id="1564" href="real-numbers.strict-inequality-real-numbers.html#4792" class="Function">preserves-le-real-ℚ</a> <a id="1584" class="Symbol">_</a> <a id="1586" class="Symbol">_</a> <a id="1588" class="Symbol">(</a><a id="1589" href="elementary-number-theory.positive-rational-numbers.html#25673" class="Function">le-mediant-zero-ℚ⁺</a> <a id="1608" href="real-numbers.saturation-inequality-real-numbers.html#1252" class="Bound">ε</a><a id="1609" class="Symbol">))))</a>
</pre>