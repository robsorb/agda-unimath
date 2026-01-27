# Strings

<pre class="Agda"><a id="20" class="Keyword">module</a> <a id="27" href="primitives.strings.html" class="Module">primitives.strings</a> <a id="46" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="102" class="Keyword">open</a> <a id="107" class="Keyword">import</a> <a id="114" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="156" class="Keyword">open</a> <a id="161" class="Keyword">import</a> <a id="168" href="foundation.booleans.html" class="Module">foundation.booleans</a>
<a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="232" class="Keyword">open</a> <a id="237" class="Keyword">import</a> <a id="244" href="foundation.maybe.html" class="Module">foundation.maybe</a>
<a id="261" class="Keyword">open</a> <a id="266" class="Keyword">import</a> <a id="273" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="301" class="Keyword">open</a> <a id="306" class="Keyword">import</a> <a id="313" href="lists.lists.html" class="Module">lists.lists</a>

<a id="326" class="Keyword">open</a> <a id="331" class="Keyword">import</a> <a id="338" href="primitives.characters.html" class="Module">primitives.characters</a>
</pre>
</details>

## Idea

The `String` type represents strings. Agda provides primitive functions to
manipulate them. Strings are written between double quotes, e.g.
`"agda-unimath"`.

## Definitions

<pre class="Agda"><a id="569" class="Keyword">postulate</a>
  <a id="String"></a><a id="581" href="primitives.strings.html#581" class="Postulate">String</a> <a id="588" class="Symbol">:</a> <a id="590" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="593" href="Agda.Primitive.html#915" class="Primitive">lzero</a>

<a id="600" class="Symbol">{-#</a> <a id="604" class="Keyword">BUILTIN</a> <a id="612" class="Keyword">STRING</a> <a id="619" href="primitives.strings.html#581" class="Postulate">String</a> <a id="626" class="Symbol">#-}</a>

<a id="631" class="Keyword">primitive</a>
  <a id="primStringUncons"></a><a id="643" href="primitives.strings.html#643" class="Primitive">primStringUncons</a> <a id="660" class="Symbol">:</a> <a id="662" href="primitives.strings.html#581" class="Postulate">String</a> <a id="669" class="Symbol">→</a> <a id="671" href="foundation.maybe.html#2157" class="Datatype">Maybe&#39;</a> <a id="678" class="Symbol">(</a><a id="679" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="681" href="primitives.characters.html#448" class="Postulate">Char</a> <a id="686" class="Symbol">(λ</a> <a id="689" href="primitives.strings.html#689" class="Bound">_</a> <a id="691" class="Symbol">→</a> <a id="693" href="primitives.strings.html#581" class="Postulate">String</a><a id="699" class="Symbol">))</a>
  <a id="primStringToList"></a><a id="704" href="primitives.strings.html#704" class="Primitive">primStringToList</a> <a id="721" class="Symbol">:</a> <a id="723" href="primitives.strings.html#581" class="Postulate">String</a> <a id="730" class="Symbol">→</a> <a id="732" href="lists.lists.html#1328" class="Datatype">list</a> <a id="737" href="primitives.characters.html#448" class="Postulate">Char</a>
  <a id="primStringFromList"></a><a id="744" href="primitives.strings.html#744" class="Primitive">primStringFromList</a> <a id="763" class="Symbol">:</a> <a id="765" href="lists.lists.html#1328" class="Datatype">list</a> <a id="770" href="primitives.characters.html#448" class="Postulate">Char</a> <a id="775" class="Symbol">→</a> <a id="777" href="primitives.strings.html#581" class="Postulate">String</a>
  <a id="primStringAppend"></a><a id="786" href="primitives.strings.html#786" class="Primitive">primStringAppend</a> <a id="803" class="Symbol">:</a> <a id="805" href="primitives.strings.html#581" class="Postulate">String</a> <a id="812" class="Symbol">→</a> <a id="814" href="primitives.strings.html#581" class="Postulate">String</a> <a id="821" class="Symbol">→</a> <a id="823" href="primitives.strings.html#581" class="Postulate">String</a>
  <a id="primStringEquality"></a><a id="832" href="primitives.strings.html#832" class="Primitive">primStringEquality</a> <a id="851" class="Symbol">:</a> <a id="853" href="primitives.strings.html#581" class="Postulate">String</a> <a id="860" class="Symbol">→</a> <a id="862" href="primitives.strings.html#581" class="Postulate">String</a> <a id="869" class="Symbol">→</a> <a id="871" href="foundation.booleans.html#1556" class="Datatype">bool</a>
  <a id="primShowChar"></a><a id="878" href="primitives.strings.html#878" class="Primitive">primShowChar</a> <a id="891" class="Symbol">:</a> <a id="893" href="primitives.characters.html#448" class="Postulate">Char</a> <a id="898" class="Symbol">→</a> <a id="900" href="primitives.strings.html#581" class="Postulate">String</a>
  <a id="primShowString"></a><a id="909" href="primitives.strings.html#909" class="Primitive">primShowString</a> <a id="924" class="Symbol">:</a> <a id="926" href="primitives.strings.html#581" class="Postulate">String</a> <a id="933" class="Symbol">→</a> <a id="935" href="primitives.strings.html#581" class="Postulate">String</a>
  <a id="primShowNat"></a><a id="944" href="primitives.strings.html#944" class="Primitive">primShowNat</a> <a id="956" class="Symbol">:</a> <a id="958" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="960" class="Symbol">→</a> <a id="962" href="primitives.strings.html#581" class="Postulate">String</a>
</pre>