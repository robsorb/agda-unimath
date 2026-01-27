# Characters

<pre class="Agda"><a id="23" class="Keyword">module</a> <a id="30" href="primitives.characters.html" class="Module">primitives.characters</a> <a id="52" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="108" class="Keyword">open</a> <a id="113" class="Keyword">import</a> <a id="120" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="162" class="Keyword">open</a> <a id="167" class="Keyword">import</a> <a id="174" href="foundation.booleans.html" class="Module">foundation.booleans</a>
<a id="194" class="Keyword">open</a> <a id="199" class="Keyword">import</a> <a id="206" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The `Char` type represents a character. Agda provides primitive functions to
manipulate them. Characters are written between single quotes, e.g. `'a'`.

## Definitions

<pre class="Agda"><a id="436" class="Keyword">postulate</a>
  <a id="Char"></a><a id="448" href="primitives.characters.html#448" class="Postulate">Char</a> <a id="453" class="Symbol">:</a> <a id="455" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="458" href="Agda.Primitive.html#915" class="Primitive">lzero</a>

<a id="465" class="Symbol">{-#</a> <a id="469" class="Keyword">BUILTIN</a> <a id="477" class="Keyword">CHAR</a> <a id="482" href="primitives.characters.html#448" class="Postulate">Char</a> <a id="487" class="Symbol">#-}</a>

<a id="492" class="Keyword">primitive</a>
  <a id="primIsLower"></a><a id="504" href="primitives.characters.html#504" class="Primitive">primIsLower</a> <a id="primIsDigit"></a><a id="516" href="primitives.characters.html#516" class="Primitive">primIsDigit</a> <a id="primIsAlpha"></a><a id="528" href="primitives.characters.html#528" class="Primitive">primIsAlpha</a> <a id="primIsSpace"></a><a id="540" href="primitives.characters.html#540" class="Primitive">primIsSpace</a> <a id="primIsAscii"></a><a id="552" href="primitives.characters.html#552" class="Primitive">primIsAscii</a>
    <a id="primIsLatin1"></a><a id="568" href="primitives.characters.html#568" class="Primitive">primIsLatin1</a> <a id="primIsPrint"></a><a id="581" href="primitives.characters.html#581" class="Primitive">primIsPrint</a> <a id="primIsHexDigit"></a><a id="593" href="primitives.characters.html#593" class="Primitive">primIsHexDigit</a> <a id="608" class="Symbol">:</a> <a id="610" href="primitives.characters.html#448" class="Postulate">Char</a> <a id="615" class="Symbol">→</a> <a id="617" href="foundation.booleans.html#1556" class="Datatype">bool</a>
  <a id="primToUpper"></a><a id="624" href="primitives.characters.html#624" class="Primitive">primToUpper</a> <a id="primToLower"></a><a id="636" href="primitives.characters.html#636" class="Primitive">primToLower</a> <a id="648" class="Symbol">:</a> <a id="650" href="primitives.characters.html#448" class="Postulate">Char</a> <a id="655" class="Symbol">→</a> <a id="657" href="primitives.characters.html#448" class="Postulate">Char</a>
  <a id="primCharToNat"></a><a id="664" href="primitives.characters.html#664" class="Primitive">primCharToNat</a> <a id="678" class="Symbol">:</a> <a id="680" href="primitives.characters.html#448" class="Postulate">Char</a> <a id="685" class="Symbol">→</a> <a id="687" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
  <a id="primNatToChar"></a><a id="691" href="primitives.characters.html#691" class="Primitive">primNatToChar</a> <a id="705" class="Symbol">:</a> <a id="707" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="709" class="Symbol">→</a> <a id="711" href="primitives.characters.html#448" class="Postulate">Char</a>
  <a id="primCharEquality"></a><a id="718" href="primitives.characters.html#718" class="Primitive">primCharEquality</a> <a id="735" class="Symbol">:</a> <a id="737" href="primitives.characters.html#448" class="Postulate">Char</a> <a id="742" class="Symbol">→</a> <a id="744" href="primitives.characters.html#448" class="Postulate">Char</a> <a id="749" class="Symbol">→</a> <a id="751" href="foundation.booleans.html#1556" class="Datatype">bool</a>
</pre>