# Steiner triple systems

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="univalent-combinatorics.steiner-triple-systems.html" class="Module">univalent-combinatorics.steiner-triple-systems</a> <a id="89" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="145" class="Keyword">open</a> <a id="150" class="Keyword">import</a> <a id="157" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="239" class="Keyword">open</a> <a id="244" class="Keyword">import</a> <a id="251" href="univalent-combinatorics.steiner-systems.html" class="Module">univalent-combinatorics.steiner-systems</a>
</pre>
</details>

## Definition

<pre class="Agda"><a id="Steiner-Triple-System"></a><a id="331" href="univalent-combinatorics.steiner-triple-systems.html#331" class="Function">Steiner-Triple-System</a> <a id="353" class="Symbol">:</a> <a id="355" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="357" class="Symbol">→</a> <a id="359" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="362" class="Symbol">(</a><a id="363" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="368" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="373" class="Symbol">)</a>
<a id="375" href="univalent-combinatorics.steiner-triple-systems.html#331" class="Function">Steiner-Triple-System</a> <a id="397" href="univalent-combinatorics.steiner-triple-systems.html#397" class="Bound">n</a> <a id="399" class="Symbol">=</a> <a id="401" href="univalent-combinatorics.steiner-systems.html#794" class="Function">Steiner-System</a> <a id="416" class="Number">2</a> <a id="418" class="Number">3</a> <a id="420" href="univalent-combinatorics.steiner-triple-systems.html#397" class="Bound">n</a>
</pre>