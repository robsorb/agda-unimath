# The dihedral groups

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="group-theory.dihedral-groups.html" class="Module">group-theory.dihedral-groups</a> <a id="68" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="124" class="Keyword">open</a> <a id="129" class="Keyword">import</a> <a id="136" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="177" class="Keyword">open</a> <a id="182" class="Keyword">import</a> <a id="189" href="elementary-number-theory.standard-cyclic-groups.html" class="Module">elementary-number-theory.standard-cyclic-groups</a>

<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="278" class="Keyword">open</a> <a id="283" class="Keyword">import</a> <a id="290" href="group-theory.dihedral-group-construction.html" class="Module">group-theory.dihedral-group-construction</a>
<a id="331" class="Keyword">open</a> <a id="336" class="Keyword">import</a> <a id="343" href="group-theory.groups.html" class="Module">group-theory.groups</a>
</pre>
</details>

## Idea

The dihedral group `Dₖ` is defined by the dihedral group construction applied to
the cyclic group `ℤ-Mod k`.

## Definition

<pre class="Agda"><a id="dihedral-group"></a><a id="522" href="group-theory.dihedral-groups.html#522" class="Function">dihedral-group</a> <a id="537" class="Symbol">:</a> <a id="539" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="541" class="Symbol">→</a> <a id="543" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="549" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="555" href="group-theory.dihedral-groups.html#522" class="Function">dihedral-group</a> <a id="570" href="group-theory.dihedral-groups.html#570" class="Bound">k</a> <a id="572" class="Symbol">=</a> <a id="574" href="group-theory.dihedral-group-construction.html#5321" class="Function">dihedral-group-Ab</a> <a id="592" class="Symbol">(</a><a id="593" href="elementary-number-theory.standard-cyclic-groups.html#1702" class="Function">ℤ-Mod-Ab</a> <a id="602" href="group-theory.dihedral-groups.html#570" class="Bound">k</a><a id="603" class="Symbol">)</a>
</pre>