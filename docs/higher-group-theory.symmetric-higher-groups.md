# Symmetric higher groups

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="higher-group-theory.symmetric-higher-groups.html" class="Module">higher-group-theory.symmetric-higher-groups</a> <a id="87" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="143" class="Keyword">open</a> <a id="148" class="Keyword">import</a> <a id="155" href="foundation.0-connected-types.html" class="Module">foundation.0-connected-types</a>
<a id="184" class="Keyword">open</a> <a id="189" class="Keyword">import</a> <a id="196" href="foundation.connected-components-universes.html" class="Module">foundation.connected-components-universes</a>
<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="282" class="Keyword">open</a> <a id="287" class="Keyword">import</a> <a id="294" href="foundation.mere-equivalences.html" class="Module">foundation.mere-equivalences</a>
<a id="323" class="Keyword">open</a> <a id="328" class="Keyword">import</a> <a id="335" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="363" class="Keyword">open</a> <a id="368" class="Keyword">import</a> <a id="375" href="higher-group-theory.higher-groups.html" class="Module">higher-group-theory.higher-groups</a>

<a id="410" class="Keyword">open</a> <a id="415" class="Keyword">import</a> <a id="422" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

The symmetric higher group of a type `X` is the connected component of the
universe at `X`.

## Definition

<pre class="Agda"><a id="595" class="Keyword">module</a> <a id="602" href="higher-group-theory.symmetric-higher-groups.html#602" class="Module">_</a>
  <a id="606" class="Symbol">{</a><a id="607" href="higher-group-theory.symmetric-higher-groups.html#607" class="Bound">l</a> <a id="609" class="Symbol">:</a> <a id="611" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="616" class="Symbol">}</a> <a id="618" class="Symbol">(</a><a id="619" href="higher-group-theory.symmetric-higher-groups.html#619" class="Bound">X</a> <a id="621" class="Symbol">:</a> <a id="623" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="626" href="higher-group-theory.symmetric-higher-groups.html#607" class="Bound">l</a><a id="627" class="Symbol">)</a>
  <a id="631" class="Keyword">where</a>

  <a id="640" href="higher-group-theory.symmetric-higher-groups.html#640" class="Function">classifying-type-symmetric-∞-Group</a> <a id="675" class="Symbol">:</a> <a id="677" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="680" class="Symbol">(</a><a id="681" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="686" href="higher-group-theory.symmetric-higher-groups.html#607" class="Bound">l</a><a id="687" class="Symbol">)</a>
  <a id="691" href="higher-group-theory.symmetric-higher-groups.html#640" class="Function">classifying-type-symmetric-∞-Group</a> <a id="726" class="Symbol">=</a> <a id="728" href="foundation.connected-components-universes.html#1854" class="Function">component-UU</a> <a id="741" href="higher-group-theory.symmetric-higher-groups.html#619" class="Bound">X</a>

  <a id="746" href="higher-group-theory.symmetric-higher-groups.html#746" class="Function">shape-symmetric-∞-Group</a> <a id="770" class="Symbol">:</a> <a id="772" href="higher-group-theory.symmetric-higher-groups.html#640" class="Function">classifying-type-symmetric-∞-Group</a>
  <a id="809" href="higher-group-theory.symmetric-higher-groups.html#746" class="Function">shape-symmetric-∞-Group</a> <a id="833" class="Symbol">=</a>
    <a id="839" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="844" href="higher-group-theory.symmetric-higher-groups.html#619" class="Bound">X</a> <a id="846" class="Symbol">(</a><a id="847" href="foundation.mere-equivalences.html#1316" class="Function">refl-mere-equiv</a> <a id="863" href="higher-group-theory.symmetric-higher-groups.html#619" class="Bound">X</a><a id="864" class="Symbol">)</a>

  <a id="869" href="higher-group-theory.symmetric-higher-groups.html#869" class="Function">classifying-pointed-type-symmetric-∞-Group</a> <a id="912" class="Symbol">:</a> <a id="914" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="927" class="Symbol">(</a><a id="928" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="933" href="higher-group-theory.symmetric-higher-groups.html#607" class="Bound">l</a><a id="934" class="Symbol">)</a>
  <a id="938" href="higher-group-theory.symmetric-higher-groups.html#869" class="Function">classifying-pointed-type-symmetric-∞-Group</a> <a id="981" class="Symbol">=</a>
    <a id="987" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a>
      <a id="998" href="higher-group-theory.symmetric-higher-groups.html#640" class="Function">classifying-type-symmetric-∞-Group</a>
      <a id="1039" href="higher-group-theory.symmetric-higher-groups.html#746" class="Function">shape-symmetric-∞-Group</a>

  <a id="1066" href="higher-group-theory.symmetric-higher-groups.html#1066" class="Function">is-0-connected-classifying-type-symmetric-∞-Group</a> <a id="1116" class="Symbol">:</a>
    <a id="1122" href="foundation.0-connected-types.html#1548" class="Function">is-0-connected</a> <a id="1137" href="higher-group-theory.symmetric-higher-groups.html#640" class="Function">classifying-type-symmetric-∞-Group</a>
  <a id="1174" href="higher-group-theory.symmetric-higher-groups.html#1066" class="Function">is-0-connected-classifying-type-symmetric-∞-Group</a> <a id="1224" class="Symbol">=</a>
    <a id="1230" href="foundation.connected-components-universes.html#5826" class="Function">is-0-connected-component-UU</a> <a id="1258" href="higher-group-theory.symmetric-higher-groups.html#619" class="Bound">X</a>

  <a id="1263" href="higher-group-theory.symmetric-higher-groups.html#1263" class="Function">symmetric-∞-Group</a> <a id="1281" class="Symbol">:</a> <a id="1283" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a> <a id="1291" class="Symbol">(</a><a id="1292" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1297" href="higher-group-theory.symmetric-higher-groups.html#607" class="Bound">l</a><a id="1298" class="Symbol">)</a>
  <a id="1302" href="higher-group-theory.symmetric-higher-groups.html#1263" class="Function">symmetric-∞-Group</a> <a id="1320" class="Symbol">=</a>
    <a id="1326" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a>
      <a id="1337" href="higher-group-theory.symmetric-higher-groups.html#869" class="Function">classifying-pointed-type-symmetric-∞-Group</a>
      <a id="1386" href="higher-group-theory.symmetric-higher-groups.html#1066" class="Function">is-0-connected-classifying-type-symmetric-∞-Group</a>
</pre>