# The higher group of integers

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="higher-group-theory.integers-higher-group.html" class="Module">higher-group-theory.integers-higher-group</a> <a id="90" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="146" class="Keyword">open</a> <a id="151" class="Keyword">import</a> <a id="158" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="190" class="Keyword">open</a> <a id="195" class="Keyword">import</a> <a id="202" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="230" class="Keyword">open</a> <a id="235" class="Keyword">import</a> <a id="242" href="higher-group-theory.higher-groups.html" class="Module">higher-group-theory.higher-groups</a>

<a id="277" class="Keyword">open</a> <a id="282" class="Keyword">import</a> <a id="289" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>

<a id="321" class="Keyword">open</a> <a id="326" class="Keyword">import</a> <a id="333" href="synthetic-homotopy-theory.circle.html" class="Module">synthetic-homotopy-theory.circle</a>
</pre>
</details>

## Idea

The **higher group of integers** is defined to be the
[circle](synthetic-homotopy-theory.circle.md). The
[loop space](synthetic-homotopy-theory.loop-spaces.md) of the circle is
[`ℤ`](elementary-number-theory.integers.md).

## Definition

<pre class="Agda"><a id="638" class="Keyword">module</a> <a id="645" href="higher-group-theory.integers-higher-group.html#645" class="Module">_</a>
  <a id="649" class="Keyword">where</a>

  <a id="658" href="higher-group-theory.integers-higher-group.html#658" class="Function">classifying-type-ℤ-∞-Group</a> <a id="685" class="Symbol">:</a> <a id="687" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="690" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="698" href="higher-group-theory.integers-higher-group.html#658" class="Function">classifying-type-ℤ-∞-Group</a> <a id="725" class="Symbol">=</a> <a id="727" href="synthetic-homotopy-theory.circle.html#1827" class="Postulate">𝕊¹</a>

  <a id="733" href="higher-group-theory.integers-higher-group.html#733" class="Function">shape-ℤ-∞-Group</a> <a id="749" class="Symbol">:</a> <a id="751" href="synthetic-homotopy-theory.circle.html#1827" class="Postulate">𝕊¹</a>
  <a id="756" href="higher-group-theory.integers-higher-group.html#733" class="Function">shape-ℤ-∞-Group</a> <a id="772" class="Symbol">=</a> <a id="774" href="synthetic-homotopy-theory.circle.html#1854" class="Postulate">base-𝕊¹</a>

  <a id="785" href="higher-group-theory.integers-higher-group.html#785" class="Function">classifying-pointed-type-ℤ-∞-Group</a> <a id="820" class="Symbol">:</a> <a id="822" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="835" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="843" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="847" href="higher-group-theory.integers-higher-group.html#785" class="Function">classifying-pointed-type-ℤ-∞-Group</a> <a id="882" class="Symbol">=</a> <a id="884" href="higher-group-theory.integers-higher-group.html#658" class="Function">classifying-type-ℤ-∞-Group</a>
  <a id="913" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="917" href="higher-group-theory.integers-higher-group.html#785" class="Function">classifying-pointed-type-ℤ-∞-Group</a> <a id="952" class="Symbol">=</a> <a id="954" href="higher-group-theory.integers-higher-group.html#733" class="Function">shape-ℤ-∞-Group</a>

  <a id="973" href="higher-group-theory.integers-higher-group.html#973" class="Function">ℤ-∞-Group</a> <a id="983" class="Symbol">:</a> <a id="985" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a> <a id="993" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="1001" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1005" href="higher-group-theory.integers-higher-group.html#973" class="Function">ℤ-∞-Group</a> <a id="1015" class="Symbol">=</a> <a id="1017" href="higher-group-theory.integers-higher-group.html#785" class="Function">classifying-pointed-type-ℤ-∞-Group</a>
  <a id="1054" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1058" href="higher-group-theory.integers-higher-group.html#973" class="Function">ℤ-∞-Group</a> <a id="1068" class="Symbol">=</a> <a id="1070" href="synthetic-homotopy-theory.circle.html#5861" class="Function">is-0-connected-𝕊¹</a>
</pre>