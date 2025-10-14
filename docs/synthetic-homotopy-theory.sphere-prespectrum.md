# The sphere prespectrum

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="synthetic-homotopy-theory.sphere-prespectrum.html" class="Module">synthetic-homotopy-theory.sphere-prespectrum</a> <a id="87" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="143" class="Keyword">open</a> <a id="148" class="Keyword">import</a> <a id="155" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="187" class="Keyword">open</a> <a id="192" class="Keyword">import</a> <a id="199" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="synthetic-homotopy-theory.prespectra.html" class="Module">synthetic-homotopy-theory.prespectra</a>
<a id="276" class="Keyword">open</a> <a id="281" class="Keyword">import</a> <a id="288" href="synthetic-homotopy-theory.suspension-prespectra.html" class="Module">synthetic-homotopy-theory.suspension-prespectra</a>

<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

The [spheres](synthetic-homotopy-theory.spheres.md) `Sⁿ` define a
[prespectrum](synthetic-homotopy-theory.prespectra.md)

```text
  Sⁿ →∗ ΩSⁿ⁺¹
```

which we call the **sphere prespectrum**.

**Note:** Even though the sphere prespectrum is defined degreewise by the
adjoint to the identity map, it is not in general a
[spectrum](synthetic-homotopy-theory.spectra.md), as the transposing map of the
[loop-suspension adjunction](synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types.md)
does not generally send [equivalences](foundation-core.equivalences.md) to
equivalences.

## Definition

### The sphere prespectrum

<pre class="Agda"><a id="sphere-Prespectrum"></a><a id="1067" href="synthetic-homotopy-theory.sphere-prespectrum.html#1067" class="Function">sphere-Prespectrum</a> <a id="1086" class="Symbol">:</a> <a id="1088" href="synthetic-homotopy-theory.prespectra.html#1274" class="Function">Prespectrum</a> <a id="1100" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1106" href="synthetic-homotopy-theory.sphere-prespectrum.html#1067" class="Function">sphere-Prespectrum</a> <a id="1125" class="Symbol">=</a> <a id="1127" href="synthetic-homotopy-theory.suspension-prespectra.html#2345" class="Function">suspension-Prespectrum</a> <a id="1150" class="Symbol">(</a><a id="1151" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="1155" class="Number">2</a> <a id="1157" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1159" href="univalent-combinatorics.standard-finite-types.html#5750" class="Function">zero-Fin</a> <a id="1168" class="Number">1</a><a id="1169" class="Symbol">)</a>
</pre>