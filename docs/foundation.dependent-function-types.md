# Dependent function types

<pre class="Agda"><a id="37" class="Keyword">module</a> <a id="44" href="foundation.dependent-function-types.html" class="Module">foundation.dependent-function-types</a> <a id="80" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="136" class="Keyword">open</a> <a id="141" class="Keyword">import</a> <a id="148" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="180" class="Keyword">open</a> <a id="185" class="Keyword">import</a> <a id="192" href="foundation.spans-families-of-types.html" class="Module">foundation.spans-families-of-types</a>
<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="foundation.terminal-spans-families-of-types.html" class="Module">foundation.terminal-spans-families-of-types</a>
<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="foundation.type-arithmetic-dependent-function-types.html" class="Module">foundation.type-arithmetic-dependent-function-types</a>
<a id="347" class="Keyword">open</a> <a id="352" class="Keyword">import</a> <a id="359" href="foundation.universal-property-dependent-function-types.html" class="Module">foundation.universal-property-dependent-function-types</a>
<a id="414" class="Keyword">open</a> <a id="419" class="Keyword">import</a> <a id="426" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

Consider a family `B` of types over `A`. A {{#concept "dependent function"}}
that takes elements `x : A` to elements of type `B x` is an assignment of an
element `f x : B x` for each `x : A`. In Agda, dependent functions can be
written using `λ`-abstraction, i.e., using the syntax

```text
  λ x → f x.
```

Informally, we also use the notation `x ↦ f x` for the assignment of values of a
dependent function `f`.

The type of dependent function `(x : A) → B x` is built in to the kernel of
Agda, and doesn't need to be introduced by us. The purpose of this file is to
record some properties of dependent function types.

## Definitions

### The structure of a span on a family of types on a dependent function type

<pre class="Agda"><a id="1204" class="Keyword">module</a> <a id="1211" href="foundation.dependent-function-types.html#1211" class="Module">_</a>
  <a id="1215" class="Symbol">{</a><a id="1216" href="foundation.dependent-function-types.html#1216" class="Bound">l1</a> <a id="1219" href="foundation.dependent-function-types.html#1219" class="Bound">l2</a> <a id="1222" class="Symbol">:</a> <a id="1224" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1229" class="Symbol">}</a> <a id="1231" class="Symbol">{</a><a id="1232" href="foundation.dependent-function-types.html#1232" class="Bound">A</a> <a id="1234" class="Symbol">:</a> <a id="1236" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1239" href="foundation.dependent-function-types.html#1216" class="Bound">l1</a><a id="1241" class="Symbol">}</a> <a id="1243" class="Symbol">(</a><a id="1244" href="foundation.dependent-function-types.html#1244" class="Bound">B</a> <a id="1246" class="Symbol">:</a> <a id="1248" href="foundation.dependent-function-types.html#1232" class="Bound">A</a> <a id="1250" class="Symbol">→</a> <a id="1252" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1255" href="foundation.dependent-function-types.html#1219" class="Bound">l2</a><a id="1257" class="Symbol">)</a>
  <a id="1261" class="Keyword">where</a>

  <a id="1270" href="foundation.dependent-function-types.html#1270" class="Function">span-type-family-Π</a> <a id="1289" class="Symbol">:</a> <a id="1291" href="foundation.spans-families-of-types.html#839" class="Function">span-type-family</a> <a id="1308" class="Symbol">(</a><a id="1309" href="foundation.dependent-function-types.html#1216" class="Bound">l1</a> <a id="1312" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1314" href="foundation.dependent-function-types.html#1219" class="Bound">l2</a><a id="1316" class="Symbol">)</a> <a id="1318" href="foundation.dependent-function-types.html#1244" class="Bound">B</a>
  <a id="1322" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1326" href="foundation.dependent-function-types.html#1270" class="Function">span-type-family-Π</a> <a id="1345" class="Symbol">=</a> <a id="1347" class="Symbol">(</a><a id="1348" href="foundation.dependent-function-types.html#1348" class="Bound">x</a> <a id="1350" class="Symbol">:</a> <a id="1352" href="foundation.dependent-function-types.html#1232" class="Bound">A</a><a id="1353" class="Symbol">)</a> <a id="1355" class="Symbol">→</a> <a id="1357" href="foundation.dependent-function-types.html#1244" class="Bound">B</a> <a id="1359" href="foundation.dependent-function-types.html#1348" class="Bound">x</a>
  <a id="1363" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1367" href="foundation.dependent-function-types.html#1270" class="Function">span-type-family-Π</a> <a id="1386" href="foundation.dependent-function-types.html#1386" class="Bound">x</a> <a id="1388" href="foundation.dependent-function-types.html#1388" class="Bound">f</a> <a id="1390" class="Symbol">=</a> <a id="1392" href="foundation.dependent-function-types.html#1388" class="Bound">f</a> <a id="1394" href="foundation.dependent-function-types.html#1386" class="Bound">x</a>
</pre>
## Properties

### Dependent function types satisfy the universal property of dependent function types

<pre class="Agda"><a id="1513" class="Keyword">module</a> <a id="1520" href="foundation.dependent-function-types.html#1520" class="Module">_</a>
  <a id="1524" class="Symbol">{</a><a id="1525" href="foundation.dependent-function-types.html#1525" class="Bound">l1</a> <a id="1528" href="foundation.dependent-function-types.html#1528" class="Bound">l2</a> <a id="1531" class="Symbol">:</a> <a id="1533" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1538" class="Symbol">}</a> <a id="1540" class="Symbol">{</a><a id="1541" href="foundation.dependent-function-types.html#1541" class="Bound">A</a> <a id="1543" class="Symbol">:</a> <a id="1545" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1548" href="foundation.dependent-function-types.html#1525" class="Bound">l1</a><a id="1550" class="Symbol">}</a> <a id="1552" class="Symbol">(</a><a id="1553" href="foundation.dependent-function-types.html#1553" class="Bound">B</a> <a id="1555" class="Symbol">:</a> <a id="1557" href="foundation.dependent-function-types.html#1541" class="Bound">A</a> <a id="1559" class="Symbol">→</a> <a id="1561" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1564" href="foundation.dependent-function-types.html#1528" class="Bound">l2</a><a id="1566" class="Symbol">)</a>
  <a id="1570" class="Keyword">where</a>

  <a id="1579" class="Keyword">abstract</a>
    <a id="1592" href="foundation.dependent-function-types.html#1592" class="Function">universal-property-dependent-function-types-Π</a> <a id="1638" class="Symbol">:</a>
      <a id="1646" href="foundation.universal-property-dependent-function-types.html#2255" class="Function">universal-property-dependent-function-types</a> <a id="1690" class="Symbol">(</a><a id="1691" href="foundation.dependent-function-types.html#1270" class="Function">span-type-family-Π</a> <a id="1710" href="foundation.dependent-function-types.html#1553" class="Bound">B</a><a id="1711" class="Symbol">)</a>
    <a id="1717" href="foundation.dependent-function-types.html#1592" class="Function">universal-property-dependent-function-types-Π</a> <a id="1763" href="foundation.dependent-function-types.html#1763" class="Bound">T</a> <a id="1765" class="Symbol">=</a> <a id="1767" href="foundation.type-arithmetic-dependent-function-types.html#1405" class="Function">is-equiv-swap-Π</a>
</pre>
### Dependent function types are terminal spans on families of types

<pre class="Agda"><a id="1866" class="Keyword">module</a> <a id="1873" href="foundation.dependent-function-types.html#1873" class="Module">_</a>
  <a id="1877" class="Symbol">{</a><a id="1878" href="foundation.dependent-function-types.html#1878" class="Bound">l1</a> <a id="1881" href="foundation.dependent-function-types.html#1881" class="Bound">l2</a> <a id="1884" class="Symbol">:</a> <a id="1886" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1891" class="Symbol">}</a> <a id="1893" class="Symbol">{</a><a id="1894" href="foundation.dependent-function-types.html#1894" class="Bound">A</a> <a id="1896" class="Symbol">:</a> <a id="1898" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1901" href="foundation.dependent-function-types.html#1878" class="Bound">l1</a><a id="1903" class="Symbol">}</a> <a id="1905" class="Symbol">(</a><a id="1906" href="foundation.dependent-function-types.html#1906" class="Bound">B</a> <a id="1908" class="Symbol">:</a> <a id="1910" href="foundation.dependent-function-types.html#1894" class="Bound">A</a> <a id="1912" class="Symbol">→</a> <a id="1914" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1917" href="foundation.dependent-function-types.html#1881" class="Bound">l2</a><a id="1919" class="Symbol">)</a>
  <a id="1923" class="Keyword">where</a>

  <a id="1932" class="Keyword">abstract</a>
    <a id="1945" href="foundation.dependent-function-types.html#1945" class="Function">is-terminal-span-type-family-Π</a> <a id="1976" class="Symbol">:</a>
      <a id="1984" href="foundation.terminal-spans-families-of-types.html#929" class="Function">is-terminal-span-type-family</a> <a id="2013" class="Symbol">(</a><a id="2014" href="foundation.dependent-function-types.html#1270" class="Function">span-type-family-Π</a> <a id="2033" href="foundation.dependent-function-types.html#1906" class="Bound">B</a><a id="2034" class="Symbol">)</a>
    <a id="2040" href="foundation.dependent-function-types.html#1945" class="Function">is-terminal-span-type-family-Π</a> <a id="2071" class="Symbol">=</a>
      <a id="2079" href="foundation.universal-property-dependent-function-types.html#2677" class="Function">is-terminal-universal-property-dependent-function-types</a>
        <a id="2143" class="Symbol">(</a> <a id="2145" href="foundation.dependent-function-types.html#1270" class="Function">span-type-family-Π</a> <a id="2164" href="foundation.dependent-function-types.html#1906" class="Bound">B</a><a id="2165" class="Symbol">)</a>
        <a id="2175" class="Symbol">(</a> <a id="2177" href="foundation.dependent-function-types.html#1592" class="Function">universal-property-dependent-function-types-Π</a> <a id="2223" href="foundation.dependent-function-types.html#1906" class="Bound">B</a><a id="2224" class="Symbol">)</a>
</pre>
## See also

- [The globular type of dependent functions](foundation.globular-type-of-dependent-functions.md)
