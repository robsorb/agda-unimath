# The universal globular type

<pre class="Agda"><a id="40" class="Symbol">{-#</a> <a id="44" class="Keyword">OPTIONS</a> <a id="52" class="Pragma">--guardedness</a> <a id="66" class="Symbol">#-}</a>

<a id="71" class="Keyword">module</a> <a id="78" href="globular-types.universal-globular-type.html" class="Module">globular-types.universal-globular-type</a> <a id="117" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="173" class="Keyword">open</a> <a id="178" class="Keyword">import</a> <a id="185" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="217" class="Keyword">open</a> <a id="222" class="Keyword">import</a> <a id="229" href="foundation.spans.html" class="Module">foundation.spans</a>
<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="globular-types.dependent-globular-types.html" class="Module">globular-types.dependent-globular-types</a>
<a id="338" class="Keyword">open</a> <a id="343" class="Keyword">import</a> <a id="350" href="globular-types.exponentials-globular-types.html" class="Module">globular-types.exponentials-globular-types</a>
<a id="393" class="Keyword">open</a> <a id="398" class="Keyword">import</a> <a id="405" href="globular-types.globular-maps.html" class="Module">globular-types.globular-maps</a>
<a id="434" class="Keyword">open</a> <a id="439" class="Keyword">import</a> <a id="446" href="globular-types.globular-types.html" class="Module">globular-types.globular-types</a>
</pre>
</details>

## Idea

The {{#concept "universal globular type"}} `𝒢 l` at
[universe level](foundation.universe-levels.md) `l` has the universe `UU l` as
its type of `0`-cells, and uses iterated binary relations for its globular
structure.

Specifically, the universal globular type is a translation from category theory
into type theory of the Hofmann–Streicher universe {{#cite Awodey22}} of
presheaves on the globular category `Γ`

```text
      s₀       s₁       s₂
    ----->   ----->   ----->
  0 -----> 1 -----> 2 -----> ⋯.
      t₀       t₁       t₂
```

The Hofmann–Streicher universe of presheaves on a category `𝒞` is the presheaf

```text
     𝒰_𝒞 I := Presheaf 𝒞/I
  El_𝒞 I A := A *,
```

where `*` is the terminal object of `𝒞/I`, i.e., the identity morphism on `I`.

We compute a few instances of the slice category `Γ/I`:

- The slice category `Γ/0` is the terminal category.
- The slice category `Γ/1` is the representing cospan

  ```text
         s₀       t₀
    s₀ -----> 1 <----- t₀
  ```

  The functors `s₀ t₀ : Γ/0 → Γ/1` are given by `* ↦ s₀` and `* ↦ t₀`,
  respectively.

- The slice category `Γ/2` is the free category on the graph

  ```text
    s₁s₀             t₁s₀
     |                 |
     |                 |
     ∨                 ∨
    s₁ -----> 1 <----- t₁
     ∧                 ∧
     |                 |
     |                 |
    s₁t₀             t₁t₀
  ```

  and so on. The functors `s₁ t₁ : Γ/1 → Γ/2` are given by

  ```text
    s₀ ↦ s₁s₀                   s₀ ↦ t₁s₀
     1 ↦ s₁           and        1 ↦ t₁
    t₀ ↦ s₁t₀                   t₀ ↦ t₁t₀
  ```

  respectively.

More specifically, the slice category `Γ/n` is isomorphic to the iterated
suspension `Σⁿ1` of the terminal category.

This means that:

- The type `0`-cells of the universal globular type is the universe of types
  `UU l`.
- The type of `1`-cells from `X` to `Y` of the universal globular type is the
  type of spans from `X` to `Y`.
- The type of `2`-cells between any two spans `R` and `S` from `X` to `Y` is the
  type of families of spans from `R x y` to `S x y` indexed by `x : X` and
  `y : Y`, and so on.

In other words, the universal globular type `𝒰` has the universe of types as its
type of `0`-cells, and for any two types `X` and `Y`, the globular type of
`1`-cells is the double
[exponent](globular-types.exponentials-globular-types.md) `(𝒰^Y)^X` of globular
types.

Unfortunately, the termination checking algorithm isn't able to establish that
this definition is terminating. Nevertheless, when termination checking is
turned off for this definition, the types of the `n`-cells come out correctly
for low values of `n`.

## Definitions

### The universal globular type

<pre class="Agda"><a id="0-cell-universal-Globular-Type"></a><a id="3197" href="globular-types.universal-globular-type.html#3197" class="Function">0-cell-universal-Globular-Type</a> <a id="3228" class="Symbol">:</a> <a id="3230" class="Symbol">(</a><a id="3231" href="globular-types.universal-globular-type.html#3231" class="Bound">l1</a> <a id="3234" href="globular-types.universal-globular-type.html#3234" class="Bound">l2</a> <a id="3237" class="Symbol">:</a> <a id="3239" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3244" class="Symbol">)</a> <a id="3246" class="Symbol">→</a> <a id="3248" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3251" class="Symbol">(</a><a id="3252" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3257" href="globular-types.universal-globular-type.html#3231" class="Bound">l1</a><a id="3259" class="Symbol">)</a>
<a id="3261" href="globular-types.universal-globular-type.html#3197" class="Function">0-cell-universal-Globular-Type</a> <a id="3292" href="globular-types.universal-globular-type.html#3292" class="Bound">l1</a> <a id="3295" href="globular-types.universal-globular-type.html#3295" class="Bound">l2</a> <a id="3298" class="Symbol">=</a> <a id="3300" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3303" href="globular-types.universal-globular-type.html#3292" class="Bound">l1</a>

<a id="3307" class="Symbol">{-#</a> <a id="3311" class="Keyword">TERMINATING</a> <a id="3323" class="Symbol">#-}</a>

<a id="universal-Globular-Type"></a><a id="3328" href="globular-types.universal-globular-type.html#3328" class="Function">universal-Globular-Type</a> <a id="3352" class="Symbol">:</a>
  <a id="3356" class="Symbol">(</a><a id="3357" href="globular-types.universal-globular-type.html#3357" class="Bound">l1</a> <a id="3360" href="globular-types.universal-globular-type.html#3360" class="Bound">l2</a> <a id="3363" class="Symbol">:</a> <a id="3365" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3370" class="Symbol">)</a> <a id="3372" class="Symbol">→</a> <a id="3374" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="3388" class="Symbol">(</a><a id="3389" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3394" href="globular-types.universal-globular-type.html#3357" class="Bound">l1</a><a id="3396" class="Symbol">)</a> <a id="3398" class="Symbol">(</a><a id="3399" href="globular-types.universal-globular-type.html#3357" class="Bound">l1</a> <a id="3402" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3404" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3409" href="globular-types.universal-globular-type.html#3360" class="Bound">l2</a><a id="3411" class="Symbol">)</a>
<a id="3413" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="3434" class="Symbol">(</a><a id="3435" href="globular-types.universal-globular-type.html#3328" class="Function">universal-Globular-Type</a> <a id="3459" href="globular-types.universal-globular-type.html#3459" class="Bound">l1</a> <a id="3462" href="globular-types.universal-globular-type.html#3462" class="Bound">l2</a><a id="3464" class="Symbol">)</a> <a id="3466" class="Symbol">=</a>
  <a id="3470" href="globular-types.universal-globular-type.html#3197" class="Function">0-cell-universal-Globular-Type</a> <a id="3501" href="globular-types.universal-globular-type.html#3459" class="Bound">l1</a> <a id="3504" href="globular-types.universal-globular-type.html#3462" class="Bound">l2</a>
<a id="3507" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a> <a id="3542" class="Symbol">(</a><a id="3543" href="globular-types.universal-globular-type.html#3328" class="Function">universal-Globular-Type</a> <a id="3567" href="globular-types.universal-globular-type.html#3567" class="Bound">l1</a> <a id="3570" href="globular-types.universal-globular-type.html#3570" class="Bound">l2</a><a id="3572" class="Symbol">)</a> <a id="3574" href="globular-types.universal-globular-type.html#3574" class="Bound">X</a> <a id="3576" href="globular-types.universal-globular-type.html#3576" class="Bound">Y</a> <a id="3578" class="Symbol">=</a>
  <a id="3582" href="globular-types.exponentials-globular-types.html#1070" class="Function">exponential-Globular-Type</a> <a id="3608" href="globular-types.universal-globular-type.html#3574" class="Bound">X</a>
    <a id="3614" class="Symbol">(</a> <a id="3616" href="globular-types.exponentials-globular-types.html#1070" class="Function">exponential-Globular-Type</a> <a id="3642" href="globular-types.universal-globular-type.html#3576" class="Bound">Y</a> <a id="3644" class="Symbol">(</a><a id="3645" href="globular-types.universal-globular-type.html#3328" class="Function">universal-Globular-Type</a> <a id="3669" href="globular-types.universal-globular-type.html#3570" class="Bound">l2</a> <a id="3672" href="globular-types.universal-globular-type.html#3570" class="Bound">l2</a><a id="3674" class="Symbol">))</a>

<a id="1-cell-universal-Globular-Type"></a><a id="3678" href="globular-types.universal-globular-type.html#3678" class="Function">1-cell-universal-Globular-Type</a> <a id="3709" class="Symbol">:</a>
  <a id="3713" class="Symbol">{</a><a id="3714" href="globular-types.universal-globular-type.html#3714" class="Bound">l1</a> <a id="3717" href="globular-types.universal-globular-type.html#3717" class="Bound">l2</a> <a id="3720" class="Symbol">:</a> <a id="3722" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3727" class="Symbol">}</a> <a id="3729" class="Symbol">(</a><a id="3730" href="globular-types.universal-globular-type.html#3730" class="Bound">X</a> <a id="3732" href="globular-types.universal-globular-type.html#3732" class="Bound">Y</a> <a id="3734" class="Symbol">:</a> <a id="3736" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3739" href="globular-types.universal-globular-type.html#3714" class="Bound">l1</a><a id="3741" class="Symbol">)</a> <a id="3743" class="Symbol">→</a> <a id="3745" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3748" class="Symbol">(</a><a id="3749" href="globular-types.universal-globular-type.html#3714" class="Bound">l1</a> <a id="3752" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3754" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3759" href="globular-types.universal-globular-type.html#3717" class="Bound">l2</a><a id="3761" class="Symbol">)</a>
<a id="3763" href="globular-types.universal-globular-type.html#3678" class="Function">1-cell-universal-Globular-Type</a> <a id="3794" class="Symbol">{</a><a id="3795" href="globular-types.universal-globular-type.html#3795" class="Bound">l1</a><a id="3797" class="Symbol">}</a> <a id="3799" class="Symbol">{</a><a id="3800" href="globular-types.universal-globular-type.html#3800" class="Bound">l2</a><a id="3802" class="Symbol">}</a> <a id="3804" class="Symbol">=</a>
  <a id="3808" href="globular-types.globular-types.html#5823" class="Function">1-cell-Globular-Type</a> <a id="3829" class="Symbol">(</a><a id="3830" href="globular-types.universal-globular-type.html#3328" class="Function">universal-Globular-Type</a> <a id="3854" href="globular-types.universal-globular-type.html#3795" class="Bound">l1</a> <a id="3857" href="globular-types.universal-globular-type.html#3800" class="Bound">l2</a><a id="3859" class="Symbol">)</a>

<a id="2-cell-universal-Globular-Type"></a><a id="3862" href="globular-types.universal-globular-type.html#3862" class="Function">2-cell-universal-Globular-Type</a> <a id="3893" class="Symbol">:</a>
  <a id="3897" class="Symbol">{</a><a id="3898" href="globular-types.universal-globular-type.html#3898" class="Bound">l1</a> <a id="3901" href="globular-types.universal-globular-type.html#3901" class="Bound">l2</a> <a id="3904" class="Symbol">:</a> <a id="3906" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3911" class="Symbol">}</a> <a id="3913" class="Symbol">{</a><a id="3914" href="globular-types.universal-globular-type.html#3914" class="Bound">X</a> <a id="3916" href="globular-types.universal-globular-type.html#3916" class="Bound">Y</a> <a id="3918" class="Symbol">:</a> <a id="3920" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3923" href="globular-types.universal-globular-type.html#3898" class="Bound">l1</a><a id="3925" class="Symbol">}</a> <a id="3927" class="Symbol">(</a><a id="3928" href="globular-types.universal-globular-type.html#3928" class="Bound">R</a> <a id="3930" href="globular-types.universal-globular-type.html#3930" class="Bound">S</a> <a id="3932" class="Symbol">:</a> <a id="3934" href="globular-types.universal-globular-type.html#3914" class="Bound">X</a> <a id="3936" class="Symbol">→</a> <a id="3938" href="globular-types.universal-globular-type.html#3916" class="Bound">Y</a> <a id="3940" class="Symbol">→</a> <a id="3942" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3945" href="globular-types.universal-globular-type.html#3901" class="Bound">l2</a><a id="3947" class="Symbol">)</a> <a id="3949" class="Symbol">→</a> <a id="3951" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3954" class="Symbol">(</a><a id="3955" href="globular-types.universal-globular-type.html#3898" class="Bound">l1</a> <a id="3958" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3960" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3965" href="globular-types.universal-globular-type.html#3901" class="Bound">l2</a><a id="3967" class="Symbol">)</a>
<a id="3969" href="globular-types.universal-globular-type.html#3862" class="Function">2-cell-universal-Globular-Type</a> <a id="4000" class="Symbol">{</a><a id="4001" href="globular-types.universal-globular-type.html#4001" class="Bound">l1</a><a id="4003" class="Symbol">}</a> <a id="4005" class="Symbol">{</a><a id="4006" href="globular-types.universal-globular-type.html#4006" class="Bound">l2</a><a id="4008" class="Symbol">}</a> <a id="4010" class="Symbol">{</a><a id="4011" href="globular-types.universal-globular-type.html#4011" class="Bound">X</a><a id="4012" class="Symbol">}</a> <a id="4014" class="Symbol">{</a><a id="4015" href="globular-types.universal-globular-type.html#4015" class="Bound">Y</a><a id="4016" class="Symbol">}</a> <a id="4018" class="Symbol">=</a>
  <a id="4022" href="globular-types.globular-types.html#6027" class="Function">2-cell-Globular-Type</a> <a id="4043" class="Symbol">(</a><a id="4044" href="globular-types.universal-globular-type.html#3328" class="Function">universal-Globular-Type</a> <a id="4068" href="globular-types.universal-globular-type.html#4001" class="Bound">l1</a> <a id="4071" href="globular-types.universal-globular-type.html#4006" class="Bound">l2</a><a id="4073" class="Symbol">)</a>

<a id="3-cell-universal-Globular-Type"></a><a id="4076" href="globular-types.universal-globular-type.html#4076" class="Function">3-cell-universal-Globular-Type</a> <a id="4107" class="Symbol">:</a>
  <a id="4111" class="Symbol">{</a><a id="4112" href="globular-types.universal-globular-type.html#4112" class="Bound">l1</a> <a id="4115" href="globular-types.universal-globular-type.html#4115" class="Bound">l2</a> <a id="4118" class="Symbol">:</a> <a id="4120" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4125" class="Symbol">}</a> <a id="4127" class="Symbol">{</a><a id="4128" href="globular-types.universal-globular-type.html#4128" class="Bound">X</a> <a id="4130" href="globular-types.universal-globular-type.html#4130" class="Bound">Y</a> <a id="4132" class="Symbol">:</a> <a id="4134" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4137" href="globular-types.universal-globular-type.html#4112" class="Bound">l1</a><a id="4139" class="Symbol">}</a> <a id="4141" class="Symbol">{</a><a id="4142" href="globular-types.universal-globular-type.html#4142" class="Bound">R</a> <a id="4144" href="globular-types.universal-globular-type.html#4144" class="Bound">S</a> <a id="4146" class="Symbol">:</a> <a id="4148" href="globular-types.universal-globular-type.html#4128" class="Bound">X</a> <a id="4150" class="Symbol">→</a> <a id="4152" href="globular-types.universal-globular-type.html#4130" class="Bound">Y</a> <a id="4154" class="Symbol">→</a> <a id="4156" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4159" href="globular-types.universal-globular-type.html#4115" class="Bound">l2</a><a id="4161" class="Symbol">}</a>
  <a id="4165" class="Symbol">(</a><a id="4166" href="globular-types.universal-globular-type.html#4166" class="Bound">A</a> <a id="4168" href="globular-types.universal-globular-type.html#4168" class="Bound">B</a> <a id="4170" class="Symbol">:</a> <a id="4172" class="Symbol">(</a><a id="4173" href="globular-types.universal-globular-type.html#4173" class="Bound">x</a> <a id="4175" class="Symbol">:</a> <a id="4177" href="globular-types.universal-globular-type.html#4128" class="Bound">X</a><a id="4178" class="Symbol">)</a> <a id="4180" class="Symbol">(</a><a id="4181" href="globular-types.universal-globular-type.html#4181" class="Bound">y</a> <a id="4183" class="Symbol">:</a> <a id="4185" href="globular-types.universal-globular-type.html#4130" class="Bound">Y</a><a id="4186" class="Symbol">)</a> <a id="4188" class="Symbol">→</a> <a id="4190" href="globular-types.universal-globular-type.html#4142" class="Bound">R</a> <a id="4192" href="globular-types.universal-globular-type.html#4173" class="Bound">x</a> <a id="4194" href="globular-types.universal-globular-type.html#4181" class="Bound">y</a> <a id="4196" class="Symbol">→</a> <a id="4198" href="globular-types.universal-globular-type.html#4144" class="Bound">S</a> <a id="4200" href="globular-types.universal-globular-type.html#4173" class="Bound">x</a> <a id="4202" href="globular-types.universal-globular-type.html#4181" class="Bound">y</a> <a id="4204" class="Symbol">→</a> <a id="4206" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4209" href="globular-types.universal-globular-type.html#4115" class="Bound">l2</a><a id="4211" class="Symbol">)</a> <a id="4213" class="Symbol">→</a> <a id="4215" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4218" class="Symbol">(</a><a id="4219" href="globular-types.universal-globular-type.html#4112" class="Bound">l1</a> <a id="4222" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="4224" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="4229" href="globular-types.universal-globular-type.html#4115" class="Bound">l2</a><a id="4231" class="Symbol">)</a>
<a id="4233" href="globular-types.universal-globular-type.html#4076" class="Function">3-cell-universal-Globular-Type</a> <a id="4264" class="Symbol">{</a><a id="4265" href="globular-types.universal-globular-type.html#4265" class="Bound">l1</a><a id="4267" class="Symbol">}</a> <a id="4269" class="Symbol">{</a><a id="4270" href="globular-types.universal-globular-type.html#4270" class="Bound">l2</a><a id="4272" class="Symbol">}</a> <a id="4274" class="Symbol">=</a>
  <a id="4278" href="globular-types.globular-types.html#6264" class="Function">3-cell-Globular-Type</a> <a id="4299" class="Symbol">(</a><a id="4300" href="globular-types.universal-globular-type.html#3328" class="Function">universal-Globular-Type</a> <a id="4324" href="globular-types.universal-globular-type.html#4265" class="Bound">l1</a> <a id="4327" href="globular-types.universal-globular-type.html#4270" class="Bound">l2</a><a id="4329" class="Symbol">)</a>
</pre>
### Dependent globular types

#### Morphisms into the universal globular type induce dependent globular types

<pre class="Agda"><a id="0-cell-dependent-globular-type-hom-universal-Globular-Type"></a><a id="4455" href="globular-types.universal-globular-type.html#4455" class="Function">0-cell-dependent-globular-type-hom-universal-Globular-Type</a> <a id="4514" class="Symbol">:</a>
  <a id="4518" class="Symbol">{</a><a id="4519" href="globular-types.universal-globular-type.html#4519" class="Bound">l1</a> <a id="4522" href="globular-types.universal-globular-type.html#4522" class="Bound">l2</a> <a id="4525" href="globular-types.universal-globular-type.html#4525" class="Bound">l3</a> <a id="4528" href="globular-types.universal-globular-type.html#4528" class="Bound">l4</a> <a id="4531" class="Symbol">:</a> <a id="4533" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4538" class="Symbol">}</a> <a id="4540" class="Symbol">(</a><a id="4541" href="globular-types.universal-globular-type.html#4541" class="Bound">G</a> <a id="4543" class="Symbol">:</a> <a id="4545" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="4559" href="globular-types.universal-globular-type.html#4519" class="Bound">l1</a> <a id="4562" href="globular-types.universal-globular-type.html#4522" class="Bound">l2</a><a id="4564" class="Symbol">)</a>
  <a id="4568" class="Symbol">(</a><a id="4569" href="globular-types.universal-globular-type.html#4569" class="Bound">h</a> <a id="4571" class="Symbol">:</a> <a id="4573" href="globular-types.globular-maps.html#774" class="Record">globular-map</a> <a id="4586" href="globular-types.universal-globular-type.html#4541" class="Bound">G</a> <a id="4588" class="Symbol">(</a><a id="4589" href="globular-types.universal-globular-type.html#3328" class="Function">universal-Globular-Type</a> <a id="4613" href="globular-types.universal-globular-type.html#4525" class="Bound">l3</a> <a id="4616" href="globular-types.universal-globular-type.html#4528" class="Bound">l4</a><a id="4618" class="Symbol">))</a> <a id="4621" class="Symbol">→</a>
  <a id="4625" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="4646" href="globular-types.universal-globular-type.html#4541" class="Bound">G</a> <a id="4648" class="Symbol">→</a> <a id="4650" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4653" href="globular-types.universal-globular-type.html#4525" class="Bound">l3</a>
<a id="4656" href="globular-types.universal-globular-type.html#4455" class="Function">0-cell-dependent-globular-type-hom-universal-Globular-Type</a> <a id="4715" href="globular-types.universal-globular-type.html#4715" class="Bound">G</a> <a id="4717" href="globular-types.universal-globular-type.html#4717" class="Bound">h</a> <a id="4719" class="Symbol">=</a>
  <a id="4723" href="globular-types.globular-maps.html#928" class="Field">0-cell-globular-map</a> <a id="4743" href="globular-types.universal-globular-type.html#4717" class="Bound">h</a>

<a id="dependent-globular-type-hom-universal-Globular-Type"></a><a id="4746" href="globular-types.universal-globular-type.html#4746" class="Function">dependent-globular-type-hom-universal-Globular-Type</a> <a id="4798" class="Symbol">:</a>
  <a id="4802" class="Symbol">{</a><a id="4803" href="globular-types.universal-globular-type.html#4803" class="Bound">l1</a> <a id="4806" href="globular-types.universal-globular-type.html#4806" class="Bound">l2</a> <a id="4809" href="globular-types.universal-globular-type.html#4809" class="Bound">l3</a> <a id="4812" href="globular-types.universal-globular-type.html#4812" class="Bound">l4</a> <a id="4815" class="Symbol">:</a> <a id="4817" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4822" class="Symbol">}</a> <a id="4824" class="Symbol">(</a><a id="4825" href="globular-types.universal-globular-type.html#4825" class="Bound">G</a> <a id="4827" class="Symbol">:</a> <a id="4829" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="4843" href="globular-types.universal-globular-type.html#4803" class="Bound">l1</a> <a id="4846" href="globular-types.universal-globular-type.html#4806" class="Bound">l2</a><a id="4848" class="Symbol">)</a>
  <a id="4852" class="Symbol">(</a><a id="4853" href="globular-types.universal-globular-type.html#4853" class="Bound">h</a> <a id="4855" class="Symbol">:</a> <a id="4857" href="globular-types.globular-maps.html#774" class="Record">globular-map</a> <a id="4870" href="globular-types.universal-globular-type.html#4825" class="Bound">G</a> <a id="4872" class="Symbol">(</a><a id="4873" href="globular-types.universal-globular-type.html#3328" class="Function">universal-Globular-Type</a> <a id="4897" href="globular-types.universal-globular-type.html#4809" class="Bound">l3</a> <a id="4900" href="globular-types.universal-globular-type.html#4812" class="Bound">l4</a><a id="4902" class="Symbol">))</a> <a id="4905" class="Symbol">→</a>
  <a id="4909" href="globular-types.dependent-globular-types.html#778" class="Record">Dependent-Globular-Type</a> <a id="4933" href="globular-types.universal-globular-type.html#4809" class="Bound">l3</a> <a id="4936" href="globular-types.universal-globular-type.html#4812" class="Bound">l4</a> <a id="4939" href="globular-types.universal-globular-type.html#4825" class="Bound">G</a>
<a id="4941" href="globular-types.dependent-globular-types.html#937" class="Field">0-cell-Dependent-Globular-Type</a>
  <a id="4974" class="Symbol">(</a> <a id="4976" href="globular-types.universal-globular-type.html#4746" class="Function">dependent-globular-type-hom-universal-Globular-Type</a> <a id="5028" href="globular-types.universal-globular-type.html#5028" class="Bound">G</a> <a id="5030" href="globular-types.universal-globular-type.html#5030" class="Bound">h</a><a id="5031" class="Symbol">)</a> <a id="5033" class="Symbol">=</a>
  <a id="5037" href="globular-types.universal-globular-type.html#4455" class="Function">0-cell-dependent-globular-type-hom-universal-Globular-Type</a> <a id="5096" href="globular-types.universal-globular-type.html#5028" class="Bound">G</a> <a id="5098" href="globular-types.universal-globular-type.html#5030" class="Bound">h</a>
<a id="5100" href="globular-types.dependent-globular-types.html#1011" class="Field">1-cell-dependent-globular-type-Dependent-Globular-Type</a>
  <a id="5157" class="Symbol">(</a> <a id="5159" href="globular-types.universal-globular-type.html#4746" class="Function">dependent-globular-type-hom-universal-Globular-Type</a> <a id="5211" href="globular-types.universal-globular-type.html#5211" class="Bound">G</a> <a id="5213" href="globular-types.universal-globular-type.html#5213" class="Bound">h</a><a id="5214" class="Symbol">)</a>
  <a id="5218" class="Symbol">{</a><a id="5219" href="globular-types.universal-globular-type.html#5219" class="Bound">x</a><a id="5220" class="Symbol">}</a> <a id="5222" class="Symbol">{</a><a id="5223" href="globular-types.universal-globular-type.html#5223" class="Bound">x&#39;</a><a id="5225" class="Symbol">}</a> <a id="5227" href="globular-types.universal-globular-type.html#5227" class="Bound">y</a> <a id="5229" href="globular-types.universal-globular-type.html#5229" class="Bound">y&#39;</a> <a id="5232" class="Symbol">=</a>
  <a id="5236" href="globular-types.universal-globular-type.html#4746" class="Function">dependent-globular-type-hom-universal-Globular-Type</a>
    <a id="5292" class="Symbol">(</a> <a id="5294" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a> <a id="5329" href="globular-types.universal-globular-type.html#5211" class="Bound">G</a> <a id="5331" href="globular-types.universal-globular-type.html#5219" class="Bound">x</a> <a id="5333" href="globular-types.universal-globular-type.html#5223" class="Bound">x&#39;</a><a id="5335" class="Symbol">)</a>
    <a id="5341" class="Symbol">(</a> <a id="5343" href="globular-types.exponentials-globular-types.html#2030" class="Function">ev-hom-exponential-Globular-Type</a>
      <a id="5382" class="Symbol">(</a> <a id="5384" href="globular-types.exponentials-globular-types.html#2030" class="Function">ev-hom-exponential-Globular-Type</a>
        <a id="5425" class="Symbol">(</a> <a id="5427" href="globular-types.globular-maps.html#1009" class="Field">1-cell-globular-map-globular-map</a> <a id="5460" href="globular-types.universal-globular-type.html#5213" class="Bound">h</a> <a id="5462" class="Symbol">{</a><a id="5463" href="globular-types.universal-globular-type.html#5219" class="Bound">x</a><a id="5464" class="Symbol">}</a> <a id="5466" class="Symbol">{</a><a id="5467" href="globular-types.universal-globular-type.html#5223" class="Bound">x&#39;</a><a id="5469" class="Symbol">})</a>
        <a id="5480" class="Symbol">(</a> <a id="5482" href="globular-types.universal-globular-type.html#5227" class="Bound">y</a><a id="5483" class="Symbol">))</a>
      <a id="5492" class="Symbol">(</a> <a id="5494" href="globular-types.universal-globular-type.html#5229" class="Bound">y&#39;</a><a id="5496" class="Symbol">))</a>
</pre>
#### Dependent globular types induce morphisms into the universal globular type

<pre class="Agda"><a id="5593" class="Symbol">{-#</a> <a id="5597" class="Keyword">TERMINATING</a> <a id="5609" class="Symbol">#-}</a>

<a id="characteristic-globular-map-Dependent-Globular-Type"></a><a id="5614" href="globular-types.universal-globular-type.html#5614" class="Function">characteristic-globular-map-Dependent-Globular-Type</a> <a id="5666" class="Symbol">:</a>
  <a id="5670" class="Symbol">{</a><a id="5671" href="globular-types.universal-globular-type.html#5671" class="Bound">l1</a> <a id="5674" href="globular-types.universal-globular-type.html#5674" class="Bound">l2</a> <a id="5677" href="globular-types.universal-globular-type.html#5677" class="Bound">l3</a> <a id="5680" href="globular-types.universal-globular-type.html#5680" class="Bound">l4</a> <a id="5683" class="Symbol">:</a> <a id="5685" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5690" class="Symbol">}</a> <a id="5692" class="Symbol">{</a><a id="5693" href="globular-types.universal-globular-type.html#5693" class="Bound">G</a> <a id="5695" class="Symbol">:</a> <a id="5697" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="5711" href="globular-types.universal-globular-type.html#5671" class="Bound">l1</a> <a id="5714" href="globular-types.universal-globular-type.html#5674" class="Bound">l2</a><a id="5716" class="Symbol">}</a>
  <a id="5720" class="Symbol">(</a><a id="5721" href="globular-types.universal-globular-type.html#5721" class="Bound">H</a> <a id="5723" class="Symbol">:</a> <a id="5725" href="globular-types.dependent-globular-types.html#778" class="Record">Dependent-Globular-Type</a> <a id="5749" href="globular-types.universal-globular-type.html#5677" class="Bound">l3</a> <a id="5752" href="globular-types.universal-globular-type.html#5680" class="Bound">l4</a> <a id="5755" href="globular-types.universal-globular-type.html#5693" class="Bound">G</a><a id="5756" class="Symbol">)</a> <a id="5758" class="Symbol">→</a>
  <a id="5762" href="globular-types.globular-maps.html#774" class="Record">globular-map</a> <a id="5775" href="globular-types.universal-globular-type.html#5693" class="Bound">G</a> <a id="5777" class="Symbol">(</a><a id="5778" href="globular-types.universal-globular-type.html#3328" class="Function">universal-Globular-Type</a> <a id="5802" href="globular-types.universal-globular-type.html#5677" class="Bound">l3</a> <a id="5805" href="globular-types.universal-globular-type.html#5680" class="Bound">l4</a><a id="5807" class="Symbol">)</a>
<a id="5809" href="globular-types.globular-maps.html#928" class="Field">0-cell-globular-map</a>
  <a id="5831" class="Symbol">(</a> <a id="5833" href="globular-types.universal-globular-type.html#5614" class="Function">characteristic-globular-map-Dependent-Globular-Type</a> <a id="5885" class="Symbol">{</a><a id="5886" class="Argument">G</a> <a id="5888" class="Symbol">=</a> <a id="5890" href="globular-types.universal-globular-type.html#5890" class="Bound">G</a><a id="5891" class="Symbol">}</a> <a id="5893" href="globular-types.universal-globular-type.html#5893" class="Bound">H</a><a id="5894" class="Symbol">)</a> <a id="5896" class="Symbol">=</a>
  <a id="5900" href="globular-types.dependent-globular-types.html#937" class="Field">0-cell-Dependent-Globular-Type</a> <a id="5931" href="globular-types.universal-globular-type.html#5893" class="Bound">H</a>
<a id="5933" href="globular-types.globular-maps.html#1009" class="Field">1-cell-globular-map-globular-map</a>
  <a id="5968" class="Symbol">(</a> <a id="5970" href="globular-types.universal-globular-type.html#5614" class="Function">characteristic-globular-map-Dependent-Globular-Type</a> <a id="6022" class="Symbol">{</a><a id="6023" class="Argument">G</a> <a id="6025" class="Symbol">=</a> <a id="6027" href="globular-types.universal-globular-type.html#6027" class="Bound">G</a><a id="6028" class="Symbol">}</a> <a id="6030" href="globular-types.universal-globular-type.html#6030" class="Bound">H</a><a id="6031" class="Symbol">)</a> <a id="6033" class="Symbol">{</a><a id="6034" href="globular-types.universal-globular-type.html#6034" class="Bound">x</a><a id="6035" class="Symbol">}</a> <a id="6037" class="Symbol">{</a><a id="6038" href="globular-types.universal-globular-type.html#6038" class="Bound">x&#39;</a><a id="6040" class="Symbol">}</a> <a id="6042" class="Symbol">=</a>
  <a id="6046" href="globular-types.exponentials-globular-types.html#2362" class="Function">bind-family-globular-maps</a>
    <a id="6076" class="Symbol">(</a> <a id="6078" class="Symbol">λ</a> <a id="6080" href="globular-types.universal-globular-type.html#6080" class="Bound">y</a> <a id="6082" class="Symbol">→</a>
      <a id="6090" href="globular-types.exponentials-globular-types.html#2362" class="Function">bind-family-globular-maps</a>
        <a id="6124" class="Symbol">(</a> <a id="6126" class="Symbol">λ</a> <a id="6128" href="globular-types.universal-globular-type.html#6128" class="Bound">y&#39;</a> <a id="6131" class="Symbol">→</a>
          <a id="6143" href="globular-types.universal-globular-type.html#5614" class="Function">characteristic-globular-map-Dependent-Globular-Type</a>
            <a id="6207" class="Symbol">(</a> <a id="6209" href="globular-types.dependent-globular-types.html#1011" class="Field">1-cell-dependent-globular-type-Dependent-Globular-Type</a> <a id="6264" href="globular-types.universal-globular-type.html#6030" class="Bound">H</a> <a id="6266" href="globular-types.universal-globular-type.html#6080" class="Bound">y</a> <a id="6268" href="globular-types.universal-globular-type.html#6128" class="Bound">y&#39;</a><a id="6270" class="Symbol">)))</a>
</pre>
## References

{{#bibliography}}
