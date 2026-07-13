# Formalización del Lema de Bombeo para Lenguajes Regulares en Lean 4

Este proyecto formaliza en **Lean 4** conceptos fundamentales de la teoría de autómatas y lenguajes formales. En particular, define los **autómatas finitos deterministas** o DFA, caracteriza los **lenguajes regulares** y demuestra formalmente el **Lema de Bombeo para Lenguajes Regulares**.

La demostración utiliza resultados de la biblioteca [`Mathlib`](https://github.com/leanprover-community/mathlib4), entre ellos el **principio del palomar**, para probar que toda palabra suficientemente larga aceptada por un DFA contiene un segmento que puede repetirse sin abandonar el lenguaje reconocido.

## Objetivos

Los objetivos principales del proyecto son:

* Representar formalmente un autómata finito determinista en Lean 4.
* Definir la ejecución de un DFA sobre palabras.
* Definir el lenguaje reconocido por un DFA.
* Caracterizar los lenguajes regulares mediante la existencia de un DFA.
* Formalizar la aparición de ciclos en ejecuciones suficientemente largas.
* Demostrar que recorrer repetidamente un ciclo preserva la aceptación.
* Construir una prueba completa del Lema de Bombeo para lenguajes regulares.

## Tecnologías utilizadas

* **Lean 4**
* **Mathlib**
* **Lake**, como sistema de construcción y gestión de dependencias

## Definiciones principales

### Autómata Finito Determinista

Un DFA sobre un alfabeto genérico `σ` está formado por:

* Un tipo finito de estados `Q`.
* Una función de transición `δ`.
* Un estado inicial `q0`.
* Un conjunto de estados de aceptación `F`.

```lean
structure DFA (σ : Type u) where
  Q : Type u
  [fintype_Q : Fintype Q]
  δ : Q → σ → Q
  q0 : Q
  F : Set Q
```

La condición `Fintype Q` garantiza que el conjunto de estados es finito, propiedad esencial para aplicar el principio del palomar.

### Función de transición extendida

La función de transición original procesa un único símbolo:

```lean
δ : Q → σ → Q
```

Para procesar una palabra completa, representada mediante `List σ`, se define una transición extendida:

```lean
def DFA.step (M : DFA σ) : M.Q → List σ → M.Q
```

Esta función representa matemáticamente a (\delta^*): recibe un estado inicial y una palabra, y devuelve el estado alcanzado después de procesar todos sus símbolos.

Conceptualmente:

[
\delta^*(q, []) = q
]

[
\delta^*(q, a :: w) = \delta^*(\delta(q,a),w)
]

### Aceptación de palabras

Una palabra es aceptada cuando la ejecución del autómata, comenzando en el estado inicial, termina en un estado perteneciente al conjunto de aceptación:

```lean
def DFA.accepts (M : DFA σ) (w : List σ) : Prop :=
  M.step M.q0 w ∈ M.F
```

En términos matemáticos:

[
M \text{ acepta } w
\iff
\delta^*(q_0,w)\in F
]

### Lenguaje reconocido por un DFA

El lenguaje de un autómata es el conjunto de todas las palabras que acepta:

```lean
def DFA.language (M : DFA σ) : Set (List σ) :=
  {w | M.accepts w}
```

### Lenguajes regulares

Un lenguaje es regular si existe algún DFA que lo reconoce:

```lean
def RegularLanguage (σ : Type) (L : Language σ) : Prop :=
  ∃ M : DFA σ, L = M.language
```

Esta definición conecta la representación abstracta de un lenguaje con un modelo computacional finito capaz de reconocerlo.

## Idea matemática de la demostración

Sea (M) un DFA con (p) estados y sea (w) una palabra aceptada cuya longitud satisface:

[
|w|\geq p
]

Durante la lectura de los primeros (p) símbolos de (w), el autómata visita al menos (p+1) estados si también se cuenta el estado inicial.

Como el DFA solamente tiene (p) estados, el principio del palomar garantiza que algún estado debe repetirse.

Por lo tanto, existen posiciones (j) y (l) tales que:

[
0\leq j<l\leq p
]

y los prefijos de longitudes (j) y (l) llevan al autómata al mismo estado:

[
\delta^*(q_0,\operatorname{take}(j,w))
======================================

\delta^*(q_0,\operatorname{take}(l,w))
]

A partir de estas posiciones, la palabra puede dividirse como:

[
w=xyz
]

donde:

* (x) contiene los primeros (j) símbolos.
* (y) contiene los símbolos entre las posiciones (j) y (l).
* (z) contiene el resto de la palabra.

Como el autómata se encuentra en el mismo estado antes y después de procesar (y), este segmento forma un ciclo. En consecuencia, puede repetirse cualquier cantidad de veces sin cambiar el estado desde el cual se procesa (z).

## Lemas principales

La demostración final se divide en varios resultados intermedios.

### `pigeonhole_states`

Este lema aplica el principio del palomar a la secuencia de estados recorridos por el DFA.

Si una palabra es suficientemente larga, existen dos prefijos distintos dentro de sus primeros (p) símbolos que terminan en el mismo estado.

El lema produce índices (j) y (l) tales que:

[
j<l\leq p
]

y:

[
\delta^*(q_0,\operatorname{take}(j,w))
======================================

\delta^*(q_0,\operatorname{take}(l,w))
]

Esta repetición permite identificar un ciclo en la ejecución del autómata.

### `cycle_property`

A partir de los índices proporcionados por el principio del palomar, se definen:

[
x=\operatorname{take}(j,w)
]

[
y=\operatorname{take}(l-j,\operatorname{drop}(j,w))
]

El lema demuestra que procesar (y) desde el estado alcanzado después de leer (x) devuelve al autómata al mismo estado:

[
\delta^*(\delta^*(q_0,x),y)
===========================

\delta^*(q_0,x)
]

Por lo tanto, (y) representa un ciclo dentro del DFA.

### `pumping_preserves_acceptance`

Este lema demuestra que, si:

[
w=xyz
]

es aceptada y (y) forma un ciclo después de procesar (x), entonces repetir (y) cualquier número de veces preserva la aceptación.

Formalmente:

[
\forall i\in\mathbb{N},
\quad
xy^iz\in L
]

En Lean, la repetición de una lista puede expresarse mediante una operación equivalente a replicar o elevar concatenativamente el segmento `y`.

La demostración se realiza por inducción sobre el número de repeticiones (i).

### `pumping_lemma`

Este teorema combina los resultados anteriores y establece el Lema de Bombeo completo.

Si (L) es regular, entonces existe una longitud de bombeo (p) tal que toda palabra (w\in L) con:

[
|w|\geq p
]

puede descomponerse como:

[
w=xyz
]

cumpliendo:

1. El segmento bombeable no es vacío:

[
y\neq []
]

2. El segmento (xy) aparece dentro de los primeros (p) símbolos:

[
|xy|\leq p
]

3. Cualquier cantidad de repeticiones de (y) produce una palabra que continúa perteneciendo al lenguaje:

[
\forall i\in\mathbb{N},
\quad
xy^iz\in L
]

La longitud de bombeo elegida corresponde al número de estados del DFA que reconoce el lenguaje:

[
p=|Q|
]

## Enunciado matemático

El resultado formalizado corresponde al siguiente teorema:

> Para todo lenguaje regular (L), existe un número natural (p) tal que, para toda palabra (w\in L) con (|w|\geq p), existen palabras (x), (y) y (z) para las cuales:
>
> [
> w=xyz,
> \qquad
> y\neq\varepsilon,
> \qquad
> |xy|\leq p
> ]
>
> y:
>
> [
> \forall i\geq 0,
> \quad
> xy^iz\in L
> ]

## Ejecución del proyecto

Después de instalar Lean 4 mediante [elan](https://github.com/leanprover/elan), el proyecto puede compilarse con:

```bash
lake build
```

También es posible abrir el repositorio en Visual Studio Code utilizando la extensión oficial de Lean 4 para revisar las demostraciones de manera interactiva.

## Posibles aplicaciones

El Lema de Bombeo se utiliza normalmente para demostrar que determinados lenguajes **no son regulares**.

El procedimiento habitual consiste en:

1. Suponer que el lenguaje es regular.
2. Obtener una longitud de bombeo (p).
3. Elegir una palabra apropiada (w) con (|w|\geq p).
4. Considerar cualquier descomposición (w=xyz) que cumpla las condiciones del lema.
5. Elegir una cantidad de repeticiones para la cual (xy^iz\notin L).
6. Obtener una contradicción.

Un ejemplo clásico es:

[
L={a^nb^n\mid n\geq 0}
]

En este lenguaje, bombear una sección situada dentro del bloque inicial de símbolos (a) rompe la igualdad entre la cantidad de símbolos (a) y (b), demostrando que el lenguaje no puede ser regular.

La sección final del proyecto proporciona una base para formalizar esta clase de argumentos por contradicción en Lean.

## Limitaciones actuales

La formalización se concentra en el Lema de Bombeo para lenguajes regulares y en las estructuras necesarias para demostrarlo.

Entre las posibles extensiones se encuentran:

* Formalizar ejemplos concretos de lenguajes no regulares.
* Demostrar que ({a^nb^n\mid n\geq 0}) no es regular.
* Relacionar DFA y expresiones regulares.
* Formalizar autómatas finitos no deterministas.
* Probar la equivalencia entre DFA y NFA.
* Formalizar propiedades de clausura de los lenguajes regulares.
* Extender el proyecto al Lema de Bombeo para lenguajes libres de contexto.

## Motivación académica

Este proyecto busca conectar la teoría de lenguajes formales con la verificación asistida por computadora.

La formalización en Lean obliga a expresar explícitamente cada hipótesis y cada paso de la demostración, incluyendo aspectos que suelen omitirse en una prueba escrita, como:

* La construcción exacta de los prefijos.
* Las relaciones entre `take`, `drop` y concatenación.
* La conservación de la longitud.
* La existencia de índices repetidos.
* La demostración inductiva de la repetición de ciclos.
* La preservación de la aceptación.

De esta manera, Lean no solamente verifica el resultado final, sino también la corrección lógica de toda la argumentación.
