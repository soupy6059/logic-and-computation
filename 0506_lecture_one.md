# Lecture 1

[Outline and Schedule](https://student.cs.uwaterloo.ca/~cs245/)

TUT F
Assignment every ~2 weeks

A | 0.25
M | 0.30
F | 0.45

# Logic and CS

Foundations of Logic and Mathematics 
- set theory => more theory
- logical axioms
- incompleteness theorems
Birth of Computation
- Turing machines
- lambda Calc
Advances in Proof Theory
- "modern proof theory" formal deduction
- type theory

# Formal Reasoning about Programs
[Lean, ROCQ, shit]

CompCert:
- compiler bugs invalidate prog
- compiler for C in ROCQ prover
- used to compile **critical** software
    - Avionics, OS kernels, smart contracts, ML algorithms, 

ROCQ -> Haskell -> PROG
     => C Compiler : C -> PROG 

# Structural Induction
Generalization of inductions

sim to java or C#

dafny.nat := $\N\cup\{0\}$ % zero inclusive
```dafny
function twoPow(n: nat): nat
{
    if n == 0 then 1
    else 2 * twoPow(n - 1)
}

// prove that 1 <= towPow(n) for all n
// lemma -> logic => SOLVER -> good/bad
lemma twoPow_geq_1(n: nat) ensures 1 <= twoPow(n) {}

lemma {:induction false} twoPow_geq_1(n: nat)
    ensures 1 <= twoPow(n) {
    if n == 0 {
        calc {
            twoPow(n);
            == twoPow(0);
            == 1;
            >= 1;
        }
    } else {
        twoPow_geq_1(n - 1); // holds for n - 1
        calc {
            twoPow(n);
            == 2 * twoPow(n - 1);
            >= 2 * 1; // by IH
            >= 1;
        }
    }
}
```
dafny gives a way to do induction for tests -> prove a lemma via induction

```dafny
datatype Tree =
| Emp
| Node(left: Tree, rigjt: Tree)

// Prove that the number of nodes in a tree is at most 2^(Height(t))-1

function max(x: nat, y: nat): nat {
    if x > y then x
    else y
}
function Height(t: Tree): nat {
    match t
    case Emp => 0
    case Node(left, right) => 1 + max(Height(left), Height(right))
}

function Nodes(t: Tree): nat {
    match t
    case Emp => 0
    case Node(left, right) => 1 + Nodes(left) + Nodes(right)
}

lemma twoPow_leq_mono(n: nat, m: nat)
    requires n <= m
    ensures twoPow(n) <= twoPow(m) {} // dfy proven

lemma twoPow_sum_upper_bound(n: nat, m: nat)
    ensure twoPow(n) + twoPow(m) <= twoPow(max(n,m)+1) {
    if n < m {
        twoPow_lt_mono(n,m);
    } else {
        twoPow_leq_mono(m,n);
    }
}

// PROVEN
lemma NodesBound(t: Tree)
    ensure Nodes(t) <= twoPow(Height(t)) - 1 {
    match t
    case Emp =>//?
    case Node(l, r) =>
        NodesBound(l);
        NodesBound(r);
        assert Nodes(l) <= twoPow(Height(l)) - 1;
        assert Nodes(r) <= twoPow(Height(r)) - 1;

        twoPow_sum_upper_bound(Height(l), Height(r));
        assert twoPow(Height(l)) + twoPow(Height(r)) <=
            twoPow(max(Height(l), Height(r)) + 1);

        calc {
            Nodes(t);
            == 1 + Nodes(l) + Nodes(r);
            <= 1 + (twoPow(Height(l)) - 1) + (twoPow(Height(r) - 1);//IH
            == twoPow(Height(l)) + twoPow(Height(r)) - 1; 
            <= twoPow(max(Height(l),Height(r))) +
                 twoPow(max(Height(l),Height(r))) - 1
            <= twoPow(max(Height(l), Height(r)) + 1) - 1;
            == twoPow(Height(t)) - 1;
        }
}
```

# Propositional Logic, and Connectives
english to prop logic; review of induction;
tanslations; prop syntax;

# First Order Logic
quantifiers // use to prove something isn't unif cts???

# Turing Machines

# Program Verification
formal deduction system
