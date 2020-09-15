# QuadraticFieldExtensions
Quadratic Extensions of Prime order Fields - Formalization in Coq

**Dependencies:** Apart from the standard library, Coqprime and fiatCrypto is used. fiatCrypto is consistently referenced as "Crypto".

The line

-R /home/au543200/Crypto/fiat-crypto/src/ Crypto

in _CoqProject will need to be changed to    
-R "PATH" Crypto

Where "PATH" is a path to fiat-crypto/src/


opam install coq-prime


**FourQ.v**

A formal specification of the curve FourQ (see https://eprint.iacr.org/2015/565.pdf)


**QuadraticFieldExtensions.v**

A specification of quadratic extensions of finite fields (as defined in Coqprime.GZnZ) of order p, where p is a prime number with p mod 4 = 3.


**RingsUtil.v and FieldsUtil.v**

Contain a few results on rings and fields respectively.

    - It is shown that fields and rings of prime order p and their quadratic extensions have characteristic p (as defined in Crypto.Algebra.Ring)

    - it is shown that a set with operations satisfying the "field_theory" (or ring_theory) of the standard library is an instance of the field (or ring) class of Crypto.Algebra.Hierarchy.

    - The groups of units of a finite fields is constructed, and it is shown to have order q - 1, where q is the order of the field.



**RepeatedSquaring**

Contains an algorithm to do exponentiation in monoids via repeated squaring.


**SquareTest**

Verifies that an element, x, of a finite field is not a square, if x^(q - 1)/2 is not 1, where q is the order of the field.