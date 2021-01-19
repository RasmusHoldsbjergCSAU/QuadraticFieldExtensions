# Formal Verification of Cryptographic primitives.

In this Project, we treat quadratic field extensions, with the goal of developing efficient formally verified implementations of elliptic curves to be used in cryptographic applications such as digital signature scheme.

**Theory**
We develop the theory of quadratic field extensions.
This includes a number of results such as the construction of the group of units for finite fields, exponentiation by repeated squaring in monoids and of course the construction of the field extensions themselves.

**Implementations**
Finite field arithmetic is being performed in the montgomery domain, see (https://www.microsoft.com/en-us/research/wp-content/uploads/1996/01/j37acmon.pdf).
In order to produce efficient implementations, we make use of a lazy reduction scheme for arithmetic in the extended field.
An important piece of the puzzle is the "separated operand scanning" method of doing montgomery multiplication (section 4 in the article above).
This project therefore contains a formally verified specification of This method, which is compatible with the Fiat Crypto pipeline and thus may be extracted to working code.
TODO: Implement lazy reduction arithmetic using the separated montgomery multiplication.
