
# Proving pigeonhole principle without excluded middle in Coq

--------------------------------

In the chapter on inductively defined propositions in the first volume
of *Software Foundations*:

https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html

there is an interesting exercise on proving the pigeonhole principle
under the assumption of excluded middle for the `In x l` predicate.
It is stated there that the excluded middle assumption is actually
unnecessary.  The file `php_wo_em.v` shows how this can be done.

--------------------------------

&copy; 2018-2019  Ching-Tsun Chou (<chingtsun.chou@gmail.com>)
