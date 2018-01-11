# Overview
Chord is a program analysis platform that enables users to productively design, implement, combine, and evaluate 
a broad variety of static and dynamic program analyses for Java bytecode.

It has the following key features:

* It provides various off-the-shelf analyses (e.g., various may-alias and call-graph analyses; thread-escape analysis; 
  static and dynamic concurrency analyses for finding races, deadlocks, atomicity violations; etc.)
* It allows users to express a broad range of analyses, including both static and dynamic analyses,
  analyses written imperatively in Java or declaratively in Datalog, context-sensitive inter-procedural analyses
  (summary-based and cloning-based), iterative refinement-based analyses, client-driven analyses, and
  combined static/dynamic analyses.
* It executes analyses in a demand-driven fashion, caches results computed by each analysis for reuse
  by other analyses without re-computation, and can execute analyses without dependencies between them in parallel.
* It guarantees that the result is the same regardless of the order in which different analyses are executed;
  moreover, results can be shared across different runs.

Chord is portable and has been tested on a variety of platforms, including Linux, Windows/Cygwin, and MacOS.
It is open source software distributed under the [New BSD License](http://www.opensource.org/licenses/bsd-license.php).


# Questions?

For questions about Chord, send email to chord-discuss{at}googlegroups.com or
[browse the archives](http://groups.google.com/group/chord-discuss).
Posting does not require membership but posts by non-members are moderated to avoid spamming group members.

