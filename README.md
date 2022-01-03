## KeYPl

**KeY for Proof Plans**

This is a frontend to the [KeY verification system](http://key-project.org) [[1]](#references) for efficiently evaluating the correctness of feature-oriented software product lines.

Software product lines (SPLs) are large families of programs that share a common set of features.
The correctness of all method variants in an SPL can be verified with the KeY verification system for individual products of an SPL.
However, to check an entire SPL, this approach checks all its product individually, which is inefficient for large SPLs (product-based analysis).

With our approach as implemented in KeYPl, we can avoid checking each product of an SPL in isolation.
To do this, we use *proof plans*, which cache proofs systematically so that we can reuse them for several configurations of an SPL [[2]](#references).
This implementation of proof plans allows for several concrete verification strategies, including feature-(product-/family-)based approaches.

### How to Use

- We provide our case study and evaluation results in the `caseStudy` directory. To reproduce our results, unzip `caseStudy.zip` and run the `evaluate` script (requires JRE 1.8 and possibly `dos2unix evaluate` under Linux systems).
- Our implementation is based on KeY 2.8.0 (vanilla version). We do not rely on abstract contracts or uninterpreted predicates, but implement partial proofs with abstract model methods [[1]](#references).
- The `KeYBridge` class implements the interface to KeY. Our programming model, proof graphs/plans, and partial proof system are all implemented in the `Core` class. The `Shell` class addresses code parsing and evaluation concerns.
- A pre-built and self-contained JAR file is available in the `evaluation/caseStudy.zip` archive. Run `java -jar KeYPl.jar` to see its usage.
- For a manual build, the only dependency required is [JDK 1.8](http://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html).
  You can build the JAR by running `./gradlew build`, which stores the JAR file into `build/libs`.
  Alternatively, you can directly run the JAR with `./gradlew run`.
- You can use the project with [IntelliJ IDEA](https://www.jetbrains.com/idea/).
  Create an `Application` run configuration to run the JAR.

### License

This project is a research effort of the [DBSE working group](http://www.dbse.ovgu.de/).
It is released under the [LGPL v3 license](LICENSE.txt).
Feel free to [contact me](mailto:kuiter@ovgu.de) (the main developer) if you have any questions.

### References

1. Wolfgang Ahrendt, Bernhard Beckert; Richard Bubel; Reiner Hähnle; Peter H. Schmitt, and Mattias Ulbrich. 2016. [Deductive Software Verification - The KeY Book - From Theory to Practice](https://www.key-project.org/thebook2/). Springer.
2. Elias Kuiter. 2020. [Proof Repositories for Correct-by-Construction Software Product Lines](http://wwwiti.cs.uni-magdeburg.de/iti_db/publikationen/ps/auto/Kuiter2020:MasterThesis.pdf). Otto-von-Guericke-University Magdeburg.
