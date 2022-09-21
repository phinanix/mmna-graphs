# mmna-graphs 

A collaberative project between @phinanix and @ohAitch to search for additional examples of [Minor Minimal Non-apex Graphs](https://en.wikipedia.org/wiki/Apex_graph#Characterization_and_recognition) (MMNA graphs). [Previous work](http://tmattman.yourweb.csuchico.edu/mpthesis.pdf) only searched up to examples on 10 vertices, but with clever techniques and performant code I suspect exhaustive search up to at least 12-13 vertices is possible without an exorbitant number of core-hours. 

## Algorithms 
* Planarity Checking (using the [Demoucron, Malgrange, and Pertuiset](http://www.mathe2.uni-bayreuth.de/EWS/demoucron.pdf) (DMP) algorithm)
* Apex and MMNA checking (using heuristics)
* Enumeration of graph minors
* Graph Canonicalization/Automorphism/Isomorphism (in-progress)
* Enumeration of Planar / Apex / MMNA candidate graphs a la [plantri](https://users.cecs.anu.edu.au/~bdm/papers/plantri-full.pdf)