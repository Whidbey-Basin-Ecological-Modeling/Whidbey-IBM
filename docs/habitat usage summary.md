see also [[HabitatType usage detail]]

All node types participate in the construction of a fully virtual simulated map, a feature currently not used.  
All node types are reflected differently from each other in the GUI.

Distributary only or Nearshore (NOT Distributary Edge):
- habitat mortality multiplier

Distributary or DistributaryEdge:
- discount movement cost when choosing destinations
- reduce elevations in all nodes to result in 0.2 min depth in Distrib or DistribEdges
- fix disjoint distributaries (changes to Blind Channel) (currently not used)

Harbor or Distributary or DistributaryEdge:
- enforce min water temp = 4 rather than 0.01 for others
- min depth of 0.2 rather than 0

Nearshore or Distributary or DistributaryEdge:
- part of assigning nearest hydro node algorithm. Every true hydro attaches to its  
  geo-nearest Nearshore or Distrib or DistribEdge. All other nodes get hydro propagated  
  to by map traversal distance

Blind Channel:
- Blind Channels may be simplified (combined) by a configured radius

Blind Channel or Impoundment:
- flow speed gets scaled down based on nearest hydro flow and width ratios

Nearshore:
- fish exit after configured consecutive hours in Nearshore nodes
- virtual nodes are created between Nearshore and neighboring non-Nearshore nodes
- fixed PMAX of 1.0

Impoundment: GUI only  
LowTideTerrace: GUI only