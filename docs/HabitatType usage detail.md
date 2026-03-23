see also [[habitat usage summary]]
##### abstracted usages
(These abstracted functions are in map.cpp)

isDistributary(HabitatType t, bool includeDistributaryEdge = true);
- includes `Distributary` and `DistributaryEdge`
- used in movement algorithms, flow speed calcs (`hydro.cpp`)
- min depth of Distributaries are set from nearest hydro node elev
- "disjoint" distributaries (not navigable from any recruit point) get special handling (see below) at map load time

isDistributaryOrHarbor(HabitatType t);
- these get special min depths and min temps

isDistributaryOrNearshore(HabitatType t);
- when initially assigning all hydro nodes to the nearest map node, only Distributaries and Nearshore are eligible. After that, all remaining nodes get the nearest hydro from a neighboring map node

isDistributaryWithoutEdgeOrIsNearshore()
- only these habitat types may receive an additional habitat mortality multiplier

~~isHarbor();~~ (only used in `isDistributaryOrHarbor`)

isNearshore(HabitatType t);
- Pmax equation has several Nearshore-specific params, with a default for all other habitats.
- Nearshore also appears with Distributary in `isDistributaryOrNearshore` and `isDistributaryWithoutEdgeOrIsNearshore` (see above)

isBlindChannel(HabitatType t);  
isImpoundment(HabitatType t);
- blind channels and impoundments receive special flow speed scalars (used when calculating swim speeds in movement algorithms)
##### direct usages
In `fish.cpp::move()`
```
if (this->location->type == HabitatType::Nearshore) {  
    this->incrementExitHabitatHoursByOneTimestep();  
} else {  
    this->numExitHabitatHours = 0;  
}
if (this->numExitHabitatHours >= model.habitatTypeExitConditionHours) {  
    this->exit(model);  
    return false;  
}
```
used as part of the exit condition.

In `load.cpp:simplifyBlindChannels()` to identify blind channels to be merged.

In `load.cpp:expandNearshoreLinks()` to create extra nodes between the nodes of all (Nearshore, non-Nearshore) edges.

In `load.cpp:loadMap()` to assign habitat type to node. Note special handling: use `DistributaryEdge` if column 11 is "1", otherwise use the string name in column 6.

(deprecated) In `load.cpp:checkDisjointDistributaries...` to change Distributaries to blind channels if they are "disconnected", meaning they cannot be navigated to from any recruit (release) point. This is deprecated, and instead we remove disconnected nodes.

In `gui.cpp` for colors and legends.