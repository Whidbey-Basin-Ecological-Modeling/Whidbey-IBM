##### how the current "single population" release is created at multiple sites
1. the main json config contains an array of `recruitEntryNodes`, ids that are later matched against map node ids. This eventually winds up in `Model::recPoints` (type `MapNode*`)
2. recruit_counts by day and size_dists by week are loaded from their respective files
3. at the start of each day, `Model::planRecruitment()` computes the number of recruits for the day, then the number for each timestep is sampled from a uniform distribution
4. at the start of each timestep, `Model::recruitSingle` moves new recruits into the model, one for each indicated from step 3. This involves:
    1. get a weighted sample `flIdx` for the appropriate week using `recSizeDists`
    2. use a hard-coded formula based on the weekly distributions:
   ```
   unsigned flIdx = sample(recSizeDist.data(), recSizeDist.size());  
   // Calculate the fork length from the bucket index  
   float forkLength = 35.0f + 5.0f * flIdx + unit_rand() * 5.0f;
   ```
    3. create a `Fish` in the current timestep with the length and uniform random sample from recruit points (Model::recPoints, see step 1)
    4. attempt to `tag` the newly created fish. Only every 2500th new recruit is actually tagged. Immediately after tagging, `Fish::trackHistory` is called, recording the location and other attributes. **In this way, tagged fish will always have their release point (recruit point) as their first location.**

Questions:
1. Will new recruits obtain their starting location in the same way, i.e. a uniform distribution over all possible recruit points?
2. Will the initial size be computed in the same way, with weekly length distributions, along with a hard-coded calculation to use them?
3. Will initial counts across all release sites be specified in a daily input file, as currently done? No separate release counts by site?
4. For multiple populations, are there any behaviors or algorithms that we expect to vary by population type, rather than by location and individual fish characteristics?