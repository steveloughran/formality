# Paper notes


## Paper: Sparrow 
2016-04-21

scheduling low latency work; responses <&lt; 100mS



### Challenges

-10K node, 16 core cluster -> 10^6 scheduling decisions/minute
-delays of 10s of mS major fraction of performance -visible
-HA

### Proposal: Decentralised

Failure mode: per scheduler
Scaling: add more schedulers

Problem: response times; conflicting decisions

Sparrow: power of two. Pick two servers, place work on server with lowest workload.

More specifically: batch sampling for multiple tasks. To schedule `m` tasks, sample `d * m` hosts (for `d > 1`), pick best.

Late binding: don't assign tasks to machines until machines have capacity

Policies and constraints on jobs, queues,

**Assumption** : services on cluster host executors (Spark, impala, LLAP). Sparrow schedules work in a multi-tenant cluster *across* the services.

**Unavailable**
 - Gang scheduling
 - placement constraints/anti-affinity
 - bin packing for optimal cluster utilisation
 
YARN can still be used to spin up services on nodes, but Sparrow also works with a static set of deployments. It may also work with other services on the nodes (e.g. HBase, Cassandra, if their load is included in the metrics provided by the workers)

Naive impl: probing for each task.

Collapses under load as duration of a job is that of the longest task, in a busy cluster p(finding a lightly used server) decreases, so
job times increase. That is: if only 10 in 1000 nodes are free, the probability of finding them is pretty low.

At 80% load, per-task sampling improved perf 3x over random, but 2.6x worse than an omniscient scheduler.

Batch sampling: aggregates results from probes for of all of a jobs tasks. To place 10 tasks across a 100 node cluster, sample 10*2 nodes, look for
10 most idle.

-Benefits: Eliminates probability that nodes will sample same nodes; avoids situations of a task picking two very slow nodes while another task picks two idle ones

Other load problem: multiple schedulers sampling worker, directing work to those with the lowest load, so making its queue too big.

Solution: workers queue up probe request and only processes when they reach the head of a queue. 
They then RPC to the scheduler, which then collects the first *n* processes which report in and give them work, the remainder
don't. The call in for requesting work can be when the work is assigned, so compensates RPC-wise.

Performance hit is time waiting for round trip RPC call is idle.

Request Cancellation: scheduler can explicitly cancel requests made to workers. This eliminates the delay when the worker is idle and requesting new work

### Constraints

Constraint placement handled by scheduler: identify those workers matching the constraints, and ask them.

Batch sampling doesn't work here as each task's constraints may be different. 
 