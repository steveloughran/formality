<!---
  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at
  
   http://www.apache.org/licenses/LICENSE-2.0
  
  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License. See accompanying LICENSE file.
-->
  


# Hadoop Coding Standards

## Introduction

Apache Hadoop is one of the most complicated open source projects being developed. Its code is nothing compared to the scale of the Linux Kernel and device drivers, yet it has some of the same characteristics: a filesystem API and implementations(s) (HDFS), a scheduler for executing work along with a means of submitting work to it (YARN), programs to process data on it (MAPREDUCE, Apache Tez), databases (Apache HBase, Apache Accumulo) and management and monitoring tools, both open source and closed). 

Where it is complicated is that it is designed to run across hundreds to thousands of individual servers, to store tens of petabytes of data, and to execute those scheduled programs in the face of failures of those servers. 

It is both a distributed system, and a filesystem and OS for data & datacenter-scale applications. It is possibly the most ambitious "unified" distributed computing projects ever attempted. (HTTP servers and browsers atop the network stack are significantly larger, but developed in a loosely couple way that reflects their layering and distribution). The core of Hadoop is a single system; the key apps that run atop it and developed alongside it, very tightly coupled to that underlying Hadoop application.

For that reason, the project has high expectations and standards of changes to the code. This document attempts to describe them.

It is also intended to provide guidelines for anyone writing applications on top of Hadoop, including YARN applications.

## Designing for Scale; Designing for Fail

Hadoop is designed to work at the scale of thousands of machines. Some of them will fail on large jobs or jobs that take time. Code needs to be designed for both the scale and the failure modes.

### Scale

Hadoop applications need to be designed to scale to thousands —even tens of thousands— of distributed components.

1. Data structures must be designed to scale, ideally at `O(1)`, `O(log2(n))` or similar. At the scale of Hadoop, `O(n)` is too expensive.
1. The algorithms to work with the data structures must also scale well.
1. Services need to be designed to handle the challenge of many thousands of services reporting near-simultaneously. The "cluster restart" scenario is a classic example here.
1. Cluster operations MUST be designed to be O(1). That is: no harder to run a cluster of a thousand machines than a cluster of 10. Equally importantly, that single-node cluster should be easy to operate.
1. Do not have one-thread-per-request service architectures without size-limited thread pools or other form of thread sharing.

Datasets may be measured in tens or hundreds of Terabytes.

1. Algorithms to work with these datasets must be designed to scale across the cluster: no single node will suffice.
1. In-memory storage is too expensive for data of this scale. While the cost will fall over time, the dataset size is likely to grow at a similar rate. Design algorithms to work efficiently when data is stored on a (slower) persistent storage, be it Hard disk or, in future, SSD.
1. Hadoop is moving towards heterogenous data storage; data may be stored at different levels in the hierarchy, with these details being potentially transparent to the application. Consider using this rather than trying to implement your own memory caches —the HDFS system is designed to support administrator-managed quotas, and distribute the cached layers around the cluster so as to make more efficient use of the storage tiers.
1. Applications need to be careful not to accidentally overload other parts of the infrastructure. Making too many simultaneous requests to the Hadoop Namenode (i.e directory listing and file status queries) can impact HDFS. Even something as "harmless" as a DNS lookup can be disruptive if a single DNS server is used to service the requests of a large cluster. 
1. A sensible size of number for storing things like counts is `long` rather than `int`.

### Failure

1. Don't expect everything to complete: rely on timeouts. YARN applications will have failures reported to their Application Master —this has to handle them.
1. Slow processes/YARN container-hosted applications can be as troublesome as failing ones, as they can slow down entire workflows. An example of this is the MapReduce "straggler". MapReduce handles these by supporting speculative execution of the trailing work, and by blacklisting nodes. Different applications will need different strategies.
1. Failures can just as easily be caused by bad application configurations and data: tracking repeated failures of part of an application can be used with some heuristics to conclude that there may be a problem. Here MapReduce can be set to react by skipping specific portions of its input data. Other applications may be able to follow this strategy, or they may have to react differently.
1. Failure at scale can have its own problems, especially in the specific case of a Hadoop cluster partition. An application may get simultaneous reports of hundreds or thousands components failing within a few seconds or minutes —it has to respond to these, possibly by recognising the cluster partition simply by the size of the failure report. (HDFS itself has known weaknesses here).
1. YARN applications: do not assume that reallocated containers will come up on the same nodes, or be able to open the same network ports.
1. YARN applications: the AM itself may fail. The default policy in this situation is that YARN kills all the containers then relaunches the AM somewhere. It is possible to request an alternative policy of "retain containers over AM restarts". In this case it becomes the duty of the AM to rebuild its state on restart. Long lived YARN applications should consider this policy.
1. Dependent services such as HDFS and YARN may themselves fail. While the HA modes should recover from the failures, the cost of this recovery is delays until the failover is complete. Applications need to consider whether they want the default mode of operation (block until failover/restart) or be designed to detect the failures and react in some way. Failure detection is relatively straightforward: configure the IPC layer to report problems rather than block. Reacting to the failure is a significantly harder issue which must be addressed on a case-by-case basis —even within an application.
1. At sufficiently large scale, data corruption may set in. This is why HDFS checksums its data —and why Hadoop may add its own checksums to Hadoop's IPC layers before long.

Hard disks fail more often than individual servers —they are mechanical and fail over time, and as there are many HDDs to a server, statistics catches up with them. SSDs have their own failure modes as they wear out.

In production clusters, disk and server failures tend to surface when a cluster is restarted; this is time that disks are checked most thoroughly by the OS, and power cycles themselves can cause problems. Applications do not have to worry about this startup phase, but HDFS does.

## Code Style

For Java code, start with the original "Sun" guidelines.

1. Two spaces are used for indentation. Not tabs, not four spaces, not eight spaces. Two.
1. Eighty characters wide. This may seem dated, but it aids patch reviewing through side-by-side comparisons.
1. Don't use `.*` imports except for `import static` imports. This means: *turn off IDE features that automatically update and re-order imports*. This feature makes merging patches harder.

### Comments

1. SHOULD use javadoc above methods, class, and field declarations.
1. SHOULD Avoid explaining how a method works: it will only become obsolete in time and just confuse people. Write down what the method is expected to do.
1. SHOULD use `// ` within methods. On their own lines, indented to match the source. Not: at end of line. Not: 
1. MUST NOT: mix `//` comments within multiline code

        String bad = evaluate() 
                    //  update interval
                    + conf.getUpdateInterval()
1. MUST NOT: use comments to turn `log` commands on or off. Downgrade them or delete them; do not just comment them out.

### Configuration options

1. Declare configuration options as constants, instead of inline

          public static final string KEY_REGISTRY_ZK_QUORUM = "hadoop.registry.zk.quorum";
1. Give them meaningful names, scoped by the service on which they operate.
1. Code which retrieves string options SHOULD use `Configuration.getTrimmed()` unless they have a specific need to include leading and trailing strings in the values.
1. Provide meaningful default values in the java source
1. Provide valid default values in `core-default.xml` and HDFS/YARN equivalents, with
meaningful text to accompany the values. These XML files are used to automatically generate documentation about configuration values. If no XML entry or text is provided, the configuration option will remain an undocumented mystery.


## Public, Private and Limited Private code

The Hadoop codebase consists of internal implementation classes, public Java-level classes and APIs, and public IPC protocol interfaces. The java language scope annotations: `public`, `private`, `protected` and package-scoped aren't sufficient to describe these —we need to distinguish a class that may be public, yet intended for internal use, from something that is for external callers. We also need to warn those external callers where an API is considered stable, versus an API that may change from release to release, as it stabilizes or evolves.

For this reason, the `hadoop-annotations` module/JAR contains some java `@` attributes for use in declaring the scope and stability of classes.

The interface audience is defined in the `org.apache.hadoop.classification.InterfaceAudience`

    public class InterfaceAudience {
      /**
       * Intended for use by any project or application.
       */
      public @interface Public {};
        
      /**
       * Intended only for the project(s) specified in the annotation.
       * For example, "Common", "HDFS", "MapReduce", "ZooKeeper", "HBase".
       */
      public @interface LimitedPrivate {
        String[] value();
      };
      /**
       * Intended for use only within Hadoop itself.
       */
      public @interface Private {};

The `@Private` and `@Public` annotations resemble those in the Java code. `@Private` means within the `hadoop` source tree ONLY. `@Public` means any application MAY use the class —though the stability annotation may be used as a warning about whether that interface is something the code may rely on.

The unusual one is `@LimitedPrivate`. This is used to declare that a class or interface is intended for use by specific modules and applications. 

The `@LimitedPrivate` attribute is a troublesome one. It implies that the Hadoop core codebase is not only aware of applications downstream, but that it is explicitly adding features purely for those applications and nothing else. As well as showing favoritism to those applications, it's potentially dangerous. Those special features created for  specific applications are effectively commitments to maintain the special feature indefinitely. In which case: why the special scope? Why not add a public API and make it a good one? This is not a hypothetical question, because special support was added into HDFS for HBase support -an append operation, and an atomic create-a-directory-but-not-its-parent method. The append operation eventually evolved into a public method, with HBase then needing to transition from its back-door operation to the public API. And [HADOOP-10995](https://issues.apache.org/jira/browse/HADOOP-10995) showed where some operations thought to be unused/deprecated were pulled —only to discover that HBase stopped compiling. 

What does that mean? Try to avoid this notion altogether.


### Stability

The stability of a class's public methods is declared via the `org.apache.hadoop.classification.InterfaceStability` annotation, which has three values, `Unstable`, `Stable` and `Evolving`.

    public class InterfaceStability {
      /**
       * Can evolve while retaining compatibility for minor release boundaries.; 
       * can break compatibility only at major release (ie. at m.0).
       */
      public @interface Stable {};  
      
      /**
       * Evolving, but can break compatibility at minor release (i.e. m.x)
       */
      public @interface Evolving {};
      
      /**
       * No guarantee is provided as to reliability or stability across any
       * level of release granularity.
       */
      public @interface Unstable {};
    }

It is a requirement that: **all public interfaces must have a stability annotation**

 1. All classes that are annotated with `Public` or`LimitedPrivate` MUST have an `InterfaceStability` annotation.
 1. Classes that are `Private` MUST be considered unstable unless a different `InterfaceStability` annotation states otherwise.
 1. Incompatible changes MUST NOT be made to classes marked as stable.
 
 What does that mean?
 
 1. The `interface` of a class is, according to the *Hadoop Compatibility Guidelines*, defined as the API level binding, **the signature**, and the actual behavior of the methods, **the semantics**. A stable interface not only has to be compatible at the source and binary level, it has to work the same.
 1. During development of a new feature, tag the public APIs as `Unstable` or `Evolving`. Declaring that something new is `Stable` is unrealistic. There will be changes, so not constrain yourself by declaring that it isn't going to change.
 1. There's also an implicit assumption that any class or interface that does not have any scope attribute is private. Even so, there is no harm in explicitly stating this.

Submitted patches which provide new APIs for use within the Hadoop stack MUST have scope attributes for all public APIs.
 


## Concurrency

Hadoop services are highly concurrent. This codebase is not a place to learn about Java concurrency —developers are expected to have acquired knowledge and experience of Java threading and concurrency before getting involved in Hadoop internals.

Background: the Java memory model:
* [The Java Memory Model](http://www.cs.umd.edu/~pugh/java/memoryModel/), especially [this paper](http://dl.dropbox.com/u/1011627/journal.pdf).

1. Use the `java.utils.concurrent` classes wherever possible.
1. Use the `AtomicBoolean` and `AtomicInteger` classes in preference to shared simple datatypes.
1. If simple datatypes are shared across threads, they MUST be marked `volatile`.

Note that Java `volatile` types are more expensive than C/C++ (they are memory barriers),
so should not be used for types which are not `synchronized`, or which are only accessed within
synchronization blocks.

1. In the core services, try to avoid overreaching service-wide locks.
1. Consider operation-specific locks through having (`final`) fields which can be locked for access to specific areas.
1. If-and-only-if-absolutely-necessary, lock on the `.class` object. This is justifiable if the operation would affect all instances of a class.
1. Avoid calling native code in locked regions.
1. Avoid calling expensive operations (including `System.currentTimeMillis()`) in a locked region. If these operations do not need to be synchronized, consider calling them in advance and cache the results
1. Code MUST NOT ignore an `InterruptedException` —it is a sign that part of the
system wishes to stop that thread, often on a process shutdown.
Wrap it in an `InterruptedIOException` if you need to convert to an `IOException`.
1. Code MUST NOT start threads inside constructors. These may execute before the class is
fully constructed, leading to bizarre failure conditions.
1. Use `Callable<V>` over `Runnable`, as it can not only return a value —it can
raise an exception.
1. Use Executors over Threads
1. Use fixed pool executors over creating a new thread per request/operation.
 The one-thread-per-action architecture does not scale to the size of workloads which Hadoop applications can generate.
 This is not just server side; it has surfaced in pure-client-side code, such as the S3A filesystem client
 ([HADOOP-11446](https://issues.apache.org/jira/browse/HADOOP-11446)). A good design for a small application, one
 that works in the test cases, can fail dramatically in the field.


Key `java.utils.concurrent` classes include

* `ExecutorService`
* `Callable<V>`
* Queues, including the `BlockingQueue`.


There is a reasonable amount of code that can be considered dated in Hadoop, using threads and runnables. These should be cleaned up at some point —rather than mimicked.



## Logging

Hadoop logging has several audiences:

* People who are new to Hadoop and trying to get a single node cluster to work.
* Hadoop sysadmins who don't want to have to become experts in reading Java stack traces to diagnose
local cluster problems.
* people who help other people's Hadoop clusters to work (that includes those companies that provide some form of Hadoop support).
* Hadoop JIRA bug reports.
* Hadoop developers.
* Programs that analyze the logs to extract information.

Hadoop's logging could be improved —there's a bias towards logging for Hadoop developers than for other people, because it's the developers who add the logs they need to get things to work.

Areas for improvement include: including some links to diagnostics pages on the wiki, including more URLs for the hadoop services just brought up, and printing out some basic statistics. 

Hadoop is also (slowly) migrating from the apache commons-logging API to SLF4J. This style guide covers SLF4J only:

1. SLF4J is the logging API to use for all new classes. It MUST be used.
1. ERROR, WARN and INFO level events MAY be logged without guarding
  their invocation.
1. DEBUG-level log calls MUST be guarded. This eliminates the need
to construct string instances.
1. Unguarded statements MUST NOT use string concatenation operations to build the log string, as these are called even if the logging does not take place. Use `{}` clauses in the log string.
  Bad:

      LOG.info("Operation "+ action+ " outcome: " +outcome)
  Good:

      LOG.info("Operation {} outcome: {}", action, outcome)

1. Classes SHOULD have lightweight `toString()` operators to aid logging. These MUST be robust
against failures if some of the inner fields are null.
1. Exceptions should be logged with the text and the exception included as a
 final argument, for the trace.
1. `Exception.toString()` MUST be used instead of `Exception.getMessage()`,
as some classes have a null message.

         LOG.error("Failed to start: {}", ex, ex)

There is also the opportunity to add logs for machines to parse, not people. The HDFS Audit Log is an example of this —it enables off-line analysis of what a filesystem has been used for, including by interesting programs to detect which files are popular, and which files never get used after a few hours -and so can be deleted. Any contributions here are welcome.



## Cross-Platform Support

Hadoop is used in Production server-side on Linux and Windows, with some Solaris and AIX deployments. Code needs to work on all of these. 

Java 6 is unsupported from Hadoop 2.7+, with Java 7 and 8 being the target platforms. Java 9 is expected to remove some of the operations. The old Apple Java 6 JVMs are obsolete and not relevant, even for development. 

Hadoop is used client-side on Linux, Windows, OS/X and other systems.

CPUs may be 32-bit or 64-bit, x86, PPC, ARM or other parts. 

JVMs may be: the classic "Sun/Oracle" JVM, OpenJDK, IBM JDK, or other JVMs based off the Sun/Oracle source tree. These tend to differ in

* heap management.
* non-standard libraries (`com.sun`, `com.ibm`, ...). Some parts of the code —particularly the Kerberos support— has to use reflection to make use of these JVM-specific libraries.
* Garbage collection implementation, pauses and such like. 

Operating Systems vary more, with key areas being:

* Case sensitivity and semantics of underlying native filesystem. Example, Windows NTFS does not support rename operations while a file in a path is open. 
* Native paths. Again, windows with its drive letter `c:\path` structure stands out. Hadoop's `Path` class contains logic to handle these...sometimes test construct paths by going

        File file = something();
        Path p = new Path("file://" + file.toString())
  use
  
        Path p = new Path(file.toURI());

* Process execution. Example: as OS/X does not support process groups, YARN containers do not automatically destroy all children when the container's parent (launcher) process terminates.
* Process signalling
* Environment variables. Names and case may be different.
* Arguments to the standard Unix commands such as `ls`, `ps`, `kill`, `top` and suchlike.

## Performance

Hadoop prioritizes correctness over performance. It absolutely prioritizes data preservation over performance. Data must not get lost or corrupted.

That said, Hadoop is designed to scale to tens of thousands of machines. Algorithms should be designed to scale: ideally `O(1)`, failing that something `O(lg(n))`.

## Protobuf and RPC

* New fields on existing messages must be `optional`, otherwise all existing clients will be unable to talk to the far end.
* Accordingly, services must be designed to have a valid default for a new field, handling the absence of a field value gracefully.


## Security

Hadoop supports insecure clusters and secure "Kerberized" clusters. 
The latter uses Kerberos to authenticate services as well as users.
This means it is **critical** that Hadoop code works in secure environments.

As a developer, that means you need to understand (a) how to set up
a secure Hadoop cluster and (b) how to write code that works in a
secure Hadoop cluster.

Set up a machine/VM as a Kerberos Domain Controller (KDC) and use this
to create the keytabs needed for Hadoop run in in secure mode. 
This can take a couple of hours, hours in which you will learn the basics of Kerberos.

Insecure clusters run in-cluster code in different accounts
from the users submitting work. Access to HDFS propagates by passing
the `HADOOP_USER` environment variable around. This variable is picked up
by programs which use the Hadoop HDFS client libraries and used
 to impersonate that user (in an unsecured cluster, obviously). 
 
YARN applications MUST set this environment variable when launching an application in an insecure cluster.

Secure clusters use Kerberos and require each user submitting work to have an account of the same name in the cluster.

### Prerequisite Knowledge


* Basic Kerberos concepts and architecture.
* How to set up a secure Hadoop cluster (at least a VM) —including SPNEGO authenticated HDFS and RM web .
* How to read and edit a `krb5.conf` file.
* What SPNEGO is; how to set your web browser up to use it.
* What Hadoop Delegation Tokens are for; how they differ from Authentication tokens, and when to use them.
* Web services: how to use the Authentication Filter and how to offer a token renewal service.
* REST clients: how to set up Jersey for SPNEGO & how to react to authentication failures.
* RPC services: how to declare the principal for communications in
 `META-INF/services/org.apache.hadoop.security.SecurityInfo` and the matching `SecurityInfo` subclass.
* YARN applications: how to get delegation tokens from clients to your application; which ones you will need.
* Long-lived YARN services: how to work with keytabs
* The meaning of obscure GSS API error messages (you can always learn these as you go along).

Is this a lot to know? Yes. Is it intimidating? Don't worry: we all find Kerberos hard.
But do not think you can get away without this knowledge -all you are doing is putting
your learning off.


### References

Read these. You do need to know the details.

1. [Adding Security to Apache Hadoop](http://hortonworks.com/wp-content/uploads/2011/10/security-design_withCover-1.pdf)
1. [The Role of Delegation Tokens in Apache Hadoop Security](http://hortonworks.com/blog/the-role-of-delegation-tokens-in-apache-hadoop-security/)
1. [Chapter 8. Secure Apache HBase](http://hbase.apache.org/book/security.html)
1. Hadoop Operations 1st edition, p135+
1. [Java 8 Kerberos Requirements](http://docs.oracle.com/javase/8/docs/technotes/guides/security/jgss/tutorials/KerberosReq.html)
1. [Troubleshooting Kerberos on Java 8](http://docs.oracle.com/javase/8/docs/technotes/guides/security/jgss/tutorials/Troubleshooting.html)
1. [JAAS Configuration (Java 8)](http://docs.oracle.com/javase/8/docs/technotes/guides/security/jgss/tutorials/LoginConfigFile.html)

### Coding equirements

1. DO NOT PUT SECURITY AND KERBEROS OFF UNTIL THE END OF YOUR WORK
1. Do not assume that user names are simple "unix" names; they may have spaces and kerberos realms in them.
1. Use the `UserGroupInformation` class to manage user identities; its `doAs()` operation to perform actions
as a specific user.
1. Test against both secure and insecure clusters. The `MiniKDC` server provides a basic in-JVM
Kerberos controller for tests. 
1. Some parts of the Hadoop stack (e.g. Zookeeper) are also controlled by JVM properties. Be careful when setting
up such applications to set the properties before.

Key has to be the first point: Security cannot be an afterthought. If you put it off you will find your
near-deadline time spent trying to debug security issues in code that hasn't been designed to be secure,
while struggling to read those documents referenced above and learn the associated concepts in a hurry.
Avoid this by putting in the effort early.



## Exceptions

Exceptions are a critical form of diagnostics on system failures.

* They should be designed to provide enough information to enable experienced
Hadoop operators to identify the problem.
* They should provide enough information to enable new Hadoop
users to identify problems starting or connecting to their cluster.
* They need to provide information for the Hadoop developers too.
* Information MUST NOT be lost as the exception is passed up the stack.


Exceptions written purely for the benefit of developers are not what end users
or operations teams need —and in some cases can be misleading. As an example,
the java network stack returns errors such as `java.net.ConnectionRefusedException`
which returns none of the specifics about what connection was being refused 
(destination host & port), and can be misinterpreted by people unfamiliar with
Java exceptions or the sockets API as a Java-side problem. 

This is why Hadoop wraps the standard socket exceptions in `NetUtils.wrapException()`

1. These extend the normal error messages with host and port information for the experts,
1. They add links to Hadoop wiki pages for the newbies who interpret "Connection Refused"
as the namenode refusing connections, rather than them getting their destination port misconfigured.
1. It retains all the existing socket classes. They aren't just wrapped in a
general `IOException` —they are wrapped in new instances of the same exception class. This
ensures that `catch()` clauses can select on exception types.

In general:


1. Try to use Hadoop's existing exception classes where possible.
1. Except for some special cases, exceptions MUST be derived from `IOException`
1. Use specific exceptions in preference to the generic `IOException` 
1. `IllegalArgumentException` may be used for some checking of input parameters,
but only where consistent with other parts of the stack.
1. If an exception is generated from another exception, the inner exception
must be included, either via the constructor or through `Exception.initCause()`.
1. If an exception is wrapping another exception, the inner exception
text MUST be included in the message of the outer exception.
1. The text value of an exception MUST be extracted from `Exception.toString`.
1. `Exception.getMessage()` MUST NOT be used. For some exceptions this returns null.
1. Where Hadoop adds support for extra exception diagnostics (such as with
`NetUtils.wrapException()`) —use it.
1. Exceptions should provide any extra information to aid diagnostics, 
including —but not limited to— paths, remote hosts, and any details about
the operation being attempted.
1. Where Hadoop doesn't add support for extra diagnostics —try implementing it.


The requirement to derive exceptions from `IOException` means that
developers must not use Guava's `Preconditions.checkState()` check as
these throw `IllegalStateException` instances. 


## Internationalization


1. Error messages use EN_US, US English in their text messages.
1. Log messages must use US English as their text.
1. Classes, methods and variables must use US English in their names.
1. Names that are misspelled can be near-impossible to remove: please check with
a spell checker set to the US if you have any doubts about your spelling.
1. Code must use `String.toLowerCase(EN_US).equals()` rather than
 `String.equalsIgnoreCase()`. Otherwise the comparison will fail in
 some locales (example: Turkey).
1. Similarly, use `String.toLowerCase(EN_US)` and `String.toUpperCase(EN_US)` to
change the case of text.

## Main functions


A static `main(String[] args)` method routine can be invoked via the
`/bin/hadoop` script, a script which will set up the classpath and
other environment variables consistently.

Hadoop uses its `ToolRunner` class as the entry point to code —both
client and server.

This provides a standard set of configuration parameters, including 
adding the ability to define and  extend the Hadoop XML configuration to
use.

Entry points SHOULD use the `TestRunner` interface for their entry point
logic.

This is not mandatory; there may be valid reasons to avoid doing this, a key
one being that the application may be using an alternative CLI parser such
as `JCommander`. If an alternative CLI parser library is used, the `main()`
routine SHOULD support the standard command line options, especially the
`-D name=value` syntax.

## Tests

Tests are a critical part of the Hadoop codebase.

The standard for tests is as high as for the code itself. 

Tests MUST be

* Executable by anyone, on any of the supported development platforms (Linux, Windows and OS/X)
* Designed to show something *works as intended even in the face of failure*. That doesn't just mean "shows that given the right parameters, you get the right answers", it means "given the wrong args/state, it fails as expected". Good tests try to break the code under test.
* Be fast to run. Slow tests hamper the entire build and waste people's time.
* Be designed for failures to be diagnosed purely from the assertion failure text and generated logs. Everything needed to understand why a test failed should be determinable from the results of a remote Jenkins/CI tool-managed run, the generated test reports and any log data collected.
* Be deterministic. Everyone hates tests that fail intermittently.
* Be designed for maintenance. Comments, meaningful names, etc. Equally importantly: not contained hard coded strings in log and exception searches, Instead use constants in the classes under test and refer to them.


Tests MUST

* Use directories under the property `test.dir` for temporary data. The way to get this dir dynamically is: 

        new File(System.getProperty("test.dir", "target"));
* shut down services after the test run.
* Not leave threads running or services running irrespective of whether they fail or not. That is: always clean up afterwards, either in `try {} finally {}` clauses or `@After` and `@AfterClass` methods. This teardown code must also be robust against incomplete state, such as null object references.
* Work on OS/X, non-Intel platforms and Windows. There's a field in `org.apache.hadoop.util.Shell` which can be used in an `Assert.assume()` clause to skip test cases which do not work here.
* To avoid port in use exceptions, use port '0' for registering services, or scan for a free port.

Tests MUST NOT

* Require internet access. That includes DNS lookup of remote sites.
* Contain any assumptions about the ordering of previous tests -such as expecting a prior test to have set up the system. Tests may run in different orders, or purely standalone.
* Rely on a specific log-level for generating output that is then analyzed. Some tests do this, and they are problematic. The preference is to move away from these and instrument the classes better.
* Require specific timings of operations, including the execution performance or ordering of asynchronous operations.
* Have hard-coded network ports. This causes problems in parallel runs, especially on the Apache Jenkins servers. Either use port 0, or scan for a free port.
* Run up large bills against remote cloud storage infrastructures *by default*. The object store client test suites are automatically skipped for this reason.
* Take long times to complete. There are some in the codebase which are slow; these do not begin with the word `Test` to stop them being run except when explicitly requested to do so.
* Store data in `/tmp`, or the temp dir suggested by `java.io.createTempFile(String, String)`. All temporary data must be created under the directory `./target`. This will be cleaned up in test runs, and not interfere with parallel test runs.


Tests MAY

* Assume the test machine is well-configured. That is, the machine knows its own name, has adequate disk space.

Tests SHOULD 

* Use loopback addresses `localhost` rather than hostnames, because the hostname to IP mapping may loop through the external network, where a firewall may then block network access.

* Clean up after themselves.


### Assertions

Tests SHOULD provide meaningful text on assertion failures. The best metric is "can someone looking at the test results get any idea of what failed without chasing up the stack trace in an IDE?"

That means adding meaningful text to assertions, along with any diagnostics information that can be picked up.

Bad:

    assertTrue(target.exec());

Good

    assertTrue("exec() failed on " + target, target.exec());

Bad

    assertTrue(target.update()==0);

Good

    assertEquals("update() failed on " + target, 0, target.update());

Such assertions are aided by having the classes under test having meaningful `toString()` operators —which is why these should be implemented.

### Timeouts

Test MUST have timeouts. The test runner will kill tests that take too long -but this loses information about which test failed. By giving the individual tests a timeout, diagnostics are improved.

Add a timeout to the test method

      @Test(timeout = 90000)

Better: declare a test rule which is picked by all test methods

      @Rule
      public final Timeout testTimeout = new Timeout(90000);


*Important*: make it a long enough timeout that only failing tests fail. The target machine
here is not your own, it is an underpowered Linux VM spun up by Jenkins somewhere.

### Keeping tests fast

Slow tests don't get run. A big cause of delay in Hadoop's current test suite is the time to start up new Miniclusters ... the time to wait for an instance to start up can often take longer than the rest of the test.

### Exposing class methods for testing

Sometimes classes in Hadoop expose internal methods for use in testing. 

There are three ways of exporting private methods in a production class for this

1. Make `public` and mark `@VisibleForTesting`. Easiest, but risks implicitly becoming part of the API.
1. Mark `@VisibleForTesting`, but make package scoped. This allows tests in the same package to use the method, 
so is unlikely to become part of the API. It does require all tests to be in the same package, which
can be a constraint.
1. Mark `@VisibleForTesting`, but make `protected`, then subclass in the test source tree
 with a class that exposes the methods. This adds a new risk: that it is subclassed 
 in production. It may also add more maintenance costs.


There is no formal Hadoop policy here.

There is however, another strategy: don't expose your internal methods for testing.
The test cases around a class are the test of that classes APIs —and often the
code people start with to use the code.

If the functionality of a class cannot be used without diving below that API,
it's a sign that the API is limited. People will end up using your test methods,
either because they needed to, or just because they copied your code as a starting
point —and it was using those methods.

For any class which is designed for external invocation, this implies 
you should think about improving that public API for testability,
rather than sneaking into the internals. 

If your class isn't designed for direct public consultation, but instead 
a small part of a service remotely accessible over the network
—then yes, exposing the internals may be justifiable. Just bear in mind that you are
increasing the costs of maintaining the code: someone will need to update all
the tests as changes are made to the internals of a class.


*Further Reading*

* [Standard for Software Component Testing](http://www.testingstandards.co.uk/Component%20Testing.pdf)


### Testing with Exceptions

Catching and validating exceptions are an essential 
aspect of testing failure modes. However, it is dangerously
easy to write brittle tests which fail the moment anyone changes the exception
text.

To avoid this:

1. Use specific exception classes, then catch purely those exceptions.
1. Use constants when defining error strings, so that the test
can look for the same text
1. When looking for the text, use `String.contains()` over
`String.equals()` or `String.startsWith()`.

Bad

    try {
      doSomething("arg")
      Assert.fail("should not have got here")
    } catch(IOException e) {
      Assert.assertEquals("failure on path /tmp", e.getMessage());
    }
    

This is way to brittle and doesn't help you find out what is going on on a failure.

Good

    @Test()
    public void testSomething {
      try {
        doSomething("arg")
        Assert.fail("should not have got here")
      } catch(PathNotFoundException e) {
        Assert.assertTrue(
          "did not find " + Errors.FAILURE_ON_PATH + " in " + e,
          e.toString().contains(Errors.FAILURE_ON_PATH);
      }
    }
    

Here a constant is used to define what is looked for (obviously, one used in the exception's constructor). It also uses the `String.contains()` operator —so if extra details are added to the exception, the assertion still holds.

Good

    @Test(expected = PathNotFoundException.class)
    public void testSomething {
        doSomething("arg")
    }


This takes advantage of JUnit 4's ability to expect a specific exception class, and looks for it. This is nice and short. Where it is weak is that it doesn't let you check the contents of the exception. If the exception is sufficiently unique within the actions, that may be enough. 

Good: examine the contents of the exception as well as the type. 
Rethrow the exception if it doesn't match, after adding a log message explaining why it was rethrown:

    @Test
    public void testSomething {
      try {
        result = doSomething("arg")
        Assert.fail("expected a failure, got: " + result)
      } catch(PathNotFoundException e) {
        if (!e.toString().contains(Errors.FAILURE_ON_PATH) {
          LOG.error("No " + Errors.FAILURE_ON_PATH + " in {}" ,e, e)
          throw e;
        }
      }
    }

This implementation ensures all exception information is propagated. If it doesn't fail, the return value of the 
operation is included in the failure exception, to aid debugging. 
As the test is failing because the code in question is not behaving as expected, 
having a stack trace in the test results can be invaluable. 

In comparing the two options, the JUnit 4 {{expected}} will be less informative, but it makes for a much easier to understand test. For it to be a good test, some conditions must be met

1. There's only one place in the test case where raising the expected exception can happen. If the exception could get raised before or after the core operation being tested, then the test could be failing in the wrong place —with the test runner not picking it up.
1. The type of the exception is sufficient to verify that the failure was as expected. A high level `Exception` or `IOException` is unlikely to be adequate.


### Skipping tests that aren't available on the test system

Not all tests work everywhere

    public static void skip(String message) {
      log.warn("Skipping test: {}", message)
      Assume.assumeTrue(message, false);
    }

    public static void assume(boolean condition, String message) {
      if (!condition) {
        log.warn("Skipping test: {}",  message)
        Assume.assumeTrue(message, false);
      }
    }

### Testing Tips


You can automatically pick the name to use for instances of mini clusters and the
like by extracting the method name from JUnit:

      @Rule
      public TestName methodName = new TestName();

# Hadoop Coding Standards: Other Languages

### Code Style: Python

1. The indentation should be two spaces.
1. Code for Windows as well as Unix


### Code Style: Bash

1. Bash lines may exceed the 80 character limit where necessary.
1. Try not to be too clever in use of the more obscure bash features —most Hadoop developers don't know them.
1. Make sure your code recognises problems and fails with exit codes. That is, it MUST check for non-zero return codes on its operations and SHOULD then exit the script with an error.

The key thing to assume when writing Bash scripts is that the majority of the Hadoop project developers are not bash experts who know all the subtleties. If you are doing something
reasonably complex, do add some comments explaining what you are doing.


### Code Style: Native


#### MUST

1. C code following [Linux kernel style](https://www.kernel.org/doc/Documentation/CodingStyle) with one exception: indent by two spaces.
1. Make no assumptions about ASCII/Unicode, 16 vs 32 bits: use `typedef` and `TSTR` definitions; `int32` and `int64` for explicit integer sizes.
1. Use `CMake` for building.
1. Assembly code must be optional; the code and algorithms around it must not be optimized for one specific CPU family.
1. While you can try optimising for memory models of modern systems, with NUMA storage, three levels of cache and the like, it does produce code that is brittle against CPU part evolution. Don't optimize prematurely here.
1. MUST compile on Linux, OSX and Windows platforms. You should test this as well as you can. If others are expected to do the work, it is likely to languish in the patch-pending state.
1. MUST be accompanied by tests to verify the functionality.

#### MUST NOT
1. MUST NOT impact the performance of the x86 code. This is the primary CPU family used in production Hadoop. While the project is happy to accept patches for other CPUs (e.g. ARM, PPC, ...), it must not be at the expense of x86. 
1. MUST NOT remove or rename existing methods.

### Code Style: Maven POM files

* All declarations of dependencies with their versions must be in the file `hadoop-project/pom.xml`. 

# Patches to the code

Here are some things which scare the developers when they arrive in JIRA:

* Large patches which span the project. They are a nightmare to review and can change the source tree enough to stop other patches applying.
* Patches that delve into the internals of critical classes. The HDFS NameNode, Edit log and YARN schedulers stand out here. Any mistake here can cost data (HDFS) or so much CPU time (the schedulers) that it has tangible performance impact on the big Hadoop users. 
* Changes to the key public APIs of Hadoop. That includes the `FileSystem` & `FileContext` APIs, YARN submission protocols, MapReduce APIs, and the like.
* Patches that reorganise the code as part of the diff. That includes imports. They make the patch bigger (hence harder to review) and may make it harder to merge in other patches.
* Big patches without tests.
* Medium sized patches without tests.
* Small patches without tests unless they are simple things like spelling corrections in strings or comments.

Things that are appreciated:

* Documentation, in javadocs and in the `main/site` packages. Markdown is accepted there, and easy to write.
* Good tests.
* For code that is delving into the internals of the concurrency/consensus logic, well argued explanations of how the code works in all possible circumstances. State machine models and even TLA+ specifications can be used here to argue your case.
* Any description of what scale/workload your code was tested with. If it was a big test, that reassures people that this scales well. And if not, at least you are being open about it.


