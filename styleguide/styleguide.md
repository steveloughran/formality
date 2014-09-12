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
  


# Hadoop Coding Standards: Java

## Code Style

Follow the Sun guidelines with some specific exceptions

1. two spaces are used for indentation


## Concurrency

Hadoop services are highly concurrent. This codebase is not a place to learn about the Java memory model and concurrency —developers are expected to have acquired knowledge and experience of Java threading and concurrency before getting involved in Hadoop internals.

1. Use the `java.utils.concurrent` classes wherever possible.
1. Use the `AtomicBoolean` and `AtomicInteger` classes in preference to shared simple datatypes.
1. If simple datatypes are shared across threads, they MUST be marked `volatile`.
Note that Java `volatile` types are more expensive than C/C++ (they are memory barriers),
so should not be used for types which are not `synchronized`, or which are only accessed within
synchronization blocks.
1. In the core services, try to avoid overreaching service-wide locks.
1. Avoid calling native code in locked regions.
1. Avoid calling expensive operations (including `System.currentTimeMillis()`)
in locked regions.
1. Code MUST NOT ignore an `InterruptedException` —it is a sign that part of the
system wishes to stop that thread, often on a process shutdown.
Wrap it in an `InterruptedIOException` if you need to convert to an `IOException`.
1. Code MUST NOT start threads inside constructors. These may execute before the class is
fully constructed, leading to bizarre failure conditions.
1. Use Executors over threads
1. Use `Callable<V>` over `Runnable`, as it can not only return a value —it can
raise an exception.

Key `java.utils.concurrent` classes include
* `ExecutorService`
* `Callable<V>`
* Queues, including the `BlockingQueue`.


There is a reasonable amount of code that can be considered dated in Hadoop, using threads and runnables.
These should be cleaned up at some point —rather than mimicked.

## Exceptions

Exceptions are a critical form of diagnostics on system failures.

* They should be designed to provide enough information to enable experienced
Hadoop operators to identify the problem.
* They should to provide enough information to enable new hadoop
users to identify problems starting or connecting to their cluster.
* They need to provide information for the Hadoop developers too.
* Information MUST NOT be lost as the exception is passed up the stack.


Exceptions written purely for the benefit of developers are not what end users
or operations teams need —and in some cases can be misleading. As an example,
the java network stack returns errors such as `java.net.ConnectionRefusedException`
which returns none of the specifics about what connection was being refused 
destination host & port), and can be misinterpreted by people unfamiliar with
Java exceptions or the sockets API as a Java-side problem. 

This is why Hadoop wraps the standard socket exceptions in `NetUtils.wrapException()`

1. These extend the normal error messages with host and port information for the experts,
1. They add links to Hadoop wiki pages for the newbies who interpret "Connection Refused"
as the namenode refusing connections, rather than them getting their destination port misconfigured.
1. It retains all the existing socket classes. The aren't just wrapped in a
general `IOException` —they are wrapped in new instances of the same exception class. This
ensures that `catch()` clauses can select on exception types.



1. Except for some special cases, exceptions MUST be derived from `IOException`
1. Use specific exceptions in preference to the generic `IOException` 
1. `IllegalArgumentException` may be used for some checking of input parameters,
but only where consistent with other parts of the stack.
1. Exceptions should provide any extra information to aid diagnostics, 
including —but not limited to— paths, remote hosts, and any details about
the operation being attempted.
1. If an exception is generated from another exception, the inner exception
must be included, either via the constructor or through `Exception.initCause()`.
1. If an exception is wrapping another exception, the inner exception
text MUST be included in the message of the outer exception.
1. Try to use Hadoop's existing exception classes where possible.
1. Where Hadoop adds support for extra exception diagnostics (such as with
`NetUtils.wrapException()`) —use it.
1. Where Hadoop doesn't add support for extra diagnostics —try implementing it.

The requirement to derive exceptions from `IOException` means that
developers must not use Guava's `Preconditions.checkState()` check as
these throw `IllegalStateException` instances. 


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
    

Good

    try {
      doSomething("arg")
      Assert.fail("should not have got here")
    } catch(PathNotFoundException e) {
      Assert.assertTrue(
        "did not find " + Errors.FAILURE_ON_PATH + " in " + e,
        e.toString().contains(Errors.FAILURE_ON_PATH);
    }
    

Best: rethrow the exception if it doesn't match, after adding a log message explaining why it was rethrown:

    try {
      doSomething("arg")
      Assert.fail("should not have got here")
    } catch(PathNotFoundException e) {
      if (!e.toString().contains(Errors.FAILURE_ON_PATH) {
        LOG.error("No " + Errors.FAILURE_ON_PATH + " in {}" ,e, e)
        throw e;
      }

This implementation ensures all exception information is propagated. As the
test is failing because the code in question is not behaving as expected, 
having a stack trace in the test results can be invaluable. 



## Logging

There's a number of audiences for Hadoop logging:

* People who are new to Hadoop and trying to get a single node cluster to work.
* hadoop sysadmins
* people who help other people's hadoop clusters to work (that includes those companies that provide some form of Hadoop support).
* Hadoop JIRA bug reports.
* Hadoop developers.
* Programs that analyze the logs to extract information.

Hadoop's logging could be improved —there's a bias towards logging for Hadoop developers than for other people, because it's the developers who add the logs they need to get things to work.

Areas for improvement include: including some links to diagnostics pages on the wiki, including more URLs for the hadoop services just brought up, and printing out some basic statistics. 

1. SLF4J is the logging API to use for all new classes. It MUST be used.
1. ERROR, WARN and INFO level events MAY be logged without guarding
  their invocation.
1. DEBUG-level log calls MUST be guarded. This eliminates the need
to construct string instances 
1. Classes SHOULD have lightweight `toString()` operators to aid logging. These MUST be robust
against failures if some of the inner fields are null.
1. Exceptions should be logged with the text and the exception included as a
 final argument, for the trace.
1. `Exception.toString()` must be used instead of `Exception.getMessage()`,
as some classes have a null message.

         LOG.error("Failed to start: {}", ex, ex)

There is also the opportunity to add logs for machines to parse, not people. The HDFS Audit Log is an example of this —it enables off-line analysis of what a filesystem has been used for, including by interesting programs to detect which files are popular, and which files never get used after a few hours -and so can be deleted. Any contributions here are welcome.



## Internationalization


1. Error messages use EN_US, US English in their text messages.
1. Code must use `String.toLower(EN_US).equals()` rather than
 `String.equalsIgnoreCase()`. Otherwise the comparison will fail in
 some locales (example: turkey). Yes, a lot of existing code gets
 this wrong —that does not justify continuing to make the mistake.

## Tests

Tests are a critical part of the Hadoop codebase.

The standard for tests is as high as for the code itself. 

Tests MUST be

* Executable by anyone, on any of the supported development platforms (Linux, Windows and mostly OSX)
* Designed to show something works as intended even in the face of failure. That doesn't just mean "shows that given the right parameters, you get the right answers", it means "given the wrong args/state, it fails as expected". Good tests try to break the code under test.
* Be fast to run. Slow tests hamper the entire build and waste people's time.
* Be designed for failures to be diagnosed purely from the assertion failure text and generated logs. 
* Be deterministic. Everyone hates tests that fail intermittently.
* Be designed for maintenance. Comments, meaningful names, etc. Equally importantly: not contained hard coded strings in log and exception searches ... use constants in the classes under test and refer to them.


Tests MUST

* Use directories under the property `test.dir` for temporary data. The way to get this dir dynamically is: 

        new File(System.getProperty("test.dir", "target"));
* shut down services after the test run.
* Not leave threads running or services running irrespective of whether they fail or not. That is: always clean up afterwards, either in `try {} finally {}` clauses or `@After` and `@AfterClass` methods. This teardown code must also be robust against incomplete state, such as null object references.
* Work on OSX, non-intel platforms and Windows. There's a field in `org.apache.hadoop.util.Shell` which can be used in an `Assert.assume()` clause to skip test cases which do not work here.

Tests MUST NOT

* Require internet access. That includes DNS lookup of remote sites.
* Contain any assumptions about the ordering of previous tests -such as expecting a prior test to have set up the system. Tests may run in different orders, or purely standalone.
* Rely on a specific log-level for generating output that is then analyzed. Some tests do this, and they are problematic. The preference is to move away from these and instrument the classes better.
* Require specific timings of operations, including the execution performance or ordering of asynchronous operations.

Tests MAY
* Assume the test machine is well-configured. That is, the machine knows its own name, which either reached 

Tests SHOULD 
* use loopback addresses `localhost` rather than hostnames, because the hostname to IP mapping may loop through the external network, where a firewall may then block network access.
* use port '0' for registering services, as other ports may be in use.



#### Assertions

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

#### Timeouts

Test MUST have timeouts. The test runner will kill tests that take too long -but this loses information about which test failed. By giving the individual tests a timeout, diagnostics are improved.

Add a timeout to the test method

      @Test(timeout = 90000)

Better: declare a test rule which is picked by all test methods

      @Rule
      public final Timeout testTimeout = new Timeout(90000);


*Important*: make it a long enough timeout that only failing tests fail. The target machine
here is not your own, it is an underpowered Linux VM spun up by Jenkins somewhere.

#### Keeping tests fast

Slow tests don't get run. A big cause of delay in Hadoop's current test suite is the time to start up new Miniclusters ... the time to wait for an instance to start up can often take longer than the rest of the test.

### Exposing class methods for testing

There are three ways of exporting private methods in a production class for testing

1. Make public, mark `@VisibleForTesting`. Easiest, but risks implicitly becoming part of the API.
1. Mark `@VisibleForTesting`, but make package scoped. This allows tests in the same package to use the method,
so is unlikely to become part of the API. It does require all tests to be in the same package, which
can be a constraint.
1. Mark as Mark `@VisibleForTesting`, but make `protected`, then subclass in the test source tree with a class that exposes the methods. This adds a new risk: that it is subclassed in production. It may also add more maintenance costs.

There is no formal Hadoop policy here.

### Tips


You can automatically pick the name to use for instances of mini clusters and the
like by extracting the method name from JUnit:

      @Rule
      public TestName methodName = new TestName();


## Cross-Platform Support

Hadoop is used in Production server-side on Linux and Windows, with some Solaris and AIX deployments. Code needs to work on all of these. 

Java 6 is unsupported from Hadoop 2.7+, with Java 7 and 8 being the target platforms. Java 9 is expected to remove some of the operations. The old Apple Java 6 JVMs are obsolete and not relevant, even for development. 

Hadoop is used client-side on Linux, Windows, OS/X and other systems.

CPUs may be 32-bit or 64-bit, x86, PPC, ARM or other parts. 

JVMs may be: the classic "sun" JVM; openjdk, IBM JDK, or other JVMs based off the sun source tree. These tend to differ in

* heap management.
* non-standard libraries (`com.sun`, `com.ibm`, ...). Some parts of the code —in particularly the Kerberos support— has to use reflection to make use of these JVM-specific libraries.
* Garbage collection implementation, pauses and such like. 

Operating Systems vary more, with key areas being:

* Case sensitivity and semantics of underlying native filesystem. Example, Windows NTFS does not support rename operations while a file in a path is open. 
* Native paths. Again, windows with its drive letter `c:\path` structure stands out. Hadoop's `Path` class contains logic to handle these...sometimes test construct paths by going

        File file = something();
        Path p = new Path("file://" + file.toString())
  use
        String p = new Path(file.toURI());

* Process execution. Example: as OS/X does not support process groups, YARN containers do not automatically destroy all children when the container's parent (launcher) process terminates.
* Process signalling
* Environment variables. Names and case may be different.
* Arguments to the standard Unix commands such as 'ls', 'ps', 'kill', 'top' and suchlike.

## Performance

Hadoop prioritizes correctness over performance. It absolutely prioritizes data preservation over performance. Data must not get lost or corrupted.

## Patches 

Hadoop is developed by patches —changes to code needs to be designed
to enable easy review. The 80 character limit is one example; it makes
side-by-side reviewing easier.

# Hadoop Coding Standards: Other Languages

### Code Style: Python

1. The indentation should be two spaces per level


### Code Style: Bash

1. Bash lines may exceed the 80 character limit where necessary.

### Code Style: Native

1. C code
1. Make no assumptions about ASCII/Unicode, 16 vs 32 bits: use `typedef` and `TSTR` definitions; `int32` and `int64` for explicit integer sizes.
