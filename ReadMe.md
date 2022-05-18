JJBMC is a tool that is developed both at [FZI](https://www.fzi.de) and [KIT](https://www.kit.edu), which enables the software bounded model checker [JBMC](https://www.cprover.org/jbmc/) to verify contracts written in the [Java Modeling Language (JML)](http://jmlspecs.org/index.shtml). In order to run the tool, you have 3 options:
- Build it manually.
- Use our prebuilt docker image (notice, however, that proofs will take significantly longer in the docker version).
- Use the [prebuilt version](https://github.com/JonasKlamroth/JJBMC/releases/download/ISoLa/JJBMC.jar).

## Using the Docker Image
- Install docker if you do not have it already installed (e.g., via ``sudo curl -sSL https://get.docker.com/ | sh``).
- For the following step, you might need to prefix the call with ``sudo `` if you are not a member of the docker group.
- Run the interactive container via ``docker run -it jonasklamroth/jjbmc``.
- Run JJBMC as shown below in the section **Running JJBMC**.

## Building JJBMC Manually 
### Requirements
- Java 8 (both newer and older versions do not work due to incompatibilities with OpenJML)
- Gradle 6.4.1 or higher (only if gradle wrapper does not work on your system)
- Preferably some Unix OS (tested only on Ubuntu 20.04)

### Compiling JJBMC
- Make sure that **JAVA_HOME** points to a valid installation of Java 8 (tested for openjdk).
- Checkout the source code via ``git clone git@github.com:JonasKlamroth/JJBMC.git`` (for a checkout using SSH).
- Build the jar file via ``./gradlew fatJar`` (**JJBMC.jar** will appear in the root folder of your project).
- If the previous step does not work, first create a gradle wrapper via ``gradle wrapper``.

## Running JJBMC
- **Important**: JJBMC uses JBMC as a backend. Please make sure that a recent version (currently >= 5.22) of JBMC is installed and included in the path. To download and install the latest JBMC version (as part of CBMC) go to https://github.com/diffblue/cbmc/releases/.
- You can see the available command-line options via ``java -jar JJBMC.jar``.
- In general, you can run JJBMC via ``java -jar JJBMC.jar JAVA_FILE METHOD_NAME -j="JBMC_OPTIONS"``, where **JAVA_FILE** should be replaced by the JML-specified Java file that you want to analyze, **METHOD_NAME** can be replaced by a name of a method you would like to verify (if left out all methods are verified), and **JBMC_OPTIONS** should be replaced by the JBMC options that you want to set, e.g., a bound for loop unrollings via ``--unwind BOUND`` (**BOUND** should be replaced by the size of the desired bound). For examples, see the section below.

## Examples
- You can analyze a correct modular [Bubblesort example](testRes/BubbleSort.java) via
```
java -jar JJBMC.jar testRes/BubbleSort.java sort
```
- You can analyze the same [Bubblesort example](testRes/BubbleSort.java), however with a wrong specification via
```
java -jar JJBMC.jar testRes/BubbleSort.java broken_sort 
```
- You can analyze force a non modular verification (inlining all loop invariants and methods) of the [Bubblesort example](testRes/BubbleSort.java) via
```
java -jar JJBMC.jar testRes/BubbleSort.java -fi 
```
- You can analyze the [Hammingweight example](testRes/NormalHammingWeight.java) via
```
java -jar JJBMC.jar testRes/NormalHammingWeight.java -u 33
```
