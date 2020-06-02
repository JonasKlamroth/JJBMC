# JJBMC
JJBMC is a tool that is developed both at [FZI](https://www.fzi.de) and [KIT](https://www.kit.edu), which enables the software bounded model checker [JBMC](https://www.cprover.org/jbmc/) to verify contracts written in the [Java Modeling Language (JML)](http://jmlspecs.org/index.shtml). In order to run the tool, you can either build it manually or use our prebuilt docker image.

# Using the Docker Image
- Install docker if you do not have it already installed (e.g., via ``sudo curl -sSL https://get.docker.com/ | sh``)
- Obtain the docker image via ``docker pull jonasklamroth/jjbmc:small``
- Run the interactive container via ``docker run -it jonasklamroth/jjbmc:small``
- Run JJBMC as shown below

# Building JJBMC Manually 
## Requirements
- Java 8 (both newer and older versions do not work due to incompatibilities with OpenJML)
- Gradle 6.4.1 or higher (only if gradle wrapper does not work on your system)
- Preferrably some Unix OS (tested only on Ubuntu 20.04)

## Compiling JJBMC
- Make sure that **JAVA_HOME** points to a valid installation of Java 8 (tested for openjdk)
- Checkout the source code via ``git clone git@github.com:JonasKlamroth/JJBMC.git`` (for an ssh checkout)
- Build the jar file via ``./gradlew fatJar``
- If the previous step does not work, first create a gradle wrapper via ``gradle wrapper``

# Run the Case Studies
- You can see the available command-line options via ``java -jar build/libs/JJBMC.jar``
- You can analyze a correct modular Bubblesort example via
```
java -jar build/libs/JJBMC.jar testRes/BubbleSort.java -j="--unwind 6"
```
- You can analyze the same Bubblesort example, however with a wrong specification via
```
java -jar build/libs/JJBMC.jar testRes/BubbleSortBroken.java -j="--unwind 6"
```
- You can analze a non-modular version of the Bubblesort example via
```
java -jar build/libs/JJBMC.jar testRes/BubbleSort.java -j="--unwind 6"
```
- You can analze the Hammingweight example via
```
java -jar build/libs/JJBMC.jar testRes/NormalHammingWeight.java -j="--unwind 33"
```
