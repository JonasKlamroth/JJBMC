# JJBMC
JJBMC is a tool develop at the FZI/KIT which enables the bounded model checker [JBMC](https://github.com/mre/jbmc) to verify JML contracts. To run the tool you can either build it manually or use a prebuild docker image. 

# Use docker
- install docker if not already installed (e.g. sudo curl -sSL https://get.docker.com/ | sh)
- pull docker image: docker pull jonasklamroth/jjbmc:small
- run interactive container: docker run -it jonasklamroth/jjbmc:small
- run program as shown below

# Build it manually 
## Requirements
- Java 8!
- (Gradle 6.4.1 or higher) <- only if gradle wrapper doesnt work on your system
- Some Unix OS (tested only on Ubuntu 20.04)

## Compiling
- make sure JAVA_HOME points to a valid java 8 installation (tested for openjdk)
- checkout code: git clone git@github.com:JonasKlamroth/JJBMC.git (for ssh checkout)
- build jar: ./gradlew fatJar
- if not working create gradle wrapper: gradle wrapper

# Run case studies
- Show options: java -jar build/libs/JJBMC.jar
- Bubblesort: java -jar build/libs/JJBMC.jar testRes/BubbleSort.java -j="--unwind 6"
- Bubblesort with wrong specification: java -jar build/libs/JJBMC.jar testRes/BubbleSortBroken.java -j="--unwind 6"
- Bubblesort without modularization: java -jar build/libs/JJBMC.jar testRes/BubbleSort.java -j="--unwind 6"
- Hammingweight: java -jar build/libs/JJBMC.jar testRes/NormalHammingWeight.java -j="--unwind 33"
