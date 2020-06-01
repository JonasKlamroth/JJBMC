# Requirements
- Java 8!
- Gradle 6.4.1 or higher
- Some Unix OS (tested only on Ubuntu 20.04)

# Building
- create gradle wrapper: gradle wrapper
- build jar: ./gradlew fatJar
- make sure JAVA_HOME points to a valid java 8 installation

# Run case studies
- Show options: java -jar build/libs/JJBMC.jar
- Bubblesort: java -jar build/libs/JJBMC.jar testRes/BubbleSort.java -j="--unwind 6"
- Bubblesort with wrong specification: java -jar build/libs/JJBMC.jar testRes/BubbleSortBroken.java -j="--unwind 6"
- Bubblesort without modularization: java -jar build/libs/JJBMC.jar testRes/BubbleSort.java -j="--unwind 6"
- Hammingweight: java -jar build/libs/JJBMC.jar testRes/NormalHammingWeight.java -j="--unwind 33"
- add timing information: 
