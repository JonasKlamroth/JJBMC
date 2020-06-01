FROM ubuntu
RUN apt update && apt install -y \
    openjdk-8-jdk 


COPY . /JJBMC
WORKDIR /JJBMC

RUN ./gradlew fatJar