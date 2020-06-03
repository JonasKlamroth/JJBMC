FROM gradle:jdk8


COPY ./src /JJBMC/src
COPY ./resources /JJBMC/resources
COPY ./tests /JJBMC/tests
COPY ./testRes /JJBMC/testRes
COPY ./build.gradle /JJBMC/build.gradle
COPY ./lib /JJBMC/lib
COPY ./settings.gradle /JJBMC/settings.gradle

WORKDIR /JJBMC

RUN gradle wrapper
RUN ./gradlew fatJar

CMD /bin/sh
