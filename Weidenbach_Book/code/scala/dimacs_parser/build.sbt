import Dependencies._
import sbt.Keys.libraryDependencies

lazy val root = (project in file(".")).
  settings(
    inThisBuild(List(
      organization := "com.example",
      scalaVersion := "2.12.1",
      version      := "0.1.0-SNAPSHOT",
      javaOptions in run += "-Xss512M",
      javaOptions in run += "-agentlib:hprof=cpu=y",
      scalacOptions += "-optimize",
      scalacOptions += "-opt:_",
      fork := true,
      exportJars := true
    )),
    name := "Hello",
    mainClass := Some("Hello"),
    libraryDependencies += scalaTest % Test,
    libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.5"
  )
