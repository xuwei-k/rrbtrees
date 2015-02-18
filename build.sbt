scalaVersion := "2.11.5"

val scalazVersion = "7.1.1"

libraryDependencies += "org.scalaz" %% "scalaz-core" % scalazVersion
libraryDependencies += "org.scalaz" %% "scalaz-scalacheck-binding" % scalazVersion % "test"
