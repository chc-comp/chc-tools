name := "chc-format-checker"

version := "0.1"

mainClass in Compile := Some("formatchecker.Checker")

fork in run := true

cancelable in Global := true

scalaVersion := "2.11.12"

resolvers += "uuverifiers" at "http://logicrunch.it.uu.se:4096/~wv/maven/"

libraryDependencies +=
  "uuverifiers" %% "princess-smt-parser" % "2020-03-12"

libraryDependencies +=
  "net.sf.squirrel-sql.thirdparty-non-maven" % "java-cup" % "0.11a"
