// You can use $SBT_OPTS to pass additional JVM optOAions to sbt.
// Project specific options should be placed in .sbtopts in the root of your project.
// Global settings should be placed in /opt/homebrew/etc/sbtopts
//
// Homebrew's installation does not include `sbtn`.

lazy val root = project
    .in(file("."))
    .settings(
      name := "Martin Berger",
//    email := "contact@martinfriedrichberger.net",
//    url   := url("https://github.com/martinberger"),
      description  := "TBC",
      version      := "TBC",
      scalaVersion := "3.4.0"
    )

scalacOptions ++= Seq(
  "-language:strictEquality", // Switch on type-safe equality, see https://docs.scala-lang.org/scala3/book/ca-multiversal-equality.html
  "-deprecation",             // emit warning and location for usages of deprecated APIs
  "-explain",                 // explain errors in more detail
  "-explain-types",           // explain type errors in more detail
  "-feature",                 // emit warning and location for usages of features that should be imported explicitly
  "-indent",                  // allow significant indentation.
  "-new-syntax",              // require `then` and `do` in control expressions.
  "-print-lines",             // show source code line numbers.
  "-unchecked",               // enable additional warnings where generated code depends on assumptions
  "-Ykind-projector",         // allow `*` as wildcard to be compatible with kind projector
  "-Xfatal-warnings",         // fail the compilation if there are any warnings
  "-Xmigration",              // warn about constructs whose behavior may have changed since version
  "-source:3.0"
)

lazy val scalacheck = "org.scalacheck" %% "scalacheck" % "1.15.3"
//libraryDependencies += scalacheck % Test

libraryDependencies ++= Seq(
  scalacheck       % "test",
  "org.scalatest" %% "scalatest" % "3.2.14" % Test
)
