# Package

version       = "0.1.0"
author        = "Double-oxygeN"
description   = "Z3 binding for Nim"
license       = "MIT"
srcDir        = "src"



# Dependencies

requires "nim >= 0.20.2"


# Tasks

task docgen, "Generate documentation":
  exec "nim doc --outDir:docs --git.url:https://github.com/Double-oxygeN/z3nim --git.commit:master src/z3nim"
  exec "find docs -name '*.html' -exec sed \"s/-webkit-filter: \\([^;][^;]*\\)/-webkit-filter: \\1;\\n  filter: \\1/\" -i '{}' \\;"
