import Lake
open Lake DSL

package leanMeetup {
  -- add package configuration options here
}

lean_lib LeanMeetup {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe leanMeetup {
  root := `Main
}
