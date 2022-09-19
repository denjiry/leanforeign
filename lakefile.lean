import Lake
open Lake DSL

package LeanForeign {
  -- add package configuration options here
}

lean_lib LeanForeign {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe leanforeign {
  root := `Main
}
