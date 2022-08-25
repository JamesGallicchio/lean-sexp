import Lake
open Lake DSL

package «lean-sexp»

lean_lib Sexp

@[defaultTarget]
lean_exe «lean-sexp-test» {
  root := `Main
}