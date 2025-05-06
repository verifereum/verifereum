open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0518Theory;
val () = new_theory "vfmTest0518";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0518") $ get_result_defs "vfmTestDefs0518";
val () = export_theory_no_docs ();
