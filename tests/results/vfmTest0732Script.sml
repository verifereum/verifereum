open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0732Theory;
val () = new_theory "vfmTest0732";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0732") $ get_result_defs "vfmTestDefs0732";
val () = export_theory_no_docs ();
