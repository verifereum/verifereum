open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0888Theory;
val () = new_theory "vfmTest0888";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0888") $ get_result_defs "vfmTestDefs0888";
val () = export_theory_no_docs ();
