open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0830Theory;
val () = new_theory "vfmTest0830";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0830") $ get_result_defs "vfmTestDefs0830";
val () = export_theory_no_docs ();
