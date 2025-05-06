open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0669Theory;
val () = new_theory "vfmTest0669";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0669") $ get_result_defs "vfmTestDefs0669";
val () = export_theory_no_docs ();
