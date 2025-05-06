open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0378Theory;
val () = new_theory "vfmTest0378";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0378") $ get_result_defs "vfmTestDefs0378";
val () = export_theory_no_docs ();
