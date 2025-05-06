open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0248Theory;
val () = new_theory "vfmTest0248";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0248") $ get_result_defs "vfmTestDefs0248";
val () = export_theory_no_docs ();
