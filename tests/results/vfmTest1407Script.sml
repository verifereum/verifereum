open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1407Theory;
val () = new_theory "vfmTest1407";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1407") $ get_result_defs "vfmTestDefs1407";
val () = export_theory_no_docs ();
