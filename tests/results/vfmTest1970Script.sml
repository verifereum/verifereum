open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1970Theory;
val () = new_theory "vfmTest1970";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1970") $ get_result_defs "vfmTestDefs1970";
val () = export_theory_no_docs ();
