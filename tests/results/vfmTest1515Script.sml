open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1515Theory;
val () = new_theory "vfmTest1515";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1515") $ get_result_defs "vfmTestDefs1515";
val () = export_theory_no_docs ();
