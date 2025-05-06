open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1472Theory;
val () = new_theory "vfmTest1472";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1472") $ get_result_defs "vfmTestDefs1472";
val () = export_theory_no_docs ();
