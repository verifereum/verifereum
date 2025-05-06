open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1409Theory;
val () = new_theory "vfmTest1409";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1409") $ get_result_defs "vfmTestDefs1409";
val () = export_theory_no_docs ();
