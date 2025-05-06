open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1405Theory;
val () = new_theory "vfmTest1405";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1405") $ get_result_defs "vfmTestDefs1405";
val () = export_theory_no_docs ();
