open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1022Theory;
val () = new_theory "vfmTest1022";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1022") $ get_result_defs "vfmTestDefs1022";
val () = export_theory_no_docs ();
