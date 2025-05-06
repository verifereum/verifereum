open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1600Theory;
val () = new_theory "vfmTest1600";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1600") $ get_result_defs "vfmTestDefs1600";
val () = export_theory_no_docs ();
