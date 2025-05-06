open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1061Theory;
val () = new_theory "vfmTest1061";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1061") $ get_result_defs "vfmTestDefs1061";
val () = export_theory_no_docs ();
