open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1348Theory;
val () = new_theory "vfmTest1348";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1348") $ get_result_defs "vfmTestDefs1348";
val () = export_theory_no_docs ();
