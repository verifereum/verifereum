open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1960Theory;
val () = new_theory "vfmTest1960";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1960") $ get_result_defs "vfmTestDefs1960";
val () = export_theory_no_docs ();
