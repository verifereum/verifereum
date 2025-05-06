open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1980Theory;
val () = new_theory "vfmTest1980";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1980") $ get_result_defs "vfmTestDefs1980";
val () = export_theory_no_docs ();
