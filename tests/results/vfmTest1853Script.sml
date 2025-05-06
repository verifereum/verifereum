open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1853Theory;
val () = new_theory "vfmTest1853";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1853") $ get_result_defs "vfmTestDefs1853";
val () = export_theory_no_docs ();
