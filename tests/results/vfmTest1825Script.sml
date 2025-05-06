open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1825Theory;
val () = new_theory "vfmTest1825";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1825") $ get_result_defs "vfmTestDefs1825";
val () = export_theory_no_docs ();
