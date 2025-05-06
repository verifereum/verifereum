open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1879Theory;
val () = new_theory "vfmTest1879";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1879") $ get_result_defs "vfmTestDefs1879";
val () = export_theory_no_docs ();
