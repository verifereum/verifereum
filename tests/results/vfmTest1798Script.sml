open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1798Theory;
val () = new_theory "vfmTest1798";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1798") $ get_result_defs "vfmTestDefs1798";
val () = export_theory_no_docs ();
