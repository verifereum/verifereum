open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1866Theory;
val () = new_theory "vfmTest1866";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1866") $ get_result_defs "vfmTestDefs1866";
val () = export_theory_no_docs ();
