open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1888Theory;
val () = new_theory "vfmTest1888";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1888") $ get_result_defs "vfmTestDefs1888";
val () = export_theory_no_docs ();
