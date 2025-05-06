open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1904Theory;
val () = new_theory "vfmTest1904";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1904") $ get_result_defs "vfmTestDefs1904";
val () = export_theory_no_docs ();
