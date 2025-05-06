open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1074Theory;
val () = new_theory "vfmTest1074";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1074") $ get_result_defs "vfmTestDefs1074";
val () = export_theory_no_docs ();
