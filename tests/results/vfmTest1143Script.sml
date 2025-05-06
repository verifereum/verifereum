open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1143Theory;
val () = new_theory "vfmTest1143";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1143") $ get_result_defs "vfmTestDefs1143";
val () = export_theory_no_docs ();
