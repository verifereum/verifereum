open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1225Theory;
val () = new_theory "vfmTest1225";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1225") $ get_result_defs "vfmTestDefs1225";
val () = export_theory_no_docs ();
