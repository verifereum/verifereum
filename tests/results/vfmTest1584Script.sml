open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1584Theory;
val () = new_theory "vfmTest1584";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1584") $ get_result_defs "vfmTestDefs1584";
val () = export_theory_no_docs ();
