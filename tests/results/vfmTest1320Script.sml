open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1320Theory;
val () = new_theory "vfmTest1320";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1320") $ get_result_defs "vfmTestDefs1320";
val () = export_theory_no_docs ();
