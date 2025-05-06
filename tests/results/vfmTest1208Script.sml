open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1208Theory;
val () = new_theory "vfmTest1208";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1208") $ get_result_defs "vfmTestDefs1208";
val () = export_theory_no_docs ();
