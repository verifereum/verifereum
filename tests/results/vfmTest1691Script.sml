open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1691Theory;
val () = new_theory "vfmTest1691";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1691") $ get_result_defs "vfmTestDefs1691";
val () = export_theory_no_docs ();
