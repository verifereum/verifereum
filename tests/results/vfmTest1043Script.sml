open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1043Theory;
val () = new_theory "vfmTest1043";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1043") $ get_result_defs "vfmTestDefs1043";
val () = export_theory_no_docs ();
