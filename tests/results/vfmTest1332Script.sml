open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1332Theory;
val () = new_theory "vfmTest1332";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1332") $ get_result_defs "vfmTestDefs1332";
val () = export_theory_no_docs ();
