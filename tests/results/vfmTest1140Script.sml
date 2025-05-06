open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1140Theory;
val () = new_theory "vfmTest1140";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1140") $ get_result_defs "vfmTestDefs1140";
val () = export_theory_no_docs ();
