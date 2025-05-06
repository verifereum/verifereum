open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1263Theory;
val () = new_theory "vfmTest1263";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1263") $ get_result_defs "vfmTestDefs1263";
val () = export_theory_no_docs ();
