open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1203Theory;
val () = new_theory "vfmTest1203";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1203") $ get_result_defs "vfmTestDefs1203";
val () = export_theory_no_docs ();
