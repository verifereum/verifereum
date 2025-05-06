open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1720Theory;
val () = new_theory "vfmTest1720";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1720") $ get_result_defs "vfmTestDefs1720";
val () = export_theory_no_docs ();
