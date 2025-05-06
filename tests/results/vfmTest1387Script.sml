open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1387Theory;
val () = new_theory "vfmTest1387";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1387") $ get_result_defs "vfmTestDefs1387";
val () = export_theory_no_docs ();
