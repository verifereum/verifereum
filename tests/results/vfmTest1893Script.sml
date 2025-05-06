open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1893Theory;
val () = new_theory "vfmTest1893";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1893") $ get_result_defs "vfmTestDefs1893";
val () = export_theory_no_docs ();
