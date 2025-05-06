open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1695Theory;
val () = new_theory "vfmTest1695";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1695") $ get_result_defs "vfmTestDefs1695";
val () = export_theory_no_docs ();
