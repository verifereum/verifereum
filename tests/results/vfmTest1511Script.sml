open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1511Theory;
val () = new_theory "vfmTest1511";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1511") $ get_result_defs "vfmTestDefs1511";
val () = export_theory_no_docs ();
