open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1194Theory;
val () = new_theory "vfmTest1194";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1194") $ get_result_defs "vfmTestDefs1194";
val () = export_theory_no_docs ();
