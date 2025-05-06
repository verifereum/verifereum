open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1244Theory;
val () = new_theory "vfmTest1244";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1244") $ get_result_defs "vfmTestDefs1244";
val () = export_theory_no_docs ();
