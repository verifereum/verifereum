open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1455Theory;
val () = new_theory "vfmTest1455";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1455") $ get_result_defs "vfmTestDefs1455";
val () = export_theory_no_docs ();
