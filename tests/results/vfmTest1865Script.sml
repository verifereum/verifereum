open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1865Theory;
val () = new_theory "vfmTest1865";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1865") $ get_result_defs "vfmTestDefs1865";
val () = export_theory_no_docs ();
