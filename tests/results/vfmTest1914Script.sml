open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1914Theory;
val () = new_theory "vfmTest1914";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1914") $ get_result_defs "vfmTestDefs1914";
val () = export_theory_no_docs ();
