open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1724Theory;
val () = new_theory "vfmTest1724";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1724") $ get_result_defs "vfmTestDefs1724";
val () = export_theory_no_docs ();
