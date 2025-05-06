open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1099Theory;
val () = new_theory "vfmTest1099";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1099") $ get_result_defs "vfmTestDefs1099";
val () = export_theory_no_docs ();
