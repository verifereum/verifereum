open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1342Theory;
val () = new_theory "vfmTest1342";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1342") $ get_result_defs "vfmTestDefs1342";
val () = export_theory_no_docs ();
