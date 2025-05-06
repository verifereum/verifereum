open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1042Theory;
val () = new_theory "vfmTest1042";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1042") $ get_result_defs "vfmTestDefs1042";
val () = export_theory_no_docs ();
