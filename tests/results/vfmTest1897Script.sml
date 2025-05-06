open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1897Theory;
val () = new_theory "vfmTest1897";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1897") $ get_result_defs "vfmTestDefs1897";
val () = export_theory_no_docs ();
