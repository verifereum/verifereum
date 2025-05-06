open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1018Theory;
val () = new_theory "vfmTest1018";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1018") $ get_result_defs "vfmTestDefs1018";
val () = export_theory_no_docs ();
