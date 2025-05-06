open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1101Theory;
val () = new_theory "vfmTest1101";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1101") $ get_result_defs "vfmTestDefs1101";
val () = export_theory_no_docs ();
