open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1787Theory;
val () = new_theory "vfmTest1787";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1787") $ get_result_defs "vfmTestDefs1787";
val () = export_theory_no_docs ();
