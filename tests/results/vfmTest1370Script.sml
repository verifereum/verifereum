open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1370Theory;
val () = new_theory "vfmTest1370";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1370") $ get_result_defs "vfmTestDefs1370";
val () = export_theory_no_docs ();
