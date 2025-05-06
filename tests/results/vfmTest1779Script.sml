open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1779Theory;
val () = new_theory "vfmTest1779";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1779") $ get_result_defs "vfmTestDefs1779";
val () = export_theory_no_docs ();
