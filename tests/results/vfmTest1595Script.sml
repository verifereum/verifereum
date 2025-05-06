open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1595Theory;
val () = new_theory "vfmTest1595";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1595") $ get_result_defs "vfmTestDefs1595";
val () = export_theory_no_docs ();
