open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1966Theory;
val () = new_theory "vfmTest1966";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1966") $ get_result_defs "vfmTestDefs1966";
val () = export_theory_no_docs ();
