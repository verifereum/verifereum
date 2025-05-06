open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1416Theory;
val () = new_theory "vfmTest1416";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1416") $ get_result_defs "vfmTestDefs1416";
val () = export_theory_no_docs ();
