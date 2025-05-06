open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1328Theory;
val () = new_theory "vfmTest1328";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1328") $ get_result_defs "vfmTestDefs1328";
val () = export_theory_no_docs ();
