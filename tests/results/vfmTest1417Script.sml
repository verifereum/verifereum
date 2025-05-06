open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1417Theory;
val () = new_theory "vfmTest1417";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1417") $ get_result_defs "vfmTestDefs1417";
val () = export_theory_no_docs ();
