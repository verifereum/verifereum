open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1524Theory;
val () = new_theory "vfmTest1524";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1524") $ get_result_defs "vfmTestDefs1524";
val () = export_theory_no_docs ();
