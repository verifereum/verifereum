open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1573Theory;
val () = new_theory "vfmTest1573";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1573") $ get_result_defs "vfmTestDefs1573";
val () = export_theory_no_docs ();
