open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1767Theory;
val () = new_theory "vfmTest1767";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1767") $ get_result_defs "vfmTestDefs1767";
val () = export_theory_no_docs ();
