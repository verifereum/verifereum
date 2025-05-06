open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1734Theory;
val () = new_theory "vfmTest1734";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1734") $ get_result_defs "vfmTestDefs1734";
val () = export_theory_no_docs ();
