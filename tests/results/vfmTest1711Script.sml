open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1711Theory;
val () = new_theory "vfmTest1711";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1711") $ get_result_defs "vfmTestDefs1711";
val () = export_theory_no_docs ();
