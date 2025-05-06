open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1814Theory;
val () = new_theory "vfmTest1814";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1814") $ get_result_defs "vfmTestDefs1814";
val () = export_theory_no_docs ();
