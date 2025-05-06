open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1743Theory;
val () = new_theory "vfmTest1743";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1743") $ get_result_defs "vfmTestDefs1743";
val () = export_theory_no_docs ();
