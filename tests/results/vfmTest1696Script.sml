open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1696Theory;
val () = new_theory "vfmTest1696";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1696") $ get_result_defs "vfmTestDefs1696";
val () = export_theory_no_docs ();
