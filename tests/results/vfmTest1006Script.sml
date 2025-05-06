open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1006Theory;
val () = new_theory "vfmTest1006";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1006") $ get_result_defs "vfmTestDefs1006";
val () = export_theory_no_docs ();
