open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1715Theory;
val () = new_theory "vfmTest1715";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1715") $ get_result_defs "vfmTestDefs1715";
val () = export_theory_no_docs ();
