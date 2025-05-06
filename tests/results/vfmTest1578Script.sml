open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1578Theory;
val () = new_theory "vfmTest1578";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1578") $ get_result_defs "vfmTestDefs1578";
val () = export_theory_no_docs ();
