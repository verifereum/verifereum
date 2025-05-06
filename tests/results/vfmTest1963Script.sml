open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1963Theory;
val () = new_theory "vfmTest1963";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1963") $ get_result_defs "vfmTestDefs1963";
val () = export_theory_no_docs ();
