open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1815Theory;
val () = new_theory "vfmTest1815";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1815") $ get_result_defs "vfmTestDefs1815";
val () = export_theory_no_docs ();
