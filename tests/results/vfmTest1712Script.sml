open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1712Theory;
val () = new_theory "vfmTest1712";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1712") $ get_result_defs "vfmTestDefs1712";
val () = export_theory_no_docs ();
