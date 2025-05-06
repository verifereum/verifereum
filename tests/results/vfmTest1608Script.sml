open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1608Theory;
val () = new_theory "vfmTest1608";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1608") $ get_result_defs "vfmTestDefs1608";
val () = export_theory_no_docs ();
