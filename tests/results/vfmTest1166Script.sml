open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1166Theory;
val () = new_theory "vfmTest1166";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1166") $ get_result_defs "vfmTestDefs1166";
val () = export_theory_no_docs ();
