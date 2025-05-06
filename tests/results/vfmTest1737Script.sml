open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1737Theory;
val () = new_theory "vfmTest1737";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1737") $ get_result_defs "vfmTestDefs1737";
val () = export_theory_no_docs ();
