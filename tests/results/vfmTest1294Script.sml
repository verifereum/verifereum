open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1294Theory;
val () = new_theory "vfmTest1294";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1294") $ get_result_defs "vfmTestDefs1294";
val () = export_theory_no_docs ();
