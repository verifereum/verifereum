open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1990Theory;
val () = new_theory "vfmTest1990";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1990") $ get_result_defs "vfmTestDefs1990";
val () = export_theory_no_docs ();
