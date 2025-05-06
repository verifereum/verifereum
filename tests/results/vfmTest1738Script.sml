open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1738Theory;
val () = new_theory "vfmTest1738";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1738") $ get_result_defs "vfmTestDefs1738";
val () = export_theory_no_docs ();
