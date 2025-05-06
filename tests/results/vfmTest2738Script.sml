open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2738Theory;
val () = new_theory "vfmTest2738";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2738") $ get_result_defs "vfmTestDefs2738";
val () = export_theory_no_docs ();
