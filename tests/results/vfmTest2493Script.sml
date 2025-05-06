open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2493Theory;
val () = new_theory "vfmTest2493";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2493") $ get_result_defs "vfmTestDefs2493";
val () = export_theory_no_docs ();
