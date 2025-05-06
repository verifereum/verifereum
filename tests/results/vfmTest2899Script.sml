open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2899Theory;
val () = new_theory "vfmTest2899";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2899") $ get_result_defs "vfmTestDefs2899";
val () = export_theory_no_docs ();
