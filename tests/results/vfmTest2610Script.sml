open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2610Theory;
val () = new_theory "vfmTest2610";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2610") $ get_result_defs "vfmTestDefs2610";
val () = export_theory_no_docs ();
