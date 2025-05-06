open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2698Theory;
val () = new_theory "vfmTest2698";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2698") $ get_result_defs "vfmTestDefs2698";
val () = export_theory_no_docs ();
