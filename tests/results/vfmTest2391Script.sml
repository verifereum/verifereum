open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2391Theory;
val () = new_theory "vfmTest2391";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2391") $ get_result_defs "vfmTestDefs2391";
val () = export_theory_no_docs ();
