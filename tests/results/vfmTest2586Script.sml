open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2586Theory;
val () = new_theory "vfmTest2586";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2586") $ get_result_defs "vfmTestDefs2586";
val () = export_theory_no_docs ();
