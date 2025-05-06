open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2279Theory;
val () = new_theory "vfmTest2279";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2279") $ get_result_defs "vfmTestDefs2279";
val () = export_theory_no_docs ();
