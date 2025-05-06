open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2771Theory;
val () = new_theory "vfmTest2771";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2771") $ get_result_defs "vfmTestDefs2771";
val () = export_theory_no_docs ();
