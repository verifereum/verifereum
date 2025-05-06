open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2904Theory;
val () = new_theory "vfmTest2904";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2904") $ get_result_defs "vfmTestDefs2904";
val () = export_theory_no_docs ();
