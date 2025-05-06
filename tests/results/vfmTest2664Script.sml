open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2664Theory;
val () = new_theory "vfmTest2664";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2664") $ get_result_defs "vfmTestDefs2664";
val () = export_theory_no_docs ();
