open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2545Theory;
val () = new_theory "vfmTest2545";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2545") $ get_result_defs "vfmTestDefs2545";
val () = export_theory_no_docs ();
