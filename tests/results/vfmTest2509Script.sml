open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2509Theory;
val () = new_theory "vfmTest2509";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2509") $ get_result_defs "vfmTestDefs2509";
val () = export_theory_no_docs ();
