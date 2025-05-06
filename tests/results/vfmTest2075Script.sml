open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2075Theory;
val () = new_theory "vfmTest2075";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2075") $ get_result_defs "vfmTestDefs2075";
val () = export_theory_no_docs ();
