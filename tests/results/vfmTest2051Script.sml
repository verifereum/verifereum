open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2051Theory;
val () = new_theory "vfmTest2051";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2051") $ get_result_defs "vfmTestDefs2051";
val () = export_theory_no_docs ();
