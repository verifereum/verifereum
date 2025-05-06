open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2520Theory;
val () = new_theory "vfmTest2520";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2520") $ get_result_defs "vfmTestDefs2520";
val () = export_theory_no_docs ();
