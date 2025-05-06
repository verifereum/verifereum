open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2630Theory;
val () = new_theory "vfmTest2630";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2630") $ get_result_defs "vfmTestDefs2630";
val () = export_theory_no_docs ();
