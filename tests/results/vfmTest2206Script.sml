open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2206Theory;
val () = new_theory "vfmTest2206";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2206") $ get_result_defs "vfmTestDefs2206";
val () = export_theory_no_docs ();
