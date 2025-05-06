open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2717Theory;
val () = new_theory "vfmTest2717";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2717") $ get_result_defs "vfmTestDefs2717";
val () = export_theory_no_docs ();
