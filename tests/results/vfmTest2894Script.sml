open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2894Theory;
val () = new_theory "vfmTest2894";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2894") $ get_result_defs "vfmTestDefs2894";
val () = export_theory_no_docs ();
