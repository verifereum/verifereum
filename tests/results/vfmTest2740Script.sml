open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2740Theory;
val () = new_theory "vfmTest2740";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2740") $ get_result_defs "vfmTestDefs2740";
val () = export_theory_no_docs ();
