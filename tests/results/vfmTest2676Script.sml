open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2676Theory;
val () = new_theory "vfmTest2676";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2676") $ get_result_defs "vfmTestDefs2676";
val () = export_theory_no_docs ();
