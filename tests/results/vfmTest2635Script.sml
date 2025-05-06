open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2635Theory;
val () = new_theory "vfmTest2635";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2635") $ get_result_defs "vfmTestDefs2635";
val () = export_theory_no_docs ();
