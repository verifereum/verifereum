open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2379Theory;
val () = new_theory "vfmTest2379";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2379") $ get_result_defs "vfmTestDefs2379";
val () = export_theory_no_docs ();
