open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2615Theory;
val () = new_theory "vfmTest2615";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2615") $ get_result_defs "vfmTestDefs2615";
val () = export_theory_no_docs ();
