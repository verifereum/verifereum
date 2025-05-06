open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2498Theory;
val () = new_theory "vfmTest2498";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2498") $ get_result_defs "vfmTestDefs2498";
val () = export_theory_no_docs ();
