open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2029Theory;
val () = new_theory "vfmTest2029";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2029") $ get_result_defs "vfmTestDefs2029";
val () = export_theory_no_docs ();
