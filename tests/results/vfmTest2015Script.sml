open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2015Theory;
val () = new_theory "vfmTest2015";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2015") $ get_result_defs "vfmTestDefs2015";
val () = export_theory_no_docs ();
