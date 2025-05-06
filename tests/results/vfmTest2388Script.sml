open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2388Theory;
val () = new_theory "vfmTest2388";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2388") $ get_result_defs "vfmTestDefs2388";
val () = export_theory_no_docs ();
