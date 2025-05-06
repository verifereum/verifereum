open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2679Theory;
val () = new_theory "vfmTest2679";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2679") $ get_result_defs "vfmTestDefs2679";
val () = export_theory_no_docs ();
