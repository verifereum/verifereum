open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2235Theory;
val () = new_theory "vfmTest2235";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2235") $ get_result_defs "vfmTestDefs2235";
val () = export_theory_no_docs ();
