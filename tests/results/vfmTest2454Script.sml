open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2454Theory;
val () = new_theory "vfmTest2454";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2454") $ get_result_defs "vfmTestDefs2454";
val () = export_theory_no_docs ();
