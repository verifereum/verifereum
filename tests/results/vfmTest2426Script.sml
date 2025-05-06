open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2426Theory;
val () = new_theory "vfmTest2426";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2426") $ get_result_defs "vfmTestDefs2426";
val () = export_theory_no_docs ();
