open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2032Theory;
val () = new_theory "vfmTest2032";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2032") $ get_result_defs "vfmTestDefs2032";
val () = export_theory_no_docs ();
