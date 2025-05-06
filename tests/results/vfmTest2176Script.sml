open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2176Theory;
val () = new_theory "vfmTest2176";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2176") $ get_result_defs "vfmTestDefs2176";
val () = export_theory_no_docs ();
