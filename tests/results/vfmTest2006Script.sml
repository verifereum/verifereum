open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2006Theory;
val () = new_theory "vfmTest2006";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2006") $ get_result_defs "vfmTestDefs2006";
val () = export_theory_no_docs ();
