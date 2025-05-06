open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2190Theory;
val () = new_theory "vfmTest2190";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2190") $ get_result_defs "vfmTestDefs2190";
val () = export_theory_no_docs ();
