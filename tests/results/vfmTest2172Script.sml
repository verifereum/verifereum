open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2172Theory;
val () = new_theory "vfmTest2172";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2172") $ get_result_defs "vfmTestDefs2172";
val () = export_theory_no_docs ();
