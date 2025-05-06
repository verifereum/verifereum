open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2054Theory;
val () = new_theory "vfmTest2054";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2054") $ get_result_defs "vfmTestDefs2054";
val () = export_theory_no_docs ();
