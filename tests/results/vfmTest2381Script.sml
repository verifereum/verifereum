open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2381Theory;
val () = new_theory "vfmTest2381";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2381") $ get_result_defs "vfmTestDefs2381";
val () = export_theory_no_docs ();
