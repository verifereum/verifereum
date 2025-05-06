open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2898Theory;
val () = new_theory "vfmTest2898";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2898") $ get_result_defs "vfmTestDefs2898";
val () = export_theory_no_docs ();
