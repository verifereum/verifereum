open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2611Theory;
val () = new_theory "vfmTest2611";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2611") $ get_result_defs "vfmTestDefs2611";
val () = export_theory_no_docs ();
