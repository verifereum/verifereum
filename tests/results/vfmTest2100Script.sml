open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2100Theory;
val () = new_theory "vfmTest2100";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2100") $ get_result_defs "vfmTestDefs2100";
val () = export_theory_no_docs ();
