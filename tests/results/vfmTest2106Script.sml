open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2106Theory;
val () = new_theory "vfmTest2106";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2106") $ get_result_defs "vfmTestDefs2106";
val () = export_theory_no_docs ();
