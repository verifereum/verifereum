open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2851Theory;
val () = new_theory "vfmTest2851";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2851") $ get_result_defs "vfmTestDefs2851";
val () = export_theory_no_docs ();
