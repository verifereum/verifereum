open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2079Theory;
val () = new_theory "vfmTest2079";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2079") $ get_result_defs "vfmTestDefs2079";
val () = export_theory_no_docs ();
