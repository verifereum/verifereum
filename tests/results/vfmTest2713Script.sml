open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2713Theory;
val () = new_theory "vfmTest2713";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2713") $ get_result_defs "vfmTestDefs2713";
val () = export_theory_no_docs ();
