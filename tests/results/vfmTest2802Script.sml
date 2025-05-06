open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2802Theory;
val () = new_theory "vfmTest2802";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2802") $ get_result_defs "vfmTestDefs2802";
val () = export_theory_no_docs ();
