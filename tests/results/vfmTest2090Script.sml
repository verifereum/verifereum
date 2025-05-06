open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2090Theory;
val () = new_theory "vfmTest2090";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2090") $ get_result_defs "vfmTestDefs2090";
val () = export_theory_no_docs ();
