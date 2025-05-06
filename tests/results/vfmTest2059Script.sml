open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2059Theory;
val () = new_theory "vfmTest2059";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2059") $ get_result_defs "vfmTestDefs2059";
val () = export_theory_no_docs ();
