open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2168Theory;
val () = new_theory "vfmTest2168";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2168") $ get_result_defs "vfmTestDefs2168";
val () = export_theory_no_docs ();
