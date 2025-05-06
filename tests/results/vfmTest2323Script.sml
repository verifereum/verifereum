open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2323Theory;
val () = new_theory "vfmTest2323";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2323") $ get_result_defs "vfmTestDefs2323";
val () = export_theory_no_docs ();
