open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1193Theory;
val () = new_theory "vfmTest1193";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1193") $ get_result_defs "vfmTestDefs1193";
val () = export_theory_no_docs ();
