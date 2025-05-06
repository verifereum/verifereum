open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2092Theory;
val () = new_theory "vfmTest2092";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2092") $ get_result_defs "vfmTestDefs2092";
val () = export_theory_no_docs ();
