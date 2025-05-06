open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2620Theory;
val () = new_theory "vfmTest2620";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2620") $ get_result_defs "vfmTestDefs2620";
val () = export_theory_no_docs ();
