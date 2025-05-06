open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2730Theory;
val () = new_theory "vfmTest2730";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2730") $ get_result_defs "vfmTestDefs2730";
val () = export_theory_no_docs ();
