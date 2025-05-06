open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2569Theory;
val () = new_theory "vfmTest2569";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2569") $ get_result_defs "vfmTestDefs2569";
val () = export_theory_no_docs ();
