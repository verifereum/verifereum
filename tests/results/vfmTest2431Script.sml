open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2431Theory;
val () = new_theory "vfmTest2431";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2431") $ get_result_defs "vfmTestDefs2431";
val () = export_theory_no_docs ();
