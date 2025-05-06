open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2590Theory;
val () = new_theory "vfmTest2590";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2590") $ get_result_defs "vfmTestDefs2590";
val () = export_theory_no_docs ();
