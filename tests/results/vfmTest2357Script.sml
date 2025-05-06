open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2357Theory;
val () = new_theory "vfmTest2357";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2357") $ get_result_defs "vfmTestDefs2357";
val () = export_theory_no_docs ();
