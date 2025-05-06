open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1357Theory;
val () = new_theory "vfmTest1357";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1357") $ get_result_defs "vfmTestDefs1357";
val () = export_theory_no_docs ();
