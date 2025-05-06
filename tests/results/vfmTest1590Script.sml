open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1590Theory;
val () = new_theory "vfmTest1590";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1590") $ get_result_defs "vfmTestDefs1590";
val () = export_theory_no_docs ();
