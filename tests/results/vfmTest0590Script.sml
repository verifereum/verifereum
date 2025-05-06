open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0590Theory;
val () = new_theory "vfmTest0590";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0590") $ get_result_defs "vfmTestDefs0590";
val () = export_theory_no_docs ();
