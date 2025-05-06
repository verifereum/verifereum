open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0357Theory;
val () = new_theory "vfmTest0357";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0357") $ get_result_defs "vfmTestDefs0357";
val () = export_theory_no_docs ();
