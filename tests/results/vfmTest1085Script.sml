open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1085Theory;
val () = new_theory "vfmTest1085";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1085") $ get_result_defs "vfmTestDefs1085";
val () = export_theory_no_docs ();
