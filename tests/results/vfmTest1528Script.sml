open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1528Theory;
val () = new_theory "vfmTest1528";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1528") $ get_result_defs "vfmTestDefs1528";
val () = export_theory_no_docs ();
