open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2085Theory;
val () = new_theory "vfmTest2085";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2085") $ get_result_defs "vfmTestDefs2085";
val () = export_theory_no_docs ();
