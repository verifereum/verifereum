open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2110Theory;
val () = new_theory "vfmTest2110";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2110") $ get_result_defs "vfmTestDefs2110";
val () = export_theory_no_docs ();
