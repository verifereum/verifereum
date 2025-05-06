open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2684Theory;
val () = new_theory "vfmTest2684";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2684") $ get_result_defs "vfmTestDefs2684";
val () = export_theory_no_docs ();
