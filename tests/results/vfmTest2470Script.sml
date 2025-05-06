open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2470Theory;
val () = new_theory "vfmTest2470";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2470") $ get_result_defs "vfmTestDefs2470";
val () = export_theory_no_docs ();
