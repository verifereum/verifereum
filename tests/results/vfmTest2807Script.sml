open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2807Theory;
val () = new_theory "vfmTest2807";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2807") $ get_result_defs "vfmTestDefs2807";
val () = export_theory_no_docs ();
