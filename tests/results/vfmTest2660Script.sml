open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2660Theory;
val () = new_theory "vfmTest2660";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2660") $ get_result_defs "vfmTestDefs2660";
val () = export_theory_no_docs ();
