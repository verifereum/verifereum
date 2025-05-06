open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2655Theory;
val () = new_theory "vfmTest2655";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2655") $ get_result_defs "vfmTestDefs2655";
val () = export_theory_no_docs ();
