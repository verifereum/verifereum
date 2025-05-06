open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2914Theory;
val () = new_theory "vfmTest2914";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2914") $ get_result_defs "vfmTestDefs2914";
val () = export_theory_no_docs ();
