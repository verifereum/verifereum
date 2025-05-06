open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2603Theory;
val () = new_theory "vfmTest2603";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2603") $ get_result_defs "vfmTestDefs2603";
val () = export_theory_no_docs ();
