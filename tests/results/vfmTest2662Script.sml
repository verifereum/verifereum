open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2662Theory;
val () = new_theory "vfmTest2662";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2662") $ get_result_defs "vfmTestDefs2662";
val () = export_theory_no_docs ();
