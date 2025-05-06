open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2246Theory;
val () = new_theory "vfmTest2246";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2246") $ get_result_defs "vfmTestDefs2246";
val () = export_theory_no_docs ();
