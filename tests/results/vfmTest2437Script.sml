open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2437Theory;
val () = new_theory "vfmTest2437";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2437") $ get_result_defs "vfmTestDefs2437";
val () = export_theory_no_docs ();
