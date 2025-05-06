open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2903Theory;
val () = new_theory "vfmTest2903";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2903") $ get_result_defs "vfmTestDefs2903";
val () = export_theory_no_docs ();
