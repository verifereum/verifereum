open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2221Theory;
val () = new_theory "vfmTest2221";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2221") $ get_result_defs "vfmTestDefs2221";
val () = export_theory_no_docs ();
