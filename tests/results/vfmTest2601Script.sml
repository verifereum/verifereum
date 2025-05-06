open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2601Theory;
val () = new_theory "vfmTest2601";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2601") $ get_result_defs "vfmTestDefs2601";
val () = export_theory_no_docs ();
