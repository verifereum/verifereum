open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2292Theory;
val () = new_theory "vfmTest2292";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2292") $ get_result_defs "vfmTestDefs2292";
val () = export_theory_no_docs ();
