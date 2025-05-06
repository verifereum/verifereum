open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2114Theory;
val () = new_theory "vfmTest2114";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2114") $ get_result_defs "vfmTestDefs2114";
val () = export_theory_no_docs ();
