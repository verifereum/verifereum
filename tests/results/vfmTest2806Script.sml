open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2806Theory;
val () = new_theory "vfmTest2806";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2806") $ get_result_defs "vfmTestDefs2806";
val () = export_theory_no_docs ();
