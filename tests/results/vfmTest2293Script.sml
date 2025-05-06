open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2293Theory;
val () = new_theory "vfmTest2293";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2293") $ get_result_defs "vfmTestDefs2293";
val () = export_theory_no_docs ();
