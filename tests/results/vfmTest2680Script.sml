open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2680Theory;
val () = new_theory "vfmTest2680";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2680") $ get_result_defs "vfmTestDefs2680";
val () = export_theory_no_docs ();
