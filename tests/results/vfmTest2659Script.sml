open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2659Theory;
val () = new_theory "vfmTest2659";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2659") $ get_result_defs "vfmTestDefs2659";
val () = export_theory_no_docs ();
