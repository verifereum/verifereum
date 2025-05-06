open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2838Theory;
val () = new_theory "vfmTest2838";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2838") $ get_result_defs "vfmTestDefs2838";
val () = export_theory_no_docs ();
