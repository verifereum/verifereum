open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1838Theory;
val () = new_theory "vfmTest1838";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1838") $ get_result_defs "vfmTestDefs1838";
val () = export_theory_no_docs ();
