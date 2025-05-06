open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2575Theory;
val () = new_theory "vfmTest2575";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2575") $ get_result_defs "vfmTestDefs2575";
val () = export_theory_no_docs ();
