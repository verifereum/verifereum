open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0472Theory;
val () = new_theory "vfmTest0472";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0472") $ get_result_defs "vfmTestDefs0472";
val () = export_theory_no_docs ();
