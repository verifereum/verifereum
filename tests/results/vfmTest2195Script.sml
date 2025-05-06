open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2195Theory;
val () = new_theory "vfmTest2195";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2195") $ get_result_defs "vfmTestDefs2195";
val () = export_theory_no_docs ();
