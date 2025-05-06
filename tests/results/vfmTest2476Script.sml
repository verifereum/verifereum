open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2476Theory;
val () = new_theory "vfmTest2476";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2476") $ get_result_defs "vfmTestDefs2476";
val () = export_theory_no_docs ();
