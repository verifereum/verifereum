open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2786Theory;
val () = new_theory "vfmTest2786";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2786") $ get_result_defs "vfmTestDefs2786";
val () = export_theory_no_docs ();
