open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2897Theory;
val () = new_theory "vfmTest2897";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2897") $ get_result_defs "vfmTestDefs2897";
val () = export_theory_no_docs ();
