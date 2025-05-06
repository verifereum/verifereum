open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2745Theory;
val () = new_theory "vfmTest2745";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2745") $ get_result_defs "vfmTestDefs2745";
val () = export_theory_no_docs ();
