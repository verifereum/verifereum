open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2843Theory;
val () = new_theory "vfmTest2843";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2843") $ get_result_defs "vfmTestDefs2843";
val () = export_theory_no_docs ();
