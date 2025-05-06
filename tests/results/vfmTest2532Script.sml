open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2532Theory;
val () = new_theory "vfmTest2532";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2532") $ get_result_defs "vfmTestDefs2532";
val () = export_theory_no_docs ();
