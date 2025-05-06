open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2269Theory;
val () = new_theory "vfmTest2269";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2269") $ get_result_defs "vfmTestDefs2269";
val () = export_theory_no_docs ();
