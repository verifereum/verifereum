open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2850Theory;
val () = new_theory "vfmTest2850";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2850") $ get_result_defs "vfmTestDefs2850";
val () = export_theory_no_docs ();
