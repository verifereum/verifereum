open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2294Theory;
val () = new_theory "vfmTest2294";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2294") $ get_result_defs "vfmTestDefs2294";
val () = export_theory_no_docs ();
