open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2460Theory;
val () = new_theory "vfmTest2460";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2460") $ get_result_defs "vfmTestDefs2460";
val () = export_theory_no_docs ();
