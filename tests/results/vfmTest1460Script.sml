open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1460Theory;
val () = new_theory "vfmTest1460";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1460") $ get_result_defs "vfmTestDefs1460";
val () = export_theory_no_docs ();
