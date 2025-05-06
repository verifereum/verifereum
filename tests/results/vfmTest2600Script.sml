open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2600Theory;
val () = new_theory "vfmTest2600";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2600") $ get_result_defs "vfmTestDefs2600";
val () = export_theory_no_docs ();
