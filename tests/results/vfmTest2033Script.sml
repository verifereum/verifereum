open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2033Theory;
val () = new_theory "vfmTest2033";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2033") $ get_result_defs "vfmTestDefs2033";
val () = export_theory_no_docs ();
