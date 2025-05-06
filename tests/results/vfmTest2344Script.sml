open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2344Theory;
val () = new_theory "vfmTest2344";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2344") $ get_result_defs "vfmTestDefs2344";
val () = export_theory_no_docs ();
