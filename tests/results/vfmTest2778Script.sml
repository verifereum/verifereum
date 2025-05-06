open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2778Theory;
val () = new_theory "vfmTest2778";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2778") $ get_result_defs "vfmTestDefs2778";
val () = export_theory_no_docs ();
