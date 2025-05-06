open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2155Theory;
val () = new_theory "vfmTest2155";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2155") $ get_result_defs "vfmTestDefs2155";
val () = export_theory_no_docs ();
