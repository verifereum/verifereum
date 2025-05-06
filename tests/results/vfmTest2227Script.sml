open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2227Theory;
val () = new_theory "vfmTest2227";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2227") $ get_result_defs "vfmTestDefs2227";
val () = export_theory_no_docs ();
