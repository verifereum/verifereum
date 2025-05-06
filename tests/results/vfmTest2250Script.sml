open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2250Theory;
val () = new_theory "vfmTest2250";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2250") $ get_result_defs "vfmTestDefs2250";
val () = export_theory_no_docs ();
