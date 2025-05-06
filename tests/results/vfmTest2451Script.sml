open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2451Theory;
val () = new_theory "vfmTest2451";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2451") $ get_result_defs "vfmTestDefs2451";
val () = export_theory_no_docs ();
