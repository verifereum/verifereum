open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2261Theory;
val () = new_theory "vfmTest2261";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2261") $ get_result_defs "vfmTestDefs2261";
val () = export_theory_no_docs ();
