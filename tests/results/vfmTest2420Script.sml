open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2420Theory;
val () = new_theory "vfmTest2420";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2420") $ get_result_defs "vfmTestDefs2420";
val () = export_theory_no_docs ();
