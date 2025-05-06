open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2536Theory;
val () = new_theory "vfmTest2536";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2536") $ get_result_defs "vfmTestDefs2536";
val () = export_theory_no_docs ();
