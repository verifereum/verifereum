open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2708Theory;
val () = new_theory "vfmTest2708";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2708") $ get_result_defs "vfmTestDefs2708";
val () = export_theory_no_docs ();
