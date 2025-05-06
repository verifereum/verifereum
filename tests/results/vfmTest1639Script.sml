open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1639Theory;
val () = new_theory "vfmTest1639";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1639") $ get_result_defs "vfmTestDefs1639";
val () = export_theory_no_docs ();
