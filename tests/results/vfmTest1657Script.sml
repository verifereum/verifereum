open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1657Theory;
val () = new_theory "vfmTest1657";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1657") $ get_result_defs "vfmTestDefs1657";
val () = export_theory_no_docs ();
