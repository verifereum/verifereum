open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs148Theory;
val () = new_theory "vfmStateTest148";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs148") $ get_result_defs "vfmStateTestDefs148";
val () = export_theory_no_docs ();
