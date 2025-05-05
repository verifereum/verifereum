open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs124Theory;
val () = new_theory "vfmStateTest124";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs124") $ get_result_defs "vfmStateTestDefs124";
val () = export_theory_no_docs ();
