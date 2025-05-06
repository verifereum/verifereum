open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0738Theory;
val () = new_theory "vfmTest0738";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0738") $ get_result_defs "vfmTestDefs0738";
val () = export_theory_no_docs ();
