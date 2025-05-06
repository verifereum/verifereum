open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0299Theory;
val () = new_theory "vfmTest0299";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0299") $ get_result_defs "vfmTestDefs0299";
val () = export_theory_no_docs ();
