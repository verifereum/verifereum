open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0808Theory;
val () = new_theory "vfmTest0808";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0808") $ get_result_defs "vfmTestDefs0808";
val () = export_theory_no_docs ();
