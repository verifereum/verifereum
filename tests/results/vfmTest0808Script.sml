open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0808Theory;
val () = new_theory "vfmTest0808";
val thyn = "vfmTestDefs0808";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
