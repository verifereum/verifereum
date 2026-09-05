Theory vfmTest0808[no_sig_docs]
Ancestors vfmTestDefs0808
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0808_0.nsv"];
val thyn = "vfmTestDefs0808";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
