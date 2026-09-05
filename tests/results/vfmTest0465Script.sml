Theory vfmTest0465[no_sig_docs]
Ancestors vfmTestDefs0465
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0465_0.nsv", "result0465_1.nsv"];
val thyn = "vfmTestDefs0465";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
