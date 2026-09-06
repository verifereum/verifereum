Theory vfmTest2465[no_sig_docs]
Ancestors vfmTestDefs2465
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2465_0.nsv", "result2465_1.nsv", "result2465_2.nsv", "result2465_3.nsv", "result2465_4.nsv", "result2465_5.nsv", "result2465_6.nsv", "result2465_7.nsv"];
val thyn = "vfmTestDefs2465";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
