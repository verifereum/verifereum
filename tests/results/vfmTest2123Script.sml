Theory vfmTest2123[no_sig_docs]
Ancestors vfmTestDefs2123
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2123_0.nsv", "result2123_1.nsv", "result2123_2.nsv", "result2123_3.nsv", "result2123_4.nsv", "result2123_5.nsv", "result2123_6.nsv", "result2123_7.nsv", "result2123_8.nsv"];
val thyn = "vfmTestDefs2123";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
