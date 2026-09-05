Theory vfmTest0123[no_sig_docs]
Ancestors vfmTestDefs0123
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0123_0.nsv", "result0123_1.nsv", "result0123_2.nsv", "result0123_3.nsv", "result0123_4.nsv", "result0123_5.nsv", "result0123_6.nsv", "result0123_7.nsv", "result0123_8.nsv", "result0123_9.nsv", "result0123_10.nsv", "result0123_11.nsv", "result0123_12.nsv", "result0123_13.nsv", "result0123_14.nsv", "result0123_15.nsv"];
val thyn = "vfmTestDefs0123";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
