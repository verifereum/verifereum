Theory vfmTest2218[no_sig_docs]
Ancestors vfmTestDefs2218
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2218_0.nsv", "result2218_1.nsv", "result2218_2.nsv", "result2218_3.nsv", "result2218_4.nsv", "result2218_5.nsv", "result2218_6.nsv", "result2218_7.nsv", "result2218_8.nsv", "result2218_9.nsv", "result2218_10.nsv", "result2218_11.nsv", "result2218_12.nsv", "result2218_13.nsv", "result2218_14.nsv", "result2218_15.nsv"];
val thyn = "vfmTestDefs2218";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
