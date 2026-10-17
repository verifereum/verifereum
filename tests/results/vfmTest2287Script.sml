Theory vfmTest2287[no_sig_docs]
Ancestors vfmTestDefs2287
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2287_0.nsv", "result2287_1.nsv", "result2287_2.nsv", "result2287_3.nsv", "result2287_4.nsv", "result2287_5.nsv", "result2287_6.nsv", "result2287_7.nsv", "result2287_8.nsv", "result2287_9.nsv", "result2287_10.nsv", "result2287_11.nsv", "result2287_12.nsv", "result2287_13.nsv"];
val thyn = "vfmTestDefs2287";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
