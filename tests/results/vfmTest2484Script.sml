Theory vfmTest2484[no_sig_docs]
Ancestors vfmTestDefs2484
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2484_0.nsv", "result2484_1.nsv", "result2484_2.nsv", "result2484_3.nsv", "result2484_4.nsv", "result2484_5.nsv", "result2484_6.nsv", "result2484_7.nsv", "result2484_8.nsv", "result2484_9.nsv", "result2484_10.nsv", "result2484_11.nsv", "result2484_12.nsv", "result2484_13.nsv", "result2484_14.nsv", "result2484_15.nsv"];
val thyn = "vfmTestDefs2484";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
