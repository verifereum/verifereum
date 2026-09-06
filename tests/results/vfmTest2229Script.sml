Theory vfmTest2229[no_sig_docs]
Ancestors vfmTestDefs2229
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2229_0.nsv", "result2229_1.nsv", "result2229_2.nsv", "result2229_3.nsv", "result2229_4.nsv", "result2229_5.nsv", "result2229_6.nsv", "result2229_7.nsv", "result2229_8.nsv", "result2229_9.nsv", "result2229_10.nsv", "result2229_11.nsv", "result2229_12.nsv", "result2229_13.nsv", "result2229_14.nsv", "result2229_15.nsv"];
val thyn = "vfmTestDefs2229";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
